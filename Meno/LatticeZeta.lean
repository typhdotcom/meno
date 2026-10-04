import Meno.BasisIndependence
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Algebra.Module.ZLattice.Summable

/-! # The lattice zeta function

Every bundled lattice action carries a zeta function: the Mellin
transform of its excess partition function `Z(β) − 1`. The single
Siegel–Poisson engine, in its scaled form (`scaled_duality`), is
exactly the inversion law `Z_Q(1/x) = √(π^rank/disc)·x^{rank/2}·Z_{Q∨}(x)`
that Mathlib's abstract functional-equation machinery consumes
(`WeakFEPair`). The pair `(Z_Q, Z_{Q∨})` therefore produces, with no
further analysis:

* **the completed zeta** `Q.completedZeta`, analytic away from `0` and
  `rank/2`;
* **the functional equation** `Λ_Q(rank/2 − s) = ε·Λ_{Q∨}(s)` with root
  number `ε = √(π^rank/disc)` (`completedZeta_functional_equation`):
  the zeta of a lattice at `rank/2 − s` is the zeta of its dual at `s`;
* **the Dirichlet expansion** `Λ_Q(s) = Γ(s)·∑_{a≠0} E(a)^{−s}` for
  `Re s > rank/2` (`hasSum_completedZeta`), the series converging by
  coercivity against Mathlib's lattice p-series (`summable_energy_rpow`).

For a graph the dual of the harmonic carrier is the priced cycle
lattice (`cycleActionEquivDual`), so the reflection exchanges
cohomology and homology (`IncidenceGraph.completedZeta_functional_equation`).

The decay hypothesis is the energy gap (`exists_energy_gap`): a
positive-definite form keeps every nonzero lattice point at energy
at least `c > 0`, so `Z(β) − 1` decays exponentially. -/

namespace Meno

open Filter Asymptotics Set
open scoped Classical

namespace QuadLatticeAction

universe u

variable (Q : QuadLatticeAction.{u})

/-! ## The energy gap and the decay of `Z − 1` -/

/-- **The energy gap**: every nonzero lattice point has energy at least
some `c > 0` — coercivity of the Gram chart, read at integer
coordinates, which square-sum to at least one. -/
theorem exists_energy_gap : ∃ c : ℝ, 0 < c ∧ ∀ a : Q.Λ, a ≠ 0 → c ≤ Q.form a a := by
  set b := Module.finBasis ℤ Q.Λ
  obtain ⟨c, hc, hcoer⟩ := (Q.gram_posDef b).exists_coercivity
  refine ⟨c, hc, fun a ha => ?_⟩
  set k : Fin (Module.finrank ℤ Q.Λ) → ℝ := fun i => ((b.repr a i : ℤ) : ℝ) with hk
  have hform : Q.form a a = k ⬝ᵥ (Q.gram b).mulVec k := by
    rw [Q.form_repr b a a]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, gram_apply, hk]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hone : 1 ≤ ∑ i, k i ^ 2 := by
    have hne : b.repr a ≠ 0 := by
      intro h0
      exact ha (b.repr.injective (h0.trans (map_zero b.repr).symm))
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
    have hi' : (b.repr a i : ℤ) ≠ 0 := by simpa using hi
    have h1 : (1 : ℝ) ≤ k i ^ 2 := by
      have habs : (1 : ℤ) ≤ |b.repr a i| := Int.one_le_abs hi'
      have habsR : (1 : ℝ) ≤ |((b.repr a i : ℤ) : ℝ)| := by exact_mod_cast habs
      simpa [hk] using one_le_sq_iff_one_le_abs _ |>.mpr habsR
    exact h1.trans (Finset.single_le_sum (fun j _ => sq_nonneg (k j)) (Finset.mem_univ i))
  calc c = c * 1 := (mul_one c).symm
    _ ≤ c * ∑ i, k i ^ 2 := by gcongr
    _ ≤ k ⬝ᵥ (Q.gram b).mulVec k := hcoer k
    _ = Q.form a a := hform.symm

/-- The β-scaled Boltzmann weights are summable at every `β > 0`. -/
theorem summable_scaled (β : ℝ) (hβ : 0 < β) :
    Summable (fun a : Q.Λ => Real.exp (-(β * Q.form a a))) :=
  (Q.scale β hβ).summable

/-- The excess partition function is the sum over nonzero lattice
points. -/
theorem scaledPartFn_sub_one (β : ℝ) (hβ : 0 < β) :
    Q.scaledPartFn β - 1
      = ∑' a : Q.Λ, if a = 0 then 0 else Real.exp (-(β * Q.form a a)) := by
  unfold scaledPartFn
  rw [(Q.summable_scaled β hβ).tsum_eq_add_tsum_ite 0]
  simp [Q.form_zero_left]

/-- **Exponential decay of `Z − 1`**: past `β = 1` the excess is
bounded by `C·exp(−c·β)`, `c` the energy gap. -/
theorem scaledPartFn_sub_one_le :
    ∃ c C : ℝ, 0 < c ∧ ∀ β : ℝ, 1 ≤ β →
      0 ≤ Q.scaledPartFn β - 1 ∧ Q.scaledPartFn β - 1 ≤ C * Real.exp (-c * β) := by
  obtain ⟨c, hc, hgap⟩ := Q.exists_energy_gap
  refine ⟨c, Real.exp c * (Q.scaledPartFn 1 - 1), hc, fun β hβ => ?_⟩
  have hβ0 : 0 < β := one_pos.trans_le hβ
  have hsum1 := Q.summable_scaled 1 one_pos
  have hterm_nn : ∀ a : Q.Λ,
      0 ≤ (if a = 0 then 0 else Real.exp (-(β * Q.form a a))) := fun a => by
    split_ifs <;> positivity
  have hterm_le : ∀ a : Q.Λ,
      (if a = 0 then 0 else Real.exp (-(β * Q.form a a)))
        ≤ Real.exp (-(c * (β - 1))) *
          (if a = 0 then 0 else Real.exp (-(1 * Q.form a a))) := fun a => by
    split_ifs with ha
    · simp
    · rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := hgap a ha
      nlinarith
  have hsum_ite1 : Summable (fun a : Q.Λ =>
      if a = 0 then (0 : ℝ) else Real.exp (-(1 * Q.form a a))) :=
    hsum1.of_nonneg_of_le (fun a => by split_ifs <;> positivity)
      (fun a => by split_ifs <;> simp [(Real.exp_pos _).le])
  have hsumβ : Summable (fun a : Q.Λ =>
      if a = 0 then (0 : ℝ) else Real.exp (-(β * Q.form a a))) :=
    (hsum_ite1.mul_left _).of_nonneg_of_le hterm_nn hterm_le
  refine ⟨?_, ?_⟩
  · rw [Q.scaledPartFn_sub_one β hβ0]
    exact tsum_nonneg hterm_nn
  · rw [Q.scaledPartFn_sub_one β hβ0]
    calc ∑' a, (if a = 0 then 0 else Real.exp (-(β * Q.form a a)))
        ≤ ∑' a, Real.exp (-(c * (β - 1))) *
            (if a = 0 then 0 else Real.exp (-(1 * Q.form a a))) :=
          hsumβ.tsum_le_tsum hterm_le (hsum_ite1.mul_left _)
      _ = Real.exp (-(c * (β - 1))) * (Q.scaledPartFn 1 - 1) := by
          rw [tsum_mul_left, Q.scaledPartFn_sub_one 1 one_pos]
      _ = Real.exp c * (Q.scaledPartFn 1 - 1) * Real.exp (-c * β) := by
          rw [show -(c * (β - 1)) = c + -c * β by ring, Real.exp_add]
          ring

/-- `Z − 1` is `O(x^r)` at infinity for every `r`, in `ℂ`. -/
theorem scaledPartFn_sub_one_isBigO (r : ℝ) :
    (fun x : ℝ => ((Q.scaledPartFn x : ℝ) : ℂ) - 1) =O[atTop] (· ^ r) := by
  obtain ⟨c, C, hc, hbound⟩ := Q.scaledPartFn_sub_one_le
  refine IsBigO.trans ?_ (isLittleO_exp_neg_mul_rpow_atTop hc r).isBigO
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  obtain ⟨h0, h1⟩ := hbound x hx
  rw [show ((Q.scaledPartFn x : ℝ) : ℂ) - 1 = ((Q.scaledPartFn x - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_of_nonneg h0, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact h1

/-- The partition function is continuous on `(0, ∞)`. -/
theorem continuousOn_scaledPartFn : ContinuousOn Q.scaledPartFn (Ioi 0) :=
  fun β hβ => (Q.hasDerivAt_scaledPartFn β hβ).continuousAt.continuousWithinAt

/-! ## The inversion law -/

/-- **The root number** `√(π^rank / disc)` of the lattice zeta. -/
noncomputable def rootNumber : ℝ := (Real.pi ^ Q.rank / Q.disc) ^ ((1 : ℝ) / 2)

theorem rootNumber_pos : 0 < Q.rootNumber :=
  Real.rpow_pos_of_pos (div_pos (pow_pos Real.pi_pos _) Q.disc_pos) _

/-- **The inversion law**: `Z_Q(1/x) = √(π^rank/disc)·x^{rank/2}·Z_{Q∨}(x)` —
the scaled Siegel–Poisson duality read at the dual bundle, with the
double dual transported back to the original. -/
theorem scaledPartFn_one_div (x : ℝ) (hx : 0 < x) :
    Q.scaledPartFn (1 / x)
      = Q.rootNumber * x ^ ((Q.rank : ℝ) / 2) * Q.dual.scaledPartFn x := by
  have h := Q.dual.scaled_duality x hx
  rw [← (Q.dualDual).scaledPartFn_eq x⁻¹, Q.dual_rank, Q.disc_dual] at h
  rw [one_div, h, rootNumber]
  have hπ : 0 < Real.pi ^ Q.rank := pow_pos Real.pi_pos _
  have hrw : x ^ Q.rank * (Real.pi ^ (2 * Q.rank) / Q.disc) / Real.pi ^ Q.rank
      = x ^ Q.rank * (Real.pi ^ Q.rank / Q.disc) := by
    rw [pow_mul', sq]
    field_simp
  rw [hrw, Real.mul_rpow (pow_nonneg hx.le _) (div_pos hπ Q.disc_pos).le,
    ← Real.rpow_natCast x Q.rank, ← Real.rpow_mul hx.le]
  ring_nf

/-! ## The functional-equation pair and the completed zeta -/

/-- **The FE-pair of a lattice action** of positive rank: `f = Z_Q`,
`g = Z_{Q∨}`, weight `rank/2`, root number `√(π^rank/disc)`, constant
terms `1` (the vacuum). The inversion law is `h_feq`; the energy gap
supplies the decay. -/
noncomputable def fePair (hr : 0 < Q.rank) : WeakFEPair ℂ where
  f x := (Q.scaledPartFn x : ℂ)
  g x := (Q.dual.scaledPartFn x : ℂ)
  k := (Q.rank : ℝ) / 2
  ε := (Q.rootNumber : ℂ)
  f₀ := 1
  g₀ := 1
  hf_int := (Complex.continuous_ofReal.comp_continuousOn
    Q.continuousOn_scaledPartFn).locallyIntegrableOn measurableSet_Ioi
  hg_int := (Complex.continuous_ofReal.comp_continuousOn
    Q.dual.continuousOn_scaledPartFn).locallyIntegrableOn measurableSet_Ioi
  hk := by positivity
  hε := Complex.ofReal_ne_zero.mpr Q.rootNumber_pos.ne'
  h_feq x hx := by
    rw [Q.scaledPartFn_one_div x hx, smul_eq_mul]
    push_cast
    rw [Complex.ofReal_cpow hx.le]
  hf_top r := Q.scaledPartFn_sub_one_isBigO r
  hg_top r := Q.dual.scaledPartFn_sub_one_isBigO r

/-- **The completed lattice zeta** `Λ_Q`. -/
noncomputable def completedZeta (hr : 0 < Q.rank) : ℂ → ℂ := (Q.fePair hr).Λ

/-- The dual's root number is the reciprocal one. -/
theorem dual_rootNumber : Q.dual.rootNumber = Q.rootNumber⁻¹ := by
  rw [rootNumber, rootNumber, Q.dual_rank, Q.disc_dual,
    ← Real.inv_rpow (div_pos (pow_pos Real.pi_pos _) Q.disc_pos).le]
  congr 1
  rw [pow_mul', sq]
  field_simp

/-- The symmetric pair of `Q` is the pair of its dual: `(Z_{Q∨}, Z_Q)`
with the reciprocal root number — the double dual transported. -/
theorem fePair_symm_Λ (hr : 0 < Q.rank) :
    (Q.fePair hr).symm.Λ = (Q.dual.fePair (Q.dual_rank ▸ hr)).Λ := by
  have hf : (Q.fePair hr).symm.f = (Q.dual.fePair (Q.dual_rank ▸ hr)).f := rfl
  have hk : (Q.fePair hr).symm.k = (Q.dual.fePair (Q.dual_rank ▸ hr)).k := by
    show (Q.rank : ℝ) / 2 = (Q.dual.rank : ℝ) / 2
    rw [Q.dual_rank]
  have hε : (Q.fePair hr).symm.ε = (Q.dual.fePair (Q.dual_rank ▸ hr)).ε := by
    show (Q.rootNumber : ℂ)⁻¹ = (Q.dual.rootNumber : ℂ)
    rw [Q.dual_rootNumber, Complex.ofReal_inv]
  funext s
  simp only [WeakFEPair.Λ, WeakFEPair.Λ₀, WeakFEPair.f_modif, hf, hk, hε]
  rfl

/-- **THE FUNCTIONAL EQUATION OF THE LATTICE ZETA**: the completed zeta of
a lattice at `rank/2 − s` is `√(π^rank/disc)` times the completed zeta of
its dual at `s` — Riemann's reflection, for every lattice, through the
one Siegel–Poisson engine. -/
theorem completedZeta_functional_equation (hr : 0 < Q.rank) (s : ℂ) :
    Q.completedZeta hr ((Q.rank : ℂ) / 2 - s)
      = (Q.rootNumber : ℂ) * Q.dual.completedZeta (Q.dual_rank ▸ hr) s := by
  have h := (Q.fePair hr).functional_equation s
  rw [Q.fePair_symm_Λ hr] at h
  have hk : ((Q.fePair hr).k : ℂ) = (Q.rank : ℂ) / 2 := by
    show (((Q.rank : ℝ) / 2 : ℝ) : ℂ) = _
    push_cast; ring
  rw [hk] at h
  exact h

/-! ## The Dirichlet expansion -/

/-- **The integer p-series**: `∑_{k ∈ ℤⁿ} ‖k‖^{−t}` converges for `t > n` —
Mathlib's lattice summability at the coordinate lattice. -/
theorem summable_intVec_norm_rpow {n : ℕ} {t : ℝ} (ht : (n : ℝ) < t) :
    Summable (fun k : Fin n → ℤ => ‖(fun i => (k i : ℝ))‖ ^ (-t)) := by
  set B := (Pi.basisFun ℝ (Fin n)).restrictScalars ℤ
  have hrank : Module.finrank ℤ (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))) = n := by
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin]
  have hsum := ZLattice.summable_norm_rpow
    (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))) (-t) (by rw [hrank]; linarith)
  have hcoe : ∀ k : Fin n → ℤ, ((B.equivFun.symm k : _) : Fin n → ℝ) = fun i => (k i : ℝ) := by
    intro k
    funext i
    simp [B, Module.Basis.equivFun_symm_apply, Pi.basisFun_apply, Finset.sum_apply,
      Pi.single_apply]
  refine ((Equiv.summable_iff B.equivFun.symm.toEquiv).mpr hsum).congr fun k => ?_
  simp only [Function.comp_apply, LinearEquiv.coe_toEquiv]
  rw [← hcoe k]
  rfl

/-- The sup norm of a coordinate vector is dominated by its square sum. -/
theorem sq_norm_le_sum_sq {n : ℕ} (x : Fin n → ℝ) : ‖x‖ ^ 2 ≤ ∑ i, x i ^ 2 := by
  have hnn : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h : ‖x‖ ≤ Real.sqrt (∑ i, x i ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt
      (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i))
  calc ‖x‖ ^ 2 ≤ Real.sqrt (∑ i, x i ^ 2) ^ 2 := by gcongr
    _ = ∑ i, x i ^ 2 := Real.sq_sqrt hnn

/-- **The lattice zeta series converges** past `rank/2`:
`∑_{a ≠ 0} E(a)^{−σ} < ∞` for `σ > rank/2` — coercivity of the Gram
chart against the integer p-series. -/
theorem summable_energy_rpow {σ : ℝ} (hσ : (Q.rank : ℝ) / 2 < σ) :
    Summable (fun a : Q.Λ => if a = 0 then (0 : ℝ) else Q.form a a ^ (-σ)) := by
  set b := Module.finBasis ℤ Q.Λ
  obtain ⟨c, hc, hcoer⟩ := (Q.gram_posDef b).exists_coercivity
  have hσ0 : 0 < σ := lt_of_le_of_lt (by positivity) hσ
  have hp := summable_intVec_norm_rpow (n := Module.finrank ℤ Q.Λ) (t := 2 * σ)
    (by have : ((Module.finrank ℤ Q.Λ : ℕ) : ℝ) = Q.rank := rfl; linarith)
  have hp' := (Equiv.summable_iff b.equivFun.toEquiv).mpr hp
  refine (hp'.mul_left (c ^ (-σ))).of_nonneg_of_le
    (fun a => by
      split_ifs
      · exact le_rfl
      · exact Real.rpow_nonneg (Q.form_self_nonneg a) _) fun a => ?_
  split_ifs with ha
  · exact mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg (norm_nonneg _) _)
  set k : Fin (Module.finrank ℤ Q.Λ) → ℝ := fun i => ((b.equivFun a i : ℤ) : ℝ) with hk
  have hform : Q.form a a = k ⬝ᵥ (Q.gram b).mulVec k := by
    rw [Q.form_repr b a a]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, gram_apply, hk,
      Module.Basis.equivFun_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hk0 : k ≠ 0 := by
    intro h0
    apply ha
    have : b.equivFun a = 0 := funext fun i => by
      have := congrFun h0 i
      simpa [hk] using this
    exact b.equivFun.injective (this.trans (map_zero _).symm)
  have hnorm_pos : 0 < ‖k‖ := norm_pos_iff.mpr hk0
  have hlow : c * ‖k‖ ^ 2 ≤ Q.form a a := by
    rw [hform]
    exact (mul_le_mul_of_nonneg_left (sq_norm_le_sum_sq k) hc.le).trans (hcoer k)
  have hpos : 0 < c * ‖k‖ ^ 2 := by positivity
  calc Q.form a a ^ (-σ) ≤ (c * ‖k‖ ^ 2) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos hpos hlow (by linarith)
    _ = c ^ (-σ) * ‖k‖ ^ (-(2 * σ)) := by
        rw [Real.mul_rpow hc.le (by positivity), ← Real.rpow_natCast ‖k‖ 2,
          ← Real.rpow_mul (norm_nonneg _)]
        congr 2
        push_cast; ring
    _ = c ^ (-σ) * ((fun k : Fin (Module.finrank ℤ Q.Λ) → ℤ =>
          ‖(fun i => (k i : ℝ))‖ ^ (-(2 * σ))) ∘ b.equivFun.toEquiv) a := rfl

/-- **THE DIRICHLET EXPANSION**: past `rank/2` the completed lattice zeta
is `Γ(s)·∑_{a ≠ 0} E(a)^{−s}` — Riemann's Mellin step, term by term, at
every lattice. -/
theorem hasSum_completedZeta (hr : 0 < Q.rank) {s : ℂ} (hs : (Q.rank : ℝ) / 2 < s.re) :
    HasSum (fun a : Q.Λ => Complex.Gamma s * (if a = 0 then 0 else 1)
        / ((Q.form a a : ℝ) : ℂ) ^ s)
      (Q.completedZeta hr s) := by
  have hs0 : 0 < s.re := lt_of_le_of_lt (by positivity) hs
  have hmel := ((Q.fePair hr).hasMellin (s := s) hs).2
  rw [completedZeta, ← hmel]
  have : Countable Q.Λ :=
    Countable.of_equiv _ (Module.finBasis ℤ Q.Λ).equivFun.toEquiv.symm
  refine hasSum_mellin (a := fun a : Q.Λ => if a = 0 then (0 : ℂ) else 1)
    (p := fun a => Q.form a a)
    (fun a => if ha : a = 0 then Or.inl (if_pos ha) else Or.inr (Q.form_posDef a ha))
    hs0 (fun t ht => ?_) ?_
  · have hreal := (Q.summable_scaled t ht).hasSum
    have hite := hasSum_ite_sub_hasSum hreal 0
    simp only [Q.form_zero_left, mul_zero, neg_zero, Real.exp_zero] at hite
    have hc := Complex.hasSum_ofReal.mpr hite
    convert hc using 1
    · funext a
      split_ifs <;> simp [mul_comm]
    · show ((Q.scaledPartFn t : ℝ) : ℂ) - 1 = ((Q.scaledPartFn t - 1 : ℝ) : ℂ)
      push_cast; ring
  · refine (Q.summable_energy_rpow hs).congr fun a => ?_
    split_ifs with ha
    · simp
    · rw [norm_one, one_div, Real.rpow_neg (Q.form_self_nonneg a)]


/-! ## Invariance and the graph zeta -/

/-- Form-preserving equivalence preserves rank. -/
theorem Equiv.rank_eq {Q Q' : QuadLatticeAction.{u}} (e : Q.Equiv Q') : Q'.rank = Q.rank :=
  (LinearEquiv.finrank_eq e.toLinearEquiv).symm

/-- **The zeta is an invariant of the bundle**: equivalent lattice actions
have the same completed zeta. -/
theorem Equiv.completedZeta_eq {Q Q' : QuadLatticeAction.{u}} (e : Q.Equiv Q')
    (hr : 0 < Q.rank) (hr' : 0 < Q'.rank) : Q'.completedZeta hr' = Q.completedZeta hr := by
  have hf : (Q'.fePair hr').f = (Q.fePair hr).f := by
    funext x
    show ((Q'.scaledPartFn x : ℝ) : ℂ) = ((Q.scaledPartFn x : ℝ) : ℂ)
    rw [e.scaledPartFn_eq x]
  have hk : (Q'.fePair hr').k = (Q.fePair hr).k := by
    show (Q'.rank : ℝ) / 2 = (Q.rank : ℝ) / 2
    rw [e.rank_eq]
  have hε : (Q'.fePair hr').ε = (Q.fePair hr).ε := by
    show (Q'.rootNumber : ℂ) = (Q.rootNumber : ℂ)
    rw [rootNumber, rootNumber, e.rank_eq, e.disc_eq]
  funext s
  simp only [completedZeta, WeakFEPair.Λ, WeakFEPair.Λ₀, WeakFEPair.f_modif, hf, hk, hε]
  rfl

end QuadLatticeAction

namespace IncidenceGraph

universe v

variable (G : IncidenceGraph.{v})

/-- The priced cycle lattice has rank `b₁`. -/
theorem cycleAction_rank : (G.cycleAction).rank = G.b1 := by
  rw [← (G.cycleActionEquivDual).rank_eq, QuadLatticeAction.dual_rank, G.classQuadAction_rank]

/-- **The zeta of a graph**: the completed lattice zeta of its harmonic
carrier `H¹(G;ℤ)`, on any graph with cycles. -/
noncomputable def completedZeta (hb : 0 < G.b1) : ℂ → ℂ :=
  (G.classQuadAction).completedZeta (G.classQuadAction_rank ▸ hb)

/-- **THE TOPOLOGICAL FUNCTIONAL EQUATION**: the zeta of harmonic `H¹` at
`b₁/2 − s` is the zeta of priced `H₁` at `s`, times the root number
`√(π^{b₁}/disc)` — Riemann's reflection, exchanging cohomology and
homology. -/
theorem completedZeta_functional_equation (hb : 0 < G.b1) (s : ℂ) :
    G.completedZeta hb ((G.b1 : ℂ) / 2 - s)
      = ((G.classQuadAction).rootNumber : ℂ)
        * (G.cycleAction).completedZeta (G.cycleAction_rank ▸ hb) s := by
  have hr : 0 < (G.classQuadAction).rank := G.classQuadAction_rank ▸ hb
  have h := (G.classQuadAction).completedZeta_functional_equation hr s
  have hcast : ((G.classQuadAction).rank : ℂ) = (G.b1 : ℂ) := by
    exact_mod_cast G.classQuadAction_rank
  rw [hcast] at h
  have he := (G.cycleActionEquivDual).completedZeta_eq (G.cycleAction_rank ▸ hb)
    ((G.classQuadAction).dual_rank ▸ hr)
  unfold completedZeta
  rw [h, he]

end IncidenceGraph

end Meno
