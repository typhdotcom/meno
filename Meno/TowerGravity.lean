import Meno.ResolutionCount
import Meno.Systole
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Arithmetic Gravity on the Tower (G3)

The tower face of the obstruction program (PLAN, G3).

* **CRT** (`h1ReductionCRT`): the finer reduction is the fiber
  product of the coarser ones over their common coarsening —
  `H1Reduction G (lcm q q') ≃ SGD.Pullback (h1TowerMap …) (h1TowerMap …)`,
  by componentwise Chinese remainder through the keystone
  coordinates; the counting identity is `Nat.gcd_mul_lcm` raised to
  `b₁` (`card_h1Reduction_mul_gcd`).
* **The key lemma** (`residueWeight_zero_eq_classScaledPartFn`): the
  modal coset weight is the scaled partition function —
  `residueWeight q 0 = classScaledPartFn (q²)`. The fiber of zero is
  `q·H¹` (`ker`-side of the reduction), multiplication by `q` is
  injective on the free lattice, and the energy is quadratic
  (`harmonicEnergy_zsmul`).
* **The exact law** (`residue_gravity_crossRatio`): via
  `classPartFn_eq_residueWeight_mul`, the four-resolution gravity
  defect is a cross-ratio of scaled partition functions.
* **The boundary** (`residue_gravity_dvd`): `q ∣ q'` collapses
  `{gcd, lcm}` to `{q, q'}` and the defect vanishes identically —
  **gravity is exact on the tower exactly along chains**.
* **The strictness** (`cycle3_crossRatio_neg`): on `cycleGraph 3` at
  `(q, q') = (2, 3)`, `Z(1)·Z(36) > Z(4)·Z(9)` by explicit partial
  sums with geometric tail bounds — the defect is strictly negative:
  **incomparable resolutions couple supermodularly**.
* **The impossibility** is the same theorem read as the face's
  negative: there is no resolution-independent gravity on the tower —
  exactness selects the divisibility order. -/

namespace Meno

open scoped BigOperators
open Matrix

universe u v

/-! ## `gcd`/`lcm` positivity instances -/

instance (q q' : ℕ) [NeZero q] : NeZero (Nat.gcd q q') :=
  ⟨fun h0 => NeZero.ne q (Nat.eq_zero_of_gcd_eq_zero_left h0)⟩

instance (q q' : ℕ) [NeZero q] [NeZero q'] : NeZero (Nat.lcm q q') := by
  constructor
  intro h0
  have h := Nat.gcd_mul_lcm q q'
  rw [h0, mul_zero] at h
  exact absurd h.symm (mul_ne_zero (NeZero.ne q) (NeZero.ne q'))

/-! ## Quadratic scaling of the harmonic energy -/

/-- The Gram-form energy scales quadratically under integer scalar
multiplication of the sector. -/
theorem HarmonicGramData.energy_zsmul {V : Type u} (H : HarmonicGramData V)
    (c : ℤ) (k : Fin H.r → ℤ) :
    H.energy (c • k) = ((c : ℝ)) ^ 2 * H.energy k := by
  show ∑ i, ∑ j, H.gram i j * ((c • k) i : ℝ) * ((c • k) j : ℝ)
    = (c : ℝ) ^ 2 * ∑ i, ∑ j, H.gram i j * (k i : ℝ) * (k j : ℝ)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show H.gram i j * ((c * k i : ℤ) : ℝ) * ((c * k j : ℤ) : ℝ)
    = (c : ℝ) ^ 2 * (H.gram i j * (k i : ℝ) * (k j : ℝ))
  push_cast
  ring

namespace IncidenceGraph

variable (G : IncidenceGraph.{u, v})

/-- **The harmonic energy is quadratic** (G3 key-lemma engine):
`E(c • κ) = c² · E(κ)`. -/
theorem harmonicEnergy_zsmul (c : ℤ)
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :
    G.harmonicEnergy (c • κ) = ((c : ℝ)) ^ 2 * G.harmonicEnergy κ := by
  show (G.basisGramData G.cycleBasis).energy (G.h1QuotEquiv (c • κ)) = _
  rw [map_smul]
  exact HarmonicGramData.energy_zsmul _ c _

/-! ## The key lemma -/

/-- **THE KEY LEMMA** (G3): the modal coset weight is the scaled
partition function — `residueWeight q 0 = classScaledPartFn (q²)`,
with `classScaledPartFn` the standing β-scaled carrier partition
function (`Meno/BasisIndependence.lean`). The fiber of zero is
`q·H¹`, multiplication by `q` enumerates it from the carrier
(injectively, on the free lattice), and the energy is quadratic. -/
theorem residueWeight_zero_eq_classScaledPartFn (q : ℕ) [NeZero q] :
    G.residueWeight q 0 = G.classScaledPartFn ((q : ℝ) ^ 2) := by
  have hq0 : ((q : ℤ)) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hbij : Function.Bijective
      (fun κ' : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) =>
        (⟨(q : ℤ) • κ', by
          rw [Submodule.Quotient.mk_eq_zero]
          exact ⟨κ', rfl⟩⟩ :
        {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) //
          (Submodule.Quotient.mk κ : H1Reduction G q) = 0})) := by
    constructor
    · intro a b hab
      have h := Subtype.ext_iff.mp hab
      have h2 := congrArg (⇑G.h1QuotEquiv) h
      rw [map_smul, map_smul] at h2
      apply G.h1QuotEquiv.injective
      funext i
      have h3 := congrFun h2 i
      simp only [Pi.smul_apply, smul_eq_mul] at h3
      exact mul_left_cancel₀ hq0 h3
    · rintro ⟨κ, hκ⟩
      rw [Submodule.Quotient.mk_eq_zero] at hκ
      obtain ⟨κ', hκ'⟩ := hκ
      exact ⟨κ', Subtype.ext (by
        show (q : ℤ) • κ' = κ
        simpa using hκ')⟩
  show (∑' κ : {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) //
      (Submodule.Quotient.mk κ : H1Reduction G q) = 0},
    (G.classSectorAction).weight κ.val) = _
  rw [← Equiv.tsum_eq (Equiv.ofBijective _ hbij)
    (fun κ : {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) //
        (Submodule.Quotient.mk κ : H1Reduction G q) = 0} =>
      (G.classSectorAction).weight κ.val)]
  refine tsum_congr fun κ' => ?_
  show Real.exp (-(G.harmonicEnergy ((q : ℤ) • κ')))
    = Real.exp (-((q : ℝ) ^ 2 * G.harmonicEnergy κ'))
  rw [G.harmonicEnergy_zsmul (q : ℤ) κ']
  push_cast
  ring_nf

/-- The residue complexity in scaled-partition-function form: the
harmonic complexity minus the log modal weight. -/
theorem residueAction_complexity_eq (q : ℕ) [NeZero q] :
    (G.residueAction q).complexity
      = (G.classSectorAction).complexity
        - Real.log (G.classScaledPartFn ((q : ℝ) ^ 2)) := by
  have h := G.classComplexity_residue_split q
  rw [G.residueWeight_zero_eq_classScaledPartFn q] at h
  linarith

/-! ## The exact law and its boundary -/

/-- **THE CROSS-RATIO LAW** (G3, the exact law): the four-resolution
gravity defect on the tower is a cross-ratio of scaled partition
functions — via the factorization
`classPartFn_eq_residueWeight_mul` and the key lemma, each residue
complexity is the harmonic complexity minus a scaled log, and the
base complexities cancel in the four-term combination. -/
theorem residue_gravity_crossRatio (q q' : ℕ) [NeZero q] [NeZero q'] :
    ((G.residueAction (Nat.lcm q q')).complexity
        + (G.residueAction (Nat.gcd q q')).complexity)
      - ((G.residueAction q).complexity + (G.residueAction q').complexity)
    = (Real.log (G.classScaledPartFn ((q : ℝ) ^ 2))
        + Real.log (G.classScaledPartFn ((q' : ℝ) ^ 2)))
      - (Real.log (G.classScaledPartFn ((Nat.gcd q q' : ℝ) ^ 2))
        + Real.log (G.classScaledPartFn ((Nat.lcm q q' : ℝ) ^ 2))) := by
  rw [G.residueAction_complexity_eq q, G.residueAction_complexity_eq q',
    G.residueAction_complexity_eq (Nat.gcd q q'),
    G.residueAction_complexity_eq (Nat.lcm q q')]
  ring

/-- **The boundary** (G3): along a divisibility chain the defect
vanishes identically — `{gcd, lcm} = {q, q'}` and the cross-ratio
cancels. **Gravity is exact on the tower exactly along chains.** -/
theorem residue_gravity_dvd (q q' : ℕ) [NeZero q] [NeZero q']
    (hdvd : q ∣ q') :
    ((G.residueAction (Nat.lcm q q')).complexity
        + (G.residueAction (Nat.gcd q q')).complexity)
      - ((G.residueAction q).complexity + (G.residueAction q').complexity)
    = 0 := by
  rw [G.residue_gravity_crossRatio q q', Nat.gcd_eq_left hdvd,
    Nat.dvd_antisymm (Nat.lcm_dvd hdvd dvd_rfl) (Nat.dvd_lcm_right q q')]
  ring

/-! ## Chinese remainder on the tower -/

/-- **CRT ON THE TOWER** (G3): the `lcm` reduction is the fiber
product of the two reductions over their common coarsening — the
finer resolution **is** the coupling of the coarser ones, so the
cross-ratio law is a gravity statement. Componentwise Chinese
remainder: injectivity is `lcm`-divisibility of the keystone
coordinates, surjectivity is the fiber count. -/
noncomputable def h1ReductionCRT (q q' : ℕ) [NeZero q] [NeZero q'] :
    H1Reduction G (Nat.lcm q q')
      ≃ SGD.Pullback
          (⇑(G.h1TowerMap (Nat.gcd q q') q (Nat.gcd_dvd_left q q')))
          (⇑(G.h1TowerMap (Nat.gcd q q') q' (Nat.gcd_dvd_right q q'))) := by
  haveI : Finite (SGD.Pullback
      (⇑(G.h1TowerMap (Nat.gcd q q') q (Nat.gcd_dvd_left q q')))
      (⇑(G.h1TowerMap (Nat.gcd q q') q' (Nat.gcd_dvd_right q q')))) :=
    inferInstanceAs (Finite
      {p : H1Reduction G q × H1Reduction G q' //
        G.h1TowerMap (Nat.gcd q q') q (Nat.gcd_dvd_left q q') p.1
          = G.h1TowerMap (Nat.gcd q q') q' (Nat.gcd_dvd_right q q') p.2})
  refine Equiv.ofBijective
    (fun ξ => ⟨(G.h1TowerMap q (Nat.lcm q q') (Nat.dvd_lcm_left q q') ξ,
        G.h1TowerMap q' (Nat.lcm q q') (Nat.dvd_lcm_right q q') ξ), ?_⟩)
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩)
  · obtain ⟨κ, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    rfl
  · intro ξ η hξη
    obtain ⟨κ, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    obtain ⟨κ', rfl⟩ := Submodule.Quotient.mk_surjective _ η
    have hpair := Subtype.ext_iff.mp hξη
    have h1 : (Submodule.Quotient.mk κ : H1Reduction G q)
        = Submodule.Quotient.mk κ' := congrArg Prod.fst hpair
    have h2 : (Submodule.Quotient.mk κ : H1Reduction G q')
        = Submodule.Quotient.mk κ' := congrArg Prod.snd hpair
    rw [Submodule.Quotient.eq] at h1 h2 ⊢
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    have ha' : (q : ℤ) • a = κ - κ' := ha
    have hb' : (q' : ℤ) • b = κ - κ' := hb
    have hdvd : ∀ i, ((Nat.lcm q q' : ℕ) : ℤ) ∣ G.h1QuotEquiv (κ - κ') i := by
      intro i
      have hqa : ((q : ℕ) : ℤ) ∣ G.h1QuotEquiv (κ - κ') i := by
        refine ⟨G.h1QuotEquiv a i, ?_⟩
        have h := congrFun (congrArg (⇑G.h1QuotEquiv) ha') i
        rw [map_smul] at h
        simpa [Pi.smul_apply, smul_eq_mul] using h.symm
      have hqb : ((q' : ℕ) : ℤ) ∣ G.h1QuotEquiv (κ - κ') i := by
        refine ⟨G.h1QuotEquiv b i, ?_⟩
        have h := congrFun (congrArg (⇑G.h1QuotEquiv) hb') i
        rw [map_smul] at h
        simpa [Pi.smul_apply, smul_eq_mul] using h.symm
      rw [← Int.natAbs_dvd_natAbs] at hqa hqb ⊢
      rw [Int.natAbs_natCast] at hqa hqb ⊢
      exact Nat.lcm_dvd hqa hqb
    choose y hy using hdvd
    refine ⟨(G.h1QuotEquiv).symm y, ?_⟩
    show ((Nat.lcm q q' : ℕ) : ℤ) • ((G.h1QuotEquiv).symm y) = κ - κ'
    apply G.h1QuotEquiv.injective
    rw [map_smul, LinearEquiv.apply_symm_apply]
    funext i
    show ((Nat.lcm q q' : ℕ) : ℤ) * y i = G.h1QuotEquiv (κ - κ') i
    exact (hy i).symm
  · have hq : q = q / Nat.gcd q q' * Nat.gcd q q' :=
      (Nat.div_mul_cancel (Nat.gcd_dvd_left q q')).symm
    have hq' : q' = q' / Nat.gcd q q' * Nat.gcd q q' :=
      (Nat.div_mul_cancel (Nat.gcd_dvd_right q q')).symm
    have hfib : ∀ d : H1Reduction G (Nat.gcd q q'),
        Nat.card (SGD.FiberProd
          (⇑(G.h1TowerMap (Nat.gcd q q') q (Nat.gcd_dvd_left q q')))
          (⇑(G.h1TowerMap (Nat.gcd q q') q' (Nat.gcd_dvd_right q q'))) d)
          = (q / Nat.gcd q q') ^ G.b1 * (q' / Nat.gcd q q') ^ G.b1 := by
      intro d
      rw [Nat.card_prod,
        G.card_h1TowerMap_fiber (Nat.gcd q q') q (q / Nat.gcd q q')
          (Nat.gcd_dvd_left q q') hq d,
        G.card_h1TowerMap_fiber (Nat.gcd q q') q' (q' / Nat.gcd q q')
          (Nat.gcd_dvd_right q q') hq' d]
    have harith : Nat.lcm q q'
        = Nat.gcd q q' * (q / Nat.gcd q q') * (q' / Nat.gcd q q') := by
      have hgcd0 : 0 < Nat.gcd q q' :=
        Nat.pos_of_ne_zero (NeZero.ne (Nat.gcd q q'))
      apply Nat.eq_of_mul_eq_mul_left hgcd0
      calc Nat.gcd q q' * Nat.lcm q q' = q * q' := Nat.gcd_mul_lcm q q'
        _ = (Nat.gcd q q' * (q / Nat.gcd q q'))
            * (Nat.gcd q q' * (q' / Nat.gcd q q')) := by
            rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left q q'),
              Nat.mul_div_cancel' (Nat.gcd_dvd_right q q')]
        _ = Nat.gcd q q'
            * (Nat.gcd q q' * (q / Nat.gcd q q') * (q' / Nat.gcd q q')) := by
            ring
    rw [G.card_H1Reduction (Nat.lcm q q'),
      Nat.card_congr (SGD.Pullback.equivSigmaFiber _ _), Nat.card_sigma,
      Finset.sum_congr rfl fun d _ => hfib d, Finset.sum_const,
      Finset.card_univ, ← Nat.card_eq_fintype_card,
      G.card_H1Reduction (Nat.gcd q q'), smul_eq_mul, harith]
    ring

/-- **Counting on the tower** (G3): the CRT counting identity —
`Nat.gcd_mul_lcm` raised to `b₁`. -/
theorem card_h1Reduction_mul_gcd (q q' : ℕ) [NeZero q] [NeZero q'] :
    Nat.card (H1Reduction G (Nat.lcm q q'))
        * Nat.card (H1Reduction G (Nat.gcd q q'))
      = Nat.card (H1Reduction G q) * Nat.card (H1Reduction G q') := by
  rw [G.card_H1Reduction (Nat.lcm q q'), G.card_H1Reduction (Nat.gcd q q'),
    G.card_H1Reduction q, G.card_H1Reduction q', ← mul_pow, ← mul_pow,
    show Nat.lcm q q' * Nat.gcd q q' = q * q' from by
      rw [mul_comm]
      exact Nat.gcd_mul_lcm q q']

end IncidenceGraph

/-! ## The strictness: incomparable resolutions couple supermodularly

On `cycleGraph 3` the carrier is rank one with harmonic energy
`k²/3`, so the scaled partition functions are the scalar theta values
`Z(s/3)`. At `(q, q') = (2, 3)` the cross-ratio compares
`Z(4/3)·Z(3)` against `Z(1/3)·Z(12)`, and explicit partial sums with
geometric tail bounds give `Z(4/3)·Z(3) < Z(1/3)·Z(12)` — the defect
is strictly negative. **The impossibility, read off the same
theorem: there is no resolution-independent gravity on the tower —
exactness selects the divisibility order.** -/

section ScalarEstimates

open QuadraticAction

/-- Per-mode geometric domination: `exp(−α(k+1)²) ≤ exp(−α)·exp(−α)^k`. -/
private lemma exp_sq_shift_le_geo (α : ℝ) (hα : 0 < α) (k : ℕ) :
    Real.exp (-α * ((k : ℝ) + 1) ^ 2) ≤ Real.exp (-α) * Real.exp (-α) ^ k := by
  rw [show Real.exp (-α) * Real.exp (-α) ^ k = Real.exp (-α * ((k : ℝ) + 1)) from by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    ring_nf]
  refine Real.exp_le_exp.mpr ?_
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (k:ℝ) + 1) hk]

private lemma summable_exp_sq_shift (α : ℝ) (hα : 0 < α) :
    Summable (fun k : ℕ => Real.exp (-α * ((k : ℝ) + 1) ^ 2)) := by
  have hlt : Real.exp (-α) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hgeo : Summable (fun k : ℕ => Real.exp (-α) * Real.exp (-α) ^ k) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hlt).mul_left _
  exact Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le)
    (exp_sq_shift_le_geo α hα) hgeo

/-- Symmetric split of the scalar theta value (the estimate
discipline of `Meno/Zeta.lean`, restated for the tower face). -/
private lemma scalarPartFn_sub_one_eq (α : ℝ) (hα : 0 < α) :
    scalarPartFn α - 1 = 2 * ∑' k : ℕ, Real.exp (-α * ((k : ℝ) + 1) ^ 2) := by
  set S : ℝ := ∑' k : ℕ, Real.exp (-α * ((k : ℝ) + 1) ^ 2) with hS_def
  have hshift : Summable (fun k : ℕ => Real.exp (-α * ((k : ℝ) + 1) ^ 2)) :=
    summable_exp_sq_shift α hα
  have hSum_S : HasSum (fun k : ℕ => Real.exp (-α * ((k : ℝ) + 1) ^ 2)) S :=
    hshift.hasSum
  have hf₁ : HasSum
      (fun n : ℕ => Real.exp (-α * ((((n : ℤ) + 1) : ℤ) : ℝ) ^ 2)) S := by
    refine hSum_S.congr fun n => ?_
    push_cast
    rfl
  have hf₂ : HasSum
      (fun n : ℕ => Real.exp (-α * ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2)) S := by
    refine hSum_S.congr fun n => ?_
    push_cast
    ring_nf
  have hZ : HasSum (fun k : ℤ => Real.exp (-α * ((k : ℤ) : ℝ) ^ 2))
      (S + Real.exp (-α * (((0 : ℤ) : ℝ)) ^ 2) + S) :=
    HasSum.of_add_one_of_neg_add_one hf₁ hf₂
  have hZ_val : scalarPartFn α = S + 1 + S := by
    have h := hZ.tsum_eq
    have h0 : Real.exp (-α * (((0 : ℤ) : ℝ)) ^ 2) = 1 := by simp
    rw [h0] at h
    show ∑' k : ℤ, Real.exp (-α * (k : ℝ) ^ 2) = S + 1 + S
    convert h using 1
  rw [hZ_val]
  ring

/-- The scalar theta value dominates its vacuum term. -/
private lemma one_le_scalarPartFn (α : ℝ) (hα : 0 < α) :
    1 ≤ scalarPartFn α := by
  have h := scalarPartFn_sub_one_eq α hα
  have hS : (0 : ℝ) ≤ ∑' k : ℕ, Real.exp (-α * ((k : ℝ) + 1) ^ 2) :=
    tsum_nonneg fun k => (Real.exp_pos _).le
  linarith

/-- First-mode lower bound: `1 + 2·exp(−α) ≤ Z(α)`. -/
private lemma scalarPartFn_ge (α : ℝ) (hα : 0 < α) :
    1 + 2 * Real.exp (-α) ≤ scalarPartFn α := by
  have h := scalarPartFn_sub_one_eq α hα
  have hfirst : Real.exp (-α)
      ≤ ∑' k : ℕ, Real.exp (-α * ((k : ℝ) + 1) ^ 2) := by
    have hle := (summable_exp_sq_shift α hα).sum_le_tsum {0}
      (fun j _ => (Real.exp_pos _).le)
    rw [Finset.sum_singleton] at hle
    calc Real.exp (-α) = Real.exp (-α * (((0 : ℕ) : ℝ) + 1) ^ 2) := by
          norm_num
      _ ≤ _ := hle
  linarith

/-- Geometric tail upper bound: `Z(α) ≤ 1 + 2·exp(−α)/(1−exp(−α))`. -/
private lemma scalarPartFn_le (α : ℝ) (hα : 0 < α) :
    scalarPartFn α ≤ 1 + 2 * (Real.exp (-α) / (1 - Real.exp (-α))) := by
  have h := scalarPartFn_sub_one_eq α hα
  have hexp_pos : (0 : ℝ) < Real.exp (-α) := Real.exp_pos _
  have hlt : Real.exp (-α) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hgeo : Summable (fun k : ℕ => Real.exp (-α) ^ k) :=
    summable_geometric_of_lt_one hexp_pos.le hlt
  have hbound : ∑' k : ℕ, Real.exp (-α * ((k : ℝ) + 1) ^ 2)
      ≤ Real.exp (-α) / (1 - Real.exp (-α)) := by
    calc ∑' k : ℕ, Real.exp (-α * ((k : ℝ) + 1) ^ 2)
        ≤ ∑' k : ℕ, Real.exp (-α) * Real.exp (-α) ^ k :=
          (summable_exp_sq_shift α hα).tsum_le_tsum
            (exp_sq_shift_le_geo α hα) (hgeo.mul_left _)
      _ = Real.exp (-α) * ∑' k : ℕ, Real.exp (-α) ^ k :=
          hgeo.tsum_mul_left (Real.exp (-α))
      _ = Real.exp (-α) * (1 - Real.exp (-α))⁻¹ := by
          rw [tsum_geometric_of_lt_one hexp_pos.le hlt]
      _ = Real.exp (-α) / (1 - Real.exp (-α)) := by
          rw [div_eq_mul_inv]
  linarith

/-- Bounds on `exp(1/3)` from the ninth-decimal bounds on `e`. -/
private lemma exp_third_bounds :
    (1.39 : ℝ) < Real.exp (1 / 3) ∧ Real.exp (1 / 3) < 10 / 7 := by
  have hcube : Real.exp (1 / 3) ^ 3 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hgt := Real.exp_one_gt_d9
  have hlt := Real.exp_one_lt_d9
  have hpos : (0 : ℝ) < Real.exp (1 / 3) := Real.exp_pos _
  constructor
  · by_contra hle
    push_neg at hle
    have h3 : Real.exp (1 / 3) ^ 3 ≤ (1.39 : ℝ) ^ 3 := by
      exact pow_le_pow_left₀ hpos.le hle 3
    rw [hcube] at h3
    norm_num at h3
    linarith
  · by_contra hge
    push_neg at hge
    have h3 : (10 / 7 : ℝ) ^ 3 ≤ Real.exp (1 / 3) ^ 3 := by
      exact pow_le_pow_left₀ (by norm_num) hge 3
    rw [hcube] at h3
    norm_num at h3
    linarith

/-- The three numeric exponential bounds the strictness consumes. -/
private lemma exp_numeric_bounds :
    (7 / 10 : ℝ) < Real.exp (-(1 / 3))
      ∧ Real.exp (-(4 / 3)) < 27 / 100
      ∧ Real.exp (-3) < 1 / 20 := by
  obtain ⟨hy1, hy2⟩ := exp_third_bounds
  have hpos : (0 : ℝ) < Real.exp (1 / 3) := Real.exp_pos _
  have hcube : Real.exp (1 / 3) ^ 3 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hgt := Real.exp_one_gt_d9
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.exp_neg]
    calc (7 / 10 : ℝ) = (10 / 7 : ℝ)⁻¹ := by norm_num
      _ < (Real.exp (1 / 3))⁻¹ := by
          exact inv_strictAnti₀ hpos hy2
  · have h4 : Real.exp (-(4 / 3)) = (Real.exp (1 / 3) ^ 4)⁻¹ := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]
      norm_num
    rw [h4]
    have hy4 : (100 / 27 : ℝ) < Real.exp (1 / 3) ^ 4 := by
      have : Real.exp (1 / 3) ^ 4 = Real.exp (1 / 3) * Real.exp 1 := by
        rw [← hcube]
        ring
      rw [this]
      nlinarith
    calc (Real.exp (1 / 3) ^ 4)⁻¹ < (100 / 27 : ℝ)⁻¹ := by
          exact inv_strictAnti₀ (by norm_num) hy4
      _ = 27 / 100 := by norm_num
  · have h3 : Real.exp (-3) = (Real.exp 1 ^ 3)⁻¹ := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]
      norm_num
    rw [h3]
    have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have h2 : (2.7182818283 : ℝ) ^ 2 < Real.exp 1 ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hgt)
        (by positivity : (0 : ℝ) < Real.exp 1 + 2.7182818283)]
    have he3 : (20 : ℝ) < Real.exp 1 ^ 3 := by
      nlinarith [mul_pos (sub_pos.mpr hgt)
        (by positivity : (0 : ℝ) < Real.exp 1 ^ 2), h2, hgt, he_pos]
    calc (Real.exp 1 ^ 3)⁻¹ < (20 : ℝ)⁻¹ := by
          exact inv_strictAnti₀ (by norm_num) he3
      _ = 1 / 20 := by norm_num

/-- **The theta-value comparison**: `Z(4/3)·Z(3) < Z(1/3)·Z(12)` —
partial sums against geometric tails, closed by rational
arithmetic. -/
private lemma scalarPartFn_crossRatio_lt :
    scalarPartFn (4 / 3) * scalarPartFn 3
      < scalarPartFn (1 / 3) * scalarPartFn 12 := by
  obtain ⟨hc, ha, hb⟩ := exp_numeric_bounds
  have ha_pos : (0 : ℝ) < Real.exp (-(4 / 3)) := Real.exp_pos _
  have hb_pos : (0 : ℝ) < Real.exp (-3) := Real.exp_pos _
  have h43 : scalarPartFn (4 / 3) < 127 / 73 := by
    have hle := scalarPartFn_le (4 / 3) (by norm_num)
    have hfrac : Real.exp (-(4 / 3)) / (1 - Real.exp (-(4 / 3))) < 27 / 73 := by
      rw [div_lt_iff₀ (by nlinarith)]
      nlinarith
    linarith
  have h3 : scalarPartFn 3 < 21 / 19 := by
    have hle := scalarPartFn_le 3 (by norm_num)
    have hfrac : Real.exp (-3) / (1 - Real.exp (-3)) < 1 / 19 := by
      rw [div_lt_iff₀ (by nlinarith)]
      nlinarith
    linarith
  have h13 : (12 / 5 : ℝ) < scalarPartFn (1 / 3) := by
    have hge := scalarPartFn_ge (1 / 3) (by norm_num)
    have : Real.exp (-(1 / 3)) = Real.exp (-(1 / 3)) := rfl
    nlinarith
  have h12 : (1 : ℝ) ≤ scalarPartFn 12 := one_le_scalarPartFn 12 (by norm_num)
  have h43_pos : (0 : ℝ) < scalarPartFn (4 / 3) := by
    have := one_le_scalarPartFn (4 / 3) (by norm_num)
    linarith
  have h3_pos : (0 : ℝ) < scalarPartFn 3 := by
    have := one_le_scalarPartFn 3 (by norm_num)
    linarith
  calc scalarPartFn (4 / 3) * scalarPartFn 3
      < (127 / 73) * (21 / 19) := by
        exact mul_lt_mul'' h43 h3 h43_pos.le h3_pos.le
    _ < 12 / 5 := by norm_num
    _ < scalarPartFn (1 / 3) := h13
    _ ≤ scalarPartFn (1 / 3) * scalarPartFn 12 := by
        nlinarith [h13]

end ScalarEstimates

/-! ## The strictness on `C₃` -/

/-- **The `C₃` scaled partition functions are the scalar theta
values**: the rank-one carrier with energy `k²/3` sums to `Z(s/3)`. -/
theorem cycle3_classScaledPartFn (s : ℝ) :
    (cycleGraph 3 (by norm_num)).classScaledPartFn s
      = QuadraticAction.scalarPartFn (s / 3) := by
  have hE : ∀ k : ℤ,
      (cycleGraph 3 (by norm_num)).harmonicEnergy
          (((cycleGraph 3 (by norm_num)).latticeQuotEquiv
              (cycleLatticeBasis 3 (by norm_num))).symm
            ((Equiv.funUnique (Fin 1) ℤ).symm k))
        = (k : ℝ) ^ 2 / 3 := by
    intro k
    rw [← (cycleGraph 3 (by norm_num)).basisGramData_energy_latticeQuot
      (cycleLatticeBasis 3 (by norm_num)), LinearEquiv.apply_symm_apply]
    show ∑ i, ∑ j,
        (gramOf ((cycleGraph 3 (by norm_num)).cyclesR
            (cycleLatticeBasis 3 (by norm_num))))⁻¹ i j
          * (((Equiv.funUnique (Fin 1) ℤ).symm k) i : ℝ)
          * (((Equiv.funUnique (Fin 1) ℤ).symm k) j : ℝ)
      = (k : ℝ) ^ 2 / 3
    rw [cyclesR_cycleLatticeBasis 3 (by norm_num), gramOf_cycleAllOnes,
      inv_fin_one ((3 : ℕ) : ℝ) (by norm_num)]
    norm_num [Fin.sum_univ_one, Equiv.funUnique_symm_apply]
    ring
  show (∑' κ : (Fin 3 → ℤ) ⧸ LinearMap.range
      ((cycleGraph 3 (by norm_num)).gradLin ℤ),
    Real.exp (-(s
      * (cycleGraph 3 (by norm_num)).harmonicEnergy κ))) = _
  rw [← Equiv.tsum_eq
    ((Equiv.funUnique (Fin 1) ℤ).symm.trans
      ((cycleGraph 3 (by norm_num)).latticeQuotEquiv
        (cycleLatticeBasis 3 (by norm_num))).symm.toEquiv)
    (fun κ => Real.exp (-(s
      * (cycleGraph 3 (by norm_num)).harmonicEnergy κ)))]
  refine tsum_congr fun k => ?_
  rw [show ((Equiv.funUnique (Fin 1) ℤ).symm.trans
      ((cycleGraph 3 (by norm_num)).latticeQuotEquiv
        (cycleLatticeBasis 3 (by norm_num))).symm.toEquiv) k
      = ((cycleGraph 3 (by norm_num)).latticeQuotEquiv
          (cycleLatticeBasis 3 (by norm_num))).symm
        ((Equiv.funUnique (Fin 1) ℤ).symm k) from rfl,
    hE k]
  congr 1
  ring

/-- **THE STRICTNESS** (G3): on `cycleGraph 3` at `(q, q') = (2, 3)`
the four-resolution defect is strictly negative —
`Z(1)·Z(36) > Z(4)·Z(9)` at the carrier scale, i.e.
`Z(1/3)·Z(12) > Z(4/3)·Z(3)` in theta values. **Incomparable
resolutions couple supermodularly. The impossibility, read off the
same statement: there is no resolution-independent gravity on the
tower — exactness selects the divisibility order.** -/
theorem cycle3_crossRatio_neg :
    (((cycleGraph 3 (by norm_num)).residueAction (Nat.lcm 2 3)).complexity
        + ((cycleGraph 3 (by norm_num)).residueAction
            (Nat.gcd 2 3)).complexity)
      - (((cycleGraph 3 (by norm_num)).residueAction 2).complexity
        + ((cycleGraph 3 (by norm_num)).residueAction 3).complexity)
    < 0 := by
  rw [(cycleGraph 3 (by norm_num)).residue_gravity_crossRatio 2 3,
    show Nat.gcd 2 3 = 1 from by decide,
    show Nat.lcm 2 3 = 6 from by decide,
    cycle3_classScaledPartFn, cycle3_classScaledPartFn,
    cycle3_classScaledPartFn, cycle3_classScaledPartFn]
  have harg1 : (((2 : ℕ) : ℝ) ^ 2) / 3 = 4 / 3 := by norm_num
  have harg2 : (((3 : ℕ) : ℝ) ^ 2) / 3 = 3 := by norm_num
  have harg3 : (((1 : ℕ) : ℝ) ^ 2) / 3 = 1 / 3 := by norm_num
  have harg4 : (((6 : ℕ) : ℝ) ^ 2) / 3 = 12 := by norm_num
  rw [harg1, harg2, harg3, harg4]
  have hkey := scalarPartFn_crossRatio_lt
  have hp1 : (0 : ℝ) < QuadraticAction.scalarPartFn (4 / 3) := by
    have := one_le_scalarPartFn (4 / 3) (by norm_num)
    linarith
  have hp2 : (0 : ℝ) < QuadraticAction.scalarPartFn 3 := by
    have := one_le_scalarPartFn 3 (by norm_num)
    linarith
  have hp3 : (0 : ℝ) < QuadraticAction.scalarPartFn (1 / 3) := by
    have := one_le_scalarPartFn (1 / 3) (by norm_num)
    linarith
  have hp4 : (0 : ℝ) < QuadraticAction.scalarPartFn 12 := by
    have := one_le_scalarPartFn 12 (by norm_num)
    linarith
  have hlog := Real.log_lt_log (mul_pos hp1 hp2) hkey
  rw [Real.log_mul hp1.ne' hp2.ne', Real.log_mul hp3.ne' hp4.ne'] at hlog
  linarith

end Meno
