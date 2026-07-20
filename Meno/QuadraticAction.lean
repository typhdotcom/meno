import Meno.SectorAction
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-! # Quadratic Action and Scalar Siegel–Poisson Duality

A `QuadraticAction r` is the analytic primitive whose sector lattice is
`Fin r → ℤ` and whose energy is `kᵀ Q k` for a symmetric positive-definite
Gram matrix `Q`. Summability of the Boltzmann weight is **derived** from
`Q.PosDef` (`summable_exp_neg_quadForm`, via the eigenvalue-free
coercivity bound `Matrix.PosDef.exists_coercivity`): it is a theorem
(`QuadraticAction.summable`), not a stored field.

The rank-1 case `ofScalar α hα` builds `QuadraticAction 1` with `Q = !![α]`;
its partition function equals `∑' k : ℤ, exp(-α k²)`. The scalar
**T-duality** `Z(π²/α) = √(α/π) · Z(α)` is relocated here from
`Duality.lean`. Its proof goes through `jacobiTheta` and the modular
`S`-transformation.

The general matrix Siegel–Poisson duality
`Z(π²·Q⁻¹) = √(det Q / π^r) · Z(Q)` is proved at full generality in
`Meno/SiegelPoisson.lean` (multidimensional Poisson summation over the
integer lattice); the diagonal cases below are its elementary
corroborating derivations. -/

namespace Meno

open scoped BigOperators
open UpperHalfPlane Complex Matrix

universe u

/-! ## The summability engine, upstream of the structure

Scalar Gaussian sums, the product factorization over `ℤ^r`, coercivity
of positive-definite forms, and `summable_exp_neg_quadForm` — placed
*before* `QuadraticAction` so that summability of the Boltzmann weight
is **derived** from positive-definiteness, never stored. Coercivity
and `summable_exp_neg_quadForm` live upstream of
`Meno/SiegelPoisson.lean`, which now consumes them. -/

namespace QuadraticAction

private lemma summable_scalarPartFn_nat (α : ℝ) (hα : 0 < α) :
    Summable (fun i : ℕ => Real.exp (-α * (↑i : ℝ) ^ 2)) := by
  have hle : ∀ i : ℕ, (↑i : ℝ) ≤ (↑i : ℝ) ^ 2 := by
    intro i; rcases i with _ | i
    · simp
    · nlinarith [sq_nonneg ((↑(i + 1) : ℝ) - 1),
        show (1 : ℝ) ≤ ↑(i + 1) from by exact_mod_cast Nat.succ_pos i]
  exact (Real.summable_exp_nat_mul_of_ge (neg_neg_of_pos hα)
    (f := fun i => (↑i : ℝ) ^ 2) hle).congr fun i => by congr 1

theorem summable_scalarPartFn (α : ℝ) (hα : 0 < α) :
    Summable (fun k : ℤ => Real.exp (-α * (k : ℝ) ^ 2)) :=
  .of_nat_of_neg (summable_scalarPartFn_nat α hα)
    ((summable_scalarPartFn_nat α hα).congr fun i => by push_cast; congr 1; ring)

/-- Summability of a product of independent non-negative summable
factors over `Fin r → ℤ`: the summability half of Fubini for counting
measure on `ℤ^r`. -/
theorem summable_finPi_prod (r : ℕ) (f : Fin r → ℤ → ℝ)
    (hf_nn : ∀ i z, 0 ≤ f i z)
    (hf_sum : ∀ i, Summable (f i)) :
    Summable (fun k : Fin r → ℤ => ∏ i, f i (k i)) := by
  induction r with
  | zero =>
    exact (hasSum_single default fun b hb =>
      absurd (Subsingleton.elim b default) hb).summable
  | succ n ih =>
    let e := Fin.succFunEquiv ℤ n
    set F : (Fin n → ℤ) → ℝ := fun q => ∏ i : Fin n, f (Fin.castSucc i) (q i)
    set G : ℤ → ℝ := f (Fin.last n)
    have hF_nn : ∀ q, 0 ≤ F q := fun q =>
      Finset.prod_nonneg (fun i _ => hf_nn (Fin.castSucc i) (q i))
    have hG_nn : ∀ z, 0 ≤ G z := hf_nn (Fin.last n)
    have hF_sum : Summable F :=
      ih (fun i => f (Fin.castSucc i))
        (fun i z => hf_nn (Fin.castSucc i) z)
        (fun i => hf_sum (Fin.castSucc i))
    have hG_sum : Summable G := hf_sum (Fin.last n)
    have hFG : Summable (fun p : (Fin n → ℤ) × ℤ => F p.1 * G p.2) :=
      summable_mul_of_summable_norm
        (hF_sum.congr fun q => (Real.norm_eq_abs (F q) ▸ abs_of_nonneg (hF_nn q)).symm)
        (hG_sum.congr fun z => (Real.norm_eq_abs (G z) ▸ abs_of_nonneg (hG_nn z)).symm)
    exact (e.summable_iff.mpr hFG).congr fun k =>
      (Fin.prod_univ_castSucc (fun i => f i (k i))).symm

end QuadraticAction

/-- The quadratic form of a matrix is continuous. Public: the Gaussian
family in `Meno/SiegelPoisson.lean` also consumes it. -/
lemma continuous_quadForm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    Continuous (fun x : Fin d → ℝ => x ⬝ᵥ M.mulVec x) := by
  unfold dotProduct Matrix.mulVec
  fun_prop

/-- **Coercivity**: a positive-definite form dominates a positive multiple
of the sum of squares. Eigenvalue-free: minimize on the compact unit
sphere of `∑ xᵢ²`, then scale by homogeneity. -/
theorem _root_.Matrix.PosDef.exists_coercivity {d : ℕ}
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin d → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ M.mulVec x := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- rank 0: both sides are empty sums
    subst hd
    refine ⟨1, one_pos, fun x => ?_⟩
    simp [dotProduct]
  · -- the sphere S = {x | ∑ xᵢ² = 1} is compact and nonempty
    set S : Set (Fin d → ℝ) := {x | ∑ i, x i ^ 2 = 1} with hS
    have hcont_sq : Continuous (fun x : Fin d → ℝ => ∑ i, x i ^ 2) := by fun_prop
    have hclosed : IsClosed S := isClosed_eq hcont_sq continuous_const
    have hbdd : Bornology.IsBounded S := by
      rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨1, fun x hx => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have h1 : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      rw [hx] at h1
      rw [Real.norm_eq_abs]
      nlinarith [abs_nonneg (x i), sq_abs (x i)]
    have hcompact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
    have hne : S.Nonempty := by
      refine ⟨Pi.single ⟨0, hd⟩ 1, ?_⟩
      simp [hS, Pi.single_apply]
    obtain ⟨x₀, hx₀S, hx₀min⟩ :=
      hcompact.exists_isMinOn hne (continuous_quadForm M).continuousOn
    have hx₀ne : x₀ ≠ 0 := by
      intro h0
      rw [hS] at hx₀S
      simp only [Set.mem_setOf_eq, h0, Pi.zero_apply] at hx₀S
      simp at hx₀S
    have hx₀pos : 0 < x₀ ⬝ᵥ M.mulVec x₀ := by
      have h := (posDef_iff_dotProduct_mulVec.mp hM).2 hx₀ne
      have hstar : star x₀ = x₀ := funext fun i => star_trivial _
      rwa [hstar] at h
    refine ⟨x₀ ⬝ᵥ M.mulVec x₀, hx₀pos, fun x => ?_⟩
    rcases eq_or_ne x 0 with hx | hx
    · simp [hx, Matrix.mulVec_zero, dotProduct_zero]
    · -- scale x to the sphere
      have hsum_pos : 0 < ∑ i, x i ^ 2 := by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
        exact Finset.sum_pos' (fun j _ => sq_nonneg (x j))
          ⟨i, Finset.mem_univ i,
            lt_of_le_of_ne (sq_nonneg (x i)) (Ne.symm (pow_ne_zero 2 hi))⟩
      set t : ℝ := Real.sqrt (∑ i, x i ^ 2) with ht
      have ht_pos : 0 < t := Real.sqrt_pos.mpr hsum_pos
      have ht_sq : t ^ 2 = ∑ i, x i ^ 2 := Real.sq_sqrt hsum_pos.le
      have hy : (t⁻¹ • x) ∈ S := by
        rw [hS]
        simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, mul_pow]
        rw [← Finset.mul_sum, ← ht_sq]
        field_simp
      have hval : (t⁻¹ • x) ⬝ᵥ M.mulVec (t⁻¹ • x) = t⁻¹ ^ 2 * (x ⬝ᵥ M.mulVec x) := by
        rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
        simp [smul_eq_mul, sq]
        ring
      have := isMinOn_iff.mp hx₀min _ hy
      rw [hval] at this
      have h2 : (x₀ ⬝ᵥ M.mulVec x₀) * t ^ 2 ≤ x ⬝ᵥ M.mulVec x := by
        have htne : t ≠ 0 := ne_of_gt ht_pos
        calc (x₀ ⬝ᵥ M.mulVec x₀) * t ^ 2
            ≤ (t⁻¹ ^ 2 * (x ⬝ᵥ M.mulVec x)) * t ^ 2 := by
              apply mul_le_mul_of_nonneg_right this (by positivity)
          _ = x ⬝ᵥ M.mulVec x := by field_simp
      calc (x₀ ⬝ᵥ M.mulVec x₀) * (∑ i, x i ^ 2)
          = (x₀ ⬝ᵥ M.mulVec x₀) * t ^ 2 := by rw [ht_sq]
        _ ≤ x ⬝ᵥ M.mulVec x := h2

/-- Positive scalar multiples of positive-definite matrices are positive
definite. Hand-rolled: `Matrix.PosDef.smul` needs `StarOrderedRing ℝ`
synthesis, which fails at this pin. -/
lemma posDef_smul' {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef)
    {c : ℝ} (hc : 0 < c) : (c • A).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · show (c • A)ᴴ = c • A
    rw [Matrix.conjTranspose_smul, star_trivial]
    congr 1
    exact (posDef_iff_dotProduct_mulVec.mp hA).1
  · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_pos hc ((posDef_iff_dotProduct_mulVec.mp hA).2 hx)

/-- Boltzmann weights of a positive-definite quadratic form are summable
over the integer lattice: `exp(-kᵀMk) ≤ ∏ᵢ exp(-c kᵢ²)` by coercivity,
and the right side is summable by the factorization machinery. -/
theorem summable_exp_neg_quadForm {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosDef) :
    Summable (fun k : Fin d → ℤ =>
      Real.exp (-(∑ i, ∑ j, M i j * (k i : ℝ) * (k j : ℝ)))) := by
  obtain ⟨c, hc, hcoer⟩ := hM.exists_coercivity
  have hquad : ∀ k : Fin d → ℤ,
      ∑ i, ∑ j, M i j * (k i : ℝ) * (k j : ℝ)
        = (fun i => (k i : ℝ)) ⬝ᵥ M.mulVec (fun i => (k i : ℝ)) := by
    intro k
    show ∑ i, ∑ j, M i j * (k i : ℝ) * (k j : ℝ)
      = ∑ i, (k i : ℝ) * ∑ j, M i j * (k j : ℝ)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_)
    (QuadraticAction.summable_finPi_prod d (fun _ z => Real.exp (-c * (z : ℝ) ^ 2))
      (fun _ z => (Real.exp_pos _).le)
      (fun _ => QuadraticAction.summable_scalarPartFn c hc))
  calc Real.exp (-(∑ i, ∑ j, M i j * (k i : ℝ) * (k j : ℝ)))
      ≤ Real.exp (-(c * ∑ i, (k i : ℝ) ^ 2)) := by
        apply Real.exp_le_exp.mpr
        rw [neg_le_neg_iff, hquad k]
        exact hcoer _
    _ = ∏ i, Real.exp (-c * (k i : ℝ) ^ 2) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)

/-- Over `ℝ`, a positive-definite matrix is symmetric: hermitian with
trivial star. -/
theorem _root_.Matrix.PosDef.isSymm {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.PosDef) : A.IsSymm := by
  have h : Aᴴ = A := hA.1
  ext i j
  calc Aᵀ i j = A j i := rfl
    _ = star (A j i) := (star_trivial _).symm
    _ = Aᴴ i j := rfl
    _ = A i j := by rw [h]

/-- A quadratic action of rank `r`: a positive-definite Gram form
`Q : Matrix (Fin r) (Fin r) ℝ`. Symmetry (`QuadraticAction.Q_symm`)
and summability of the Boltzmann weight (`QuadraticAction.summable`)
are **derived**, never stored. -/
structure QuadraticAction (r : ℕ) where
  Q : Matrix (Fin r) (Fin r) ℝ
  Q_posDef : Q.PosDef

namespace QuadraticAction

variable {r : ℕ} (A : QuadraticAction r)

/-- **Symmetry is a theorem**: positive-definiteness over
`ℝ` gives it. -/
theorem Q_symm : A.Q.IsSymm := A.Q_posDef.isSymm

/-- **Summability is a theorem**: the Boltzmann
weight of a quadratic action is summable, by coercivity of its
positive-definite Gram form. -/
theorem summable : Summable (fun k : Fin r → ℤ =>
    Real.exp (-(∑ i, ∑ j, A.Q i j * (k i : ℝ) * (k j : ℝ)))) :=
  summable_exp_neg_quadForm A.Q_posDef

/-- Energy at a sector: `E_Q(k) = ∑_{i,j} Q_ij · k_i · k_j`. -/
noncomputable def energy (k : Fin r → ℤ) : ℝ :=
  ∑ i, ∑ j, A.Q i j * (k i : ℝ) * (k j : ℝ)

theorem energy_zero : A.energy (0 : Fin r → ℤ) = 0 := by
  simp [energy]

/-- Quadratic energy as `xᵀ Q x` for the embedded real vector. -/
theorem energy_eq_dotProduct_mulVec (k : Fin r → ℤ) :
    A.energy k = (fun i => (k i : ℝ)) ⬝ᵥ A.Q.mulVec (fun i => (k i : ℝ)) := by
  show ∑ i, ∑ j, A.Q i j * (k i : ℝ) * (k j : ℝ)
    = ∑ i, (k i : ℝ) * ∑ j, A.Q i j * (k j : ℝ)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- Quadratic energy is non-negative. -/
theorem energy_nonneg (k : Fin r → ℤ) : 0 ≤ A.energy k := by
  rw [A.energy_eq_dotProduct_mulVec]
  have hStar : (star (fun i : Fin r => (k i : ℝ))) = fun i => (k i : ℝ) := by
    funext i; exact star_trivial _
  have h := A.Q_posDef.posSemidef.dotProduct_mulVec_nonneg (fun i => (k i : ℝ))
  rw [hStar] at h; exact h

/-- The `SectorAction` packaging of a `QuadraticAction`. -/
noncomputable def toSectorAction : SectorAction.{0} where
  Λ := Fin r → ℤ
  E := A.energy
  E_zero := ⟨0, A.energy_zero⟩
  E_nonneg := A.energy_nonneg
  summable := A.summable

theorem partFn_eq : A.toSectorAction.partFn =
    ∑' k : Fin r → ℤ,
      Real.exp (-(∑ i, ∑ j, A.Q i j * (k i : ℝ) * (k j : ℝ))) := rfl

/-- Two quadratic actions with the same Gram matrix have the same
partition function. The energy depends only on `Q`, so the Boltzmann
sums coincide pointwise. -/
theorem partFn_eq_of_Q_eq {r : ℕ} (A B : QuadraticAction r) (hQ : A.Q = B.Q) :
    A.toSectorAction.partFn = B.toSectorAction.partFn := by
  rw [A.partFn_eq, B.partFn_eq, hQ]

/-! ## Scalar quadratic action (rank 1) -/

/-- Scalar partition function `Z(α) = ∑' k : ℤ, exp(-α k²)`. -/
noncomputable def scalarPartFn (α : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp (-α * (k : ℝ) ^ 2)

/-- Scalar quadratic action at coupling `α > 0`: rank 1 with `Q = !![α]`. -/
noncomputable def ofScalar (α : ℝ) (hα : 0 < α) : QuadraticAction 1 where
  Q := !![α]
  Q_posDef := by
    refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
    · ext i j; fin_cases i; fin_cases j; rfl
    · intro x hx
      have hx0 : x 0 ≠ 0 := by
        intro h0; apply hx; ext i; fin_cases i; exact h0
      have hcomp : star x ⬝ᵥ !![α].mulVec x = α * (x 0)^2 := by
        simp [dotProduct, mulVec, Matrix.cons_val_fin_one, Pi.star_apply]
        ring
      rw [hcomp]
      have hsq : 0 < (x 0)^2 := by positivity
      exact mul_pos hα hsq

/-- Partition function of the scalar quadratic action equals
`scalarPartFn α`. -/
theorem ofScalar_partFn_eq (α : ℝ) (hα : 0 < α) :
    (ofScalar α hα).toSectorAction.partFn = scalarPartFn α := by
  show ∑' k : Fin 1 → ℤ, Real.exp (-(ofScalar α hα).energy k)
    = ∑' k : ℤ, Real.exp (-α * (k : ℝ) ^ 2)
  have henergy : ∀ k : Fin 1 → ℤ, (ofScalar α hα).energy k = α * (k 0 : ℝ)^2 := by
    intro k
    show ∑ i : Fin 1, ∑ j : Fin 1,
        (ofScalar α hα).Q i j * (k i : ℝ) * (k j : ℝ) = α * (k 0 : ℝ)^2
    show ∑ i : Fin 1, ∑ j : Fin 1, !![α] i j * (k i : ℝ) * (k j : ℝ) = α * (k 0 : ℝ)^2
    simp [Matrix.cons_val_fin_one]
    ring
  have hrewrite : (fun k : Fin 1 → ℤ => Real.exp (-(ofScalar α hα).energy k))
      = (fun k : Fin 1 → ℤ => Real.exp (-α * (k 0 : ℝ)^2)) := by
    funext k; rw [henergy k]; ring_nf
  rw [hrewrite]
  let e : (Fin 1 → ℤ) ≃ ℤ := Equiv.funUnique (Fin 1) ℤ
  exact e.tsum_eq (fun n : ℤ => Real.exp (-α * (n : ℝ) ^ 2))

/-! ## Scalar T-duality, relocated from `Duality.lean` -/

/-- The upper-half-plane parameter of the scalar action at coupling `α`:
`τ(α) = iα/π`. Public because it is the canonical dictionary entry
between coupling and modular parameter: `Z(α) = ϑ₃(τ(α))`. -/
noncomputable def quadTau (α : ℝ) : ℂ :=
  Complex.I * ↑α / ↑Real.pi

private lemma quad_tau_im_pos (α : ℝ) (hα : 0 < α) : (quadTau α).im > 0 := by
  unfold quadTau
  rw [mul_div_assoc, ← Complex.ofReal_div, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  simp only [zero_mul, one_mul, zero_add]
  exact div_pos hα Real.pi_pos

private noncomputable def quadUHP (α : ℝ) (hα : 0 < α) : UpperHalfPlane :=
  ⟨quadTau α, quad_tau_im_pos α hα⟩

private lemma quad_theta_exponent (α : ℝ) (k : ℤ) :
    ↑Real.pi * Complex.I * (↑k : ℂ) ^ 2 * quadTau α =
    ↑(-α * (k : ℝ) ^ 2) := by
  simp only [quadTau]
  have hpi : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  push_cast; field_simp; rw [Complex.I_sq]; ring

/-- **Theta identification**: the scalar partition function *is* the
Jacobi theta function at `τ = iα/π`. The single analytic source for
every duality statement downstream. -/
theorem scalarPartFn_eq_jacobiTheta (α : ℝ) :
    (↑(scalarPartFn α) : ℂ) = jacobiTheta (quadTau α) := by
  simp only [scalarPartFn, jacobiTheta]
  rw [Complex.ofReal_tsum]
  congr 1; ext k
  rw [quad_theta_exponent α k, ← Complex.ofReal_exp]

private theorem quad_S_transform (α : ℝ) (hα : 0 < α) :
    (↑(ModularGroup.S • quadUHP α hα) : ℂ) = quadTau (Real.pi ^ 2 / α) := by
  have h : (↑(quadUHP α hα) : ℂ) = quadTau α := rfl
  rw [modular_S_smul, coe_mk, h]
  simp only [quadTau]
  have hpi : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  have hα0 : (↑α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hα)
  push_cast; field_simp; exact Complex.I_sq.symm

private theorem quad_prefactor (α : ℝ) (hα : 0 < α) :
    -Complex.I * (↑(quadUHP α hα) : ℂ) = ↑(α / Real.pi : ℝ) := by
  have : (↑(quadUHP α hα) : ℂ) = quadTau α := rfl
  rw [this]; simp only [quadTau]
  have hpi : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  push_cast; field_simp; rw [Complex.I_sq]; ring

/-- **Scalar Siegel–Poisson duality** at the partition-function level:
`Z(π²/α) = √(α/π) · Z(α)`. The classical T-duality (radius inversion). -/
theorem scalarPartFn_duality (α : ℝ) (hα : 0 < α) :
    (↑(scalarPartFn (Real.pi ^ 2 / α)) : ℂ) =
    ↑(α / Real.pi : ℝ) ^ ((1 : ℂ) / 2) * ↑(scalarPartFn α) := by
  have hτ : (↑(quadUHP α hα) : ℂ) = quadTau α := rfl
  rw [scalarPartFn_eq_jacobiTheta, scalarPartFn_eq_jacobiTheta,
      show quadTau (Real.pi ^ 2 / α) = ↑(ModularGroup.S • quadUHP α hα) from
        (quad_S_transform α hα).symm,
      jacobiTheta_S_smul, quad_prefactor α hα, hτ]

/-- The scalar partition function strictly exceeds 1: the vacuum sector
contributes 1, and the `k = 1` sector contributes `exp(-α) > 0`. -/
theorem scalarPartFn_gt_one (α : ℝ) (hα : 0 < α) : 1 < scalarPartFn α := by
  have hsm := summable_scalarPartFn α hα
  have hle : ({0, 1} : Finset ℤ).sum (fun k => Real.exp (-α * (k : ℝ) ^ 2)) ≤
      scalarPartFn α := by
    show _ ≤ ∑' k, _
    exact hsm.sum_le_tsum {0, 1} (fun k _ => le_of_lt (Real.exp_pos _))
  simp at hle
  linarith [Real.exp_pos (-α)]

/-- Shifted-mode summability: the positive modes of the scalar theta
sum converge. -/
theorem summable_exp_sq_shift (α : ℝ) (hα : 0 < α) :
    Summable (fun k : ℕ => Real.exp (-α * ((k : ℝ) + 1) ^ 2)) := by
  have h := (summable_nat_add_iff 1).mpr (summable_scalarPartFn_nat α hα)
  exact h.congr fun k => by push_cast; rfl

/-- Symmetric split: the partition function minus its vacuum term
equals twice the sum over positive modes. The ℤ-sum over `k²`
collapses to the ℕ-sum over `(k+1)²` doubled (by evenness) plus the
`k = 0` term. -/
theorem scalarPartFn_sub_one_eq (α : ℝ) (hα : 0 < α) :
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

/-- Per-mode geometric domination:
`exp(−α(k+1)²) ≤ exp(−α)·exp(−α)^k`. -/
theorem exp_sq_shift_le_geo (α : ℝ) (hα : 0 < α) (k : ℕ) :
    Real.exp (-α * ((k : ℝ) + 1) ^ 2) ≤ Real.exp (-α) * Real.exp (-α) ^ k := by
  rw [show Real.exp (-α) * Real.exp (-α) ^ k
      = Real.exp (-α * ((k : ℝ) + 1)) from by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    ring_nf]
  refine Real.exp_le_exp.mpr ?_
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) + 1) hk]

/-- First-mode lower bound: `1 + 2·exp(−α) ≤ Z(α)`. -/
theorem scalarPartFn_ge (α : ℝ) (hα : 0 < α) :
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

/-- Geometric tail upper bound:
`Z(α) ≤ 1 + 2·exp(−α)/(1−exp(−α))`. -/
theorem scalarPartFn_le (α : ℝ) (hα : 0 < α) :
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

/-- Real form of the scalar duality: `Z(π²/α) = (α/π)^(1/2) · Z(α)` with
the real `rpow`. -/
theorem scalarPartFn_duality_real (α : ℝ) (hα : 0 < α) :
    scalarPartFn (Real.pi ^ 2 / α) =
    (α / Real.pi) ^ ((1 : ℝ) / 2) * scalarPartFn α := by
  have h := scalarPartFn_duality α hα
  have hnn : (0 : ℝ) ≤ α / Real.pi := le_of_lt (div_pos hα Real.pi_pos)
  apply Complex.ofReal_inj.mp
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hnn]
  convert h using 2
  push_cast; ring

/-! ## Diagonal rank-2 action and diagonal Siegel–Poisson duality

For diagonal Gram forms the lattice sum factors, so the matrix duality
`Z(π²·Q⁻¹) = √(det Q / π²) · Z(Q)` follows from two applications of the
scalar duality — **no multidimensional Poisson summation needed**. This
realizes the rank-2 matrix Siegel–Poisson target for diagonal `Q`. The
general (non-diagonal) case is proved in `Meno/SiegelPoisson.lean` via
multidimensional Poisson summation; the diagonal route here
survives as the elementary corroborating derivation. -/

/-- Diagonal rank-2 quadratic action: `Q = diag(α, β)` with `α, β > 0`. -/
noncomputable def ofDiagonal₂ (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    QuadraticAction 2 where
  Q := !![α, 0; 0, β]
  Q_posDef := by
    refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> rfl
    · intro x hx
      have hcomp : star x ⬝ᵥ !![α, 0; 0, β].mulVec x
          = α * (x 0) ^ 2 + β * (x 1) ^ 2 := by
        simp [dotProduct, mulVec, Fin.sum_univ_two, Pi.star_apply]
        ring
      rw [hcomp]
      have h01 : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
        by_contra h
        push_neg at h
        apply hx
        ext i
        fin_cases i
        · exact h.1
        · exact h.2
      rcases h01 with h0 | h1
      · have hpos : 0 < α * (x 0) ^ 2 := mul_pos hα (by positivity)
        nlinarith [mul_nonneg hβ.le (sq_nonneg (x 1))]
      · have hpos : 0 < β * (x 1) ^ 2 := mul_pos hβ (by positivity)
        nlinarith [mul_nonneg hα.le (sq_nonneg (x 0))]

@[simp] theorem ofDiagonal₂_Q (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (ofDiagonal₂ α β hα hβ).Q = !![α, 0; 0, β] := rfl


/-! ## The diagonal constructor

`ofDiagonal` builds the rank-`r` action with Gram `diag(α)`. It is
consumed as the rank-2 witness that the duality flow can vanish off
the self-dual locus (`exists_dualityFlow_eq_zero_not_selfDual`). -/


/-- Rank-r diagonal quadratic action: `Q = Matrix.diagonal α` with all
entries positive. -/
noncomputable def ofDiagonal {r : ℕ} (α : Fin r → ℝ) (hα : ∀ i, 0 < α i) :
    QuadraticAction r where
  Q := Matrix.diagonal α
  Q_posDef := by
    refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
    · show (Matrix.diagonal α)ᴴ = Matrix.diagonal α
      rw [Matrix.diagonal_conjTranspose]
      congr 1
    · intro x hx
      have hcomp : star x ⬝ᵥ (Matrix.diagonal α).mulVec x
          = ∑ i, α i * (x i) ^ 2 := by
        unfold dotProduct
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mulVec_diagonal, Pi.star_apply, star_trivial]
        ring
      rw [hcomp]
      obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
      have hi₀' : x i₀ ≠ 0 := hi₀
      refine Finset.sum_pos' (fun i _ => mul_nonneg (hα i).le (sq_nonneg _))
        ⟨i₀, Finset.mem_univ _, mul_pos (hα i₀) (by positivity)⟩

@[simp] theorem ofDiagonal_Q {r : ℕ} (α : Fin r → ℝ) (hα : ∀ i, 0 < α i) :
    (ofDiagonal α hα).Q = Matrix.diagonal α := rfl


/-- Determinant of the diagonal Gram form: `∏ αᵢ`. -/
theorem ofDiagonal_det {r : ℕ} (α : Fin r → ℝ) (hα : ∀ i, 0 < α i) :
    (ofDiagonal α hα).Q.det = ∏ i, α i := by
  rw [ofDiagonal_Q]; exact Matrix.det_diagonal


/-- Half-power of a product of non-negative reals, complex `cpow` form:
`∏ᵢ (fᵢ)^(1/2) = (∏ᵢ fᵢ)^(1/2)`. Public: also used by the
Siegel–Poisson spine (`Meno/SiegelPoisson.lean`). -/
lemma prod_cpow_half : ∀ (r : ℕ) (f : Fin r → ℝ), (∀ i, 0 ≤ f i) →
    ∏ i, (↑(f i) : ℂ) ^ ((1 : ℂ) / 2) = (↑(∏ i, f i) : ℂ) ^ ((1 : ℂ) / 2)
  | 0, f, _ => by simp
  | (n + 1), f, hf => by
    rw [Fin.prod_univ_castSucc (f := fun i => (↑(f i) : ℂ) ^ ((1 : ℂ) / 2)),
        Fin.prod_univ_castSucc (f := f),
        prod_cpow_half n (fun i => f (Fin.castSucc i)) (fun i => hf _),
        Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg
          (Finset.prod_nonneg fun i _ => hf _) (hf _)]


end QuadraticAction

end Meno
