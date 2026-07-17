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
(`QuadraticAction.summable`), not a stored field (review #5, retiring
the Session-1 deferral recorded at PLAN Goal 2).

The rank-1 case `ofScalar α hα` builds `QuadraticAction 1` with `Q = !![α]`;
its partition function equals `∑' k : ℤ, exp(-α k²)`. The scalar
**T-duality** `Z(π²/α) = √(α/π) · Z(α)` is relocated here from
`Duality.lean`. Its proof goes through `jacobiTheta` and the modular
`S`-transformation.

The general matrix Siegel–Poisson duality
`Z(π²·Q⁻¹) = √(det Q / π^r) · Z(Q)` is proved at full generality in
`Meno/SiegelPoisson.lean` (multidimensional Poisson summation over the
integer lattice, Phase 15); the diagonal cases below are its elementary
corroborating derivations. -/

namespace Meno

open scoped BigOperators
open UpperHalfPlane Complex Matrix

universe u

/-! ## The summability engine, upstream of the structure

Scalar Gaussian sums, the product factorization over `ℤ^r`, coercivity
of positive-definite forms, and `summable_exp_neg_quadForm` — placed
*before* `QuadraticAction` so that summability of the Boltzmann weight
is **derived** from positive-definiteness, never stored (review #5;
PLAN Goal 2). Coercivity and `summable_exp_neg_quadForm` are relocated
upstream from `Meno/SiegelPoisson.lean` (Phase 15), which now consumes
them. -/

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

/-- A quadratic action of rank `r`: a symmetric positive-definite Gram
form `Q : Matrix (Fin r) (Fin r) ℝ`. Summability of the Boltzmann
weight `exp(-kᵀ Q k)` on `Fin r → ℤ` is **derived**
(`QuadraticAction.summable`), never stored (review #5).

`Q_symm` is redundant over ℝ (`Q_posDef.isHermitian` already gives
symmetry) but we keep it as natural data. -/
structure QuadraticAction (r : ℕ) where
  Q : Matrix (Fin r) (Fin r) ℝ
  Q_symm : Q.IsSymm
  Q_posDef : Q.PosDef

namespace QuadraticAction

variable {r : ℕ} (A : QuadraticAction r)

/-- **Summability is a theorem** (PLAN Goal 2, closed): the Boltzmann
weight of a quadratic action is summable, by coercivity of its
positive-definite Gram form. Same name and statement as the retired
field, so consumers are unchanged. -/
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
  Q_symm := by
    ext i j; fin_cases i; fin_cases j; rfl
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
multidimensional Poisson summation (Phase 15); the diagonal route here
survives as the elementary corroborating derivation. -/

/-- Diagonal rank-2 quadratic action: `Q = diag(α, β)` with `α, β > 0`. -/
noncomputable def ofDiagonal₂ (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    QuadraticAction 2 where
  Q := !![α, 0; 0, β]
  Q_symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
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

/-- Hand-rolled pairing equivalence `(Fin 2 → ℤ) ≃ ℤ × ℤ` with a
one-β-step `toFun`. `piFinTwoEquiv`'s coercion is expensive to unfold
inside `tsum` unification; this one is not. -/
private def finTwoPair : (Fin 2 → ℤ) ≃ ℤ × ℤ where
  toFun k := (k 0, k 1)
  invFun p := ![p.1, p.2]
  left_inv k := by funext i; fin_cases i <;> rfl
  right_inv p := rfl

/-- **Partition function factorization** for the diagonal rank-2 action:
`Z(diag(α,β)) = Z(α) · Z(β)`. The lattice `ℤ²` decouples mode by mode. -/
theorem ofDiagonal₂_partFn (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (ofDiagonal₂ α β hα hβ).toSectorAction.partFn
    = scalarPartFn α * scalarPartFn β := by
  rw [(ofDiagonal₂ α β hα hβ).partFn_eq]
  simp_rw [ofDiagonal₂_Q]
  have hsplit : ∀ k : Fin 2 → ℤ,
      Real.exp (-(∑ i, ∑ j, (!![α, 0; 0, β] : Matrix (Fin 2) (Fin 2) ℝ) i j
          * (k i : ℝ) * (k j : ℝ)))
      = Real.exp (-α * (k 0 : ℝ) ^ 2) * Real.exp (-β * (k 1 : ℝ) ^ 2) := by
    intro k
    rw [← Real.exp_add]
    congr 1
    simp [Fin.sum_univ_two]
    ring
  have hfact := tsum_mul_tsum_of_summable_norm
    (f := fun m : ℤ => Real.exp (-α * (m : ℝ) ^ 2))
    (g := fun l : ℤ => Real.exp (-β * (l : ℝ) ^ 2))
    (summable_norm_iff.mpr (summable_scalarPartFn α hα))
    (summable_norm_iff.mpr (summable_scalarPartFn β hβ))
  calc ∑' k : Fin 2 → ℤ, Real.exp
        (-(∑ i, ∑ j, (!![α, 0; 0, β] : Matrix (Fin 2) (Fin 2) ℝ) i j
            * (k i : ℝ) * (k j : ℝ)))
      = ∑' k : Fin 2 → ℤ,
          Real.exp (-α * (k 0 : ℝ) ^ 2) * Real.exp (-β * (k 1 : ℝ) ^ 2) :=
        tsum_congr hsplit
    _ = ∑' p : ℤ × ℤ, Real.exp (-α * (p.1 : ℝ) ^ 2) * Real.exp (-β * (p.2 : ℝ) ^ 2) :=
        finTwoPair.tsum_eq (fun p : ℤ × ℤ =>
          Real.exp (-α * (p.1 : ℝ) ^ 2) * Real.exp (-β * (p.2 : ℝ) ^ 2))
    _ = scalarPartFn α * scalarPartFn β := hfact.symm

/-- Determinant of the diagonal Gram form: `det diag(α,β) = αβ`. -/
theorem ofDiagonal₂_det (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (ofDiagonal₂ α β hα hβ).Q.det = α * β := by
  show (!![α, 0; 0, β] : Matrix (Fin 2) (Fin 2) ℝ).det = α * β
  rw [Matrix.det_fin_two]
  simp

/-- The dual coupling matrix is exactly `π² · Q⁻¹`: the diagonal case of
the Siegel–Poisson dual Gram form. -/
theorem ofDiagonal₂_dual_Q (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (ofDiagonal₂ (Real.pi ^ 2 / α) (Real.pi ^ 2 / β)
        (div_pos (sq_pos_of_pos Real.pi_pos) hα)
        (div_pos (sq_pos_of_pos Real.pi_pos) hβ)).Q
    = Real.pi ^ 2 • (ofDiagonal₂ α β hα hβ).Q⁻¹ := by
  show (!![Real.pi ^ 2 / α, 0; 0, Real.pi ^ 2 / β] : Matrix (Fin 2) (Fin 2) ℝ)
    = Real.pi ^ 2 • (!![α, 0; 0, β] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
  have hinv : (!![α, 0; 0, β] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = !![α⁻¹, 0; 0, β⁻¹] := by
    apply Matrix.inv_eq_right_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two,
        mul_inv_cancel₀ (ne_of_gt hα), mul_inv_cancel₀ (ne_of_gt hβ)]
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [div_eq_mul_inv]

/-- **Diagonal Siegel–Poisson duality (rank 2)**:
`Z(π²·Q⁻¹) = √(det Q / π²) · Z(Q)` for `Q = diag(α, β)` — proved by two
scalar S-transformations and prefactor multiplication. The first matrix
duality in the spine, no multidimensional Poisson summation required. -/
theorem ofDiagonal₂_duality (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (↑((ofDiagonal₂ (Real.pi ^ 2 / α) (Real.pi ^ 2 / β)
        (div_pos (sq_pos_of_pos Real.pi_pos) hα)
        (div_pos (sq_pos_of_pos Real.pi_pos) hβ)).toSectorAction.partFn) : ℂ)
    = ↑(α * β / Real.pi ^ 2 : ℝ) ^ ((1 : ℂ) / 2)
      * ↑((ofDiagonal₂ α β hα hβ).toSectorAction.partFn) := by
  rw [ofDiagonal₂_partFn, ofDiagonal₂_partFn,
      Complex.ofReal_mul, Complex.ofReal_mul,
      scalarPartFn_duality α hα, scalarPartFn_duality β hβ]
  have hA : (0 : ℝ) ≤ α / Real.pi := (div_pos hα Real.pi_pos).le
  have hB : (0 : ℝ) ≤ β / Real.pi := (div_pos hβ Real.pi_pos).le
  have hmul : (↑(α / Real.pi : ℝ) : ℂ) ^ ((1 : ℂ) / 2)
        * (↑(β / Real.pi : ℝ) : ℂ) ^ ((1 : ℂ) / 2)
      = (↑(α * β / Real.pi ^ 2 : ℝ) : ℂ) ^ ((1 : ℂ) / 2) := by
    rw [← Complex.mul_cpow_ofReal_nonneg hA hB, ← Complex.ofReal_mul]
    congr 2
    field_simp
  rw [← hmul]
  ring

/-- The duality in determinant form: the prefactor is `√(det Q / π²)`. -/
theorem ofDiagonal₂_duality_det_form (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (↑((ofDiagonal₂ (Real.pi ^ 2 / α) (Real.pi ^ 2 / β)
        (div_pos (sq_pos_of_pos Real.pi_pos) hα)
        (div_pos (sq_pos_of_pos Real.pi_pos) hβ)).toSectorAction.partFn) : ℂ)
    = ↑((ofDiagonal₂ α β hα hβ).Q.det / Real.pi ^ 2 : ℝ) ^ ((1 : ℂ) / 2)
      * ↑((ofDiagonal₂ α β hα hβ).toSectorAction.partFn) := by
  rw [ofDiagonal₂_det]
  exact ofDiagonal₂_duality α β hα hβ

/-! ## Rank-r diagonal action and rank-r diagonal Siegel–Poisson duality

The general diagonal case. The lattice `ℤ^r` decouples coordinate by
coordinate (Fubini for counting measure, `tsum_finPi_factor`), each mode
obeys the scalar duality, and the prefactors multiply into
`√(det Q / π^r)`. This closes the matrix Siegel–Poisson target for
**all diagonal Gram forms at every rank** by elementary factoring; the
non-diagonal case is proved at full generality in
`Meno/SiegelPoisson.lean` (Phase 15, multidimensional Poisson
summation) and consumed by the theta graph's rank-2 non-diagonal Gram
form (`Meno/ThetaHarmonic.lean`).

`summable_finPi_prod`, `tsum_finPi_factor`, `diag_quadForm_eq` were
relocated upstream from `Hodge.lean` (where they were private); they are
pure analysis and belong to the spine. -/

/-- Diagonal quadratic form simplification: off-diagonal terms vanish,
leaving a sum of independent squared terms. -/
theorem diag_quadForm_eq (r : ℕ) (α : Fin r → ℝ)
    (Q : Fin r → Fin r → ℝ)
    (hQ_diag : ∀ i, Q i i = α i)
    (hQ_off : ∀ i j, i ≠ j → Q i j = 0)
    (k : Fin r → ℤ) :
    ∑ i : Fin r, ∑ j : Fin r, Q i j * (k i : ℝ) * (k j : ℝ) =
    ∑ i : Fin r, α i * (k i : ℝ) ^ 2 := by
  congr 1; ext i
  have h : ∀ j : Fin r, Q i j * (k i : ℝ) * (k j : ℝ) =
      if j = i then α i * (k i : ℝ) ^ 2 else 0 := by
    intro j
    split_ifs with h
    · subst h; rw [hQ_diag]; ring
    · rw [hQ_off i j (fun heq => h heq.symm)]; ring
  simp_rw [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Product factorization of `tsum` over `Fin r → ℤ`: Fubini's theorem
for counting measure on `ℤ^r` with non-negative product summands. -/
theorem tsum_finPi_factor (r : ℕ) (f : Fin r → ℤ → ℝ)
    (hf_nn : ∀ i z, 0 ≤ f i z)
    (hf_sum : ∀ i, Summable (f i)) :
    ∑' k : Fin r → ℤ, ∏ i, f i (k i) = ∏ i : Fin r, ∑' z, f i z := by
  induction r with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact tsum_eq_single default (fun b hb => absurd (Subsingleton.elim b default) hb)
  | succ n ih =>
    let e := Fin.succFunEquiv ℤ n
    have hrw : ∀ k : Fin (n + 1) → ℤ,
        ∏ i, f i (k i) = (∏ i : Fin n, f (Fin.castSucc i) ((e k).1 i)) * f (Fin.last n) (e k).2 := by
      intro k; exact Fin.prod_univ_castSucc (fun i => f i (k i))
    set F : (Fin n → ℤ) → ℝ := fun q => ∏ i : Fin n, f (Fin.castSucc i) (q i)
    set G : ℤ → ℝ := f (Fin.last n)
    have hF_nn : ∀ q, 0 ≤ F q := fun q =>
      Finset.prod_nonneg (fun i _ => hf_nn (Fin.castSucc i) (q i))
    have hG_nn : ∀ z, 0 ≤ G z := hf_nn (Fin.last n)
    have hF_sum : Summable F :=
      summable_finPi_prod n (fun i => f (Fin.castSucc i))
        (fun i z => hf_nn (Fin.castSucc i) z)
        (fun i => hf_sum (Fin.castSucc i))
    have hG_sum : Summable G := hf_sum (Fin.last n)
    have hFG : Summable (fun p : (Fin n → ℤ) × ℤ => F p.1 * G p.2) :=
      summable_mul_of_summable_norm
        (hF_sum.congr fun q => (Real.norm_eq_abs (F q) ▸ abs_of_nonneg (hF_nn q)).symm)
        (hG_sum.congr fun z => (Real.norm_eq_abs (G z) ▸ abs_of_nonneg (hG_nn z)).symm)
    have step1 : ∑' k : Fin (n + 1) → ℤ, ∏ i, f i (k i) =
        ∑' p : (Fin n → ℤ) × ℤ, F p.1 * G p.2 := by
      conv_lhs => arg 1; ext k; rw [hrw k]
      exact e.tsum_eq (fun p => F p.1 * G p.2)
    have step2 : ∑' p : (Fin n → ℤ) × ℤ, F p.1 * G p.2 =
        (∑' q, F q) * (∑' z, G z) :=
      (hF_sum.tsum_mul_tsum hG_sum hFG).symm
    have step3 : ∑' q, F q = ∏ i : Fin n, ∑' z, f (Fin.castSucc i) z :=
      ih (fun i => f (Fin.castSucc i))
        (fun i z => hf_nn (Fin.castSucc i) z)
        (fun i => hf_sum (Fin.castSucc i))
    rw [step1, step2, step3]
    exact (Fin.prod_univ_castSucc (fun i => ∑' z, f i z)).symm

/-- The diagonal Boltzmann weight factors mode by mode. -/
private lemma diag_weight_eq {r : ℕ} (α : Fin r → ℝ) (k : Fin r → ℤ) :
    Real.exp (-(∑ i, ∑ j, Matrix.diagonal α i j * (k i : ℝ) * (k j : ℝ)))
    = ∏ i, Real.exp (-α i * (k i : ℝ) ^ 2) := by
  rw [diag_quadForm_eq r α (Matrix.diagonal α)
        (fun i => Matrix.diagonal_apply_eq α i)
        (fun i j hij => Matrix.diagonal_apply_ne α hij)]
  rw [show -(∑ i : Fin r, α i * (k i : ℝ) ^ 2)
      = ∑ i : Fin r, (-α i * (k i : ℝ) ^ 2) from by
    rw [← Finset.sum_neg_distrib]; congr 1; ext i; ring]
  exact Real.exp_sum Finset.univ _

/-- Rank-r diagonal quadratic action: `Q = Matrix.diagonal α` with all
entries positive. -/
noncomputable def ofDiagonal {r : ℕ} (α : Fin r → ℝ) (hα : ∀ i, 0 < α i) :
    QuadraticAction r where
  Q := Matrix.diagonal α
  Q_symm := Matrix.isSymm_diagonal α
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

/-- **Rank-r partition function factorization**:
`Z(diag(α₁,…,α_r)) = ∏ᵢ Z(αᵢ)`. -/
theorem ofDiagonal_partFn {r : ℕ} (α : Fin r → ℝ) (hα : ∀ i, 0 < α i) :
    (ofDiagonal α hα).toSectorAction.partFn = ∏ i, scalarPartFn (α i) := by
  rw [(ofDiagonal α hα).partFn_eq]
  simp_rw [ofDiagonal_Q]
  calc ∑' k : Fin r → ℤ, Real.exp
        (-(∑ i, ∑ j, Matrix.diagonal α i j * (k i : ℝ) * (k j : ℝ)))
      = ∑' k : Fin r → ℤ, ∏ i, Real.exp (-α i * (k i : ℝ) ^ 2) :=
        tsum_congr (fun k => diag_weight_eq α k)
    _ = ∏ i : Fin r, ∑' z : ℤ, Real.exp (-α i * (z : ℝ) ^ 2) :=
        tsum_finPi_factor r (fun i z => Real.exp (-α i * (z : ℝ) ^ 2))
          (fun i z => le_of_lt (Real.exp_pos _))
          (fun i => summable_scalarPartFn (α i) (hα i))
    _ = ∏ i, scalarPartFn (α i) := rfl

/-- Determinant of the diagonal Gram form: `∏ αᵢ`. -/
theorem ofDiagonal_det {r : ℕ} (α : Fin r → ℝ) (hα : ∀ i, 0 < α i) :
    (ofDiagonal α hα).Q.det = ∏ i, α i := by
  rw [ofDiagonal_Q]; exact Matrix.det_diagonal

/-- The dual coupling matrix is `π² · Q⁻¹` at every rank (diagonal
case): inverse verified by explicit diagonal multiplication. -/
theorem ofDiagonal_dual_Q {r : ℕ} (α : Fin r → ℝ) (hα : ∀ i, 0 < α i) :
    (ofDiagonal (fun i => Real.pi ^ 2 / α i)
        (fun i => div_pos (sq_pos_of_pos Real.pi_pos) (hα i))).Q
    = Real.pi ^ 2 • (ofDiagonal α hα).Q⁻¹ := by
  rw [ofDiagonal_Q, ofDiagonal_Q]
  have hinv : (Matrix.diagonal α)⁻¹ = Matrix.diagonal (fun i => (α i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    have : (fun i => α i * (α i)⁻¹) = fun _ => (1 : ℝ) := by
      funext i; exact mul_inv_cancel₀ (ne_of_gt (hα i))
    rw [this, Matrix.diagonal_one]
  rw [hinv]
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq, div_eq_mul_inv]
  · simp [Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_ne _ h]

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

/-- **Rank-r diagonal Siegel–Poisson duality**:
`Z(π²·Q⁻¹) = √(det Q / π^r) · Z(Q)` for `Q = diag(α₁,…,α_r)`. Proved by
`r` scalar S-transformations; the prefactors multiply into the
determinant form. No multidimensional Poisson summation. -/
theorem ofDiagonal_duality {r : ℕ} (α : Fin r → ℝ) (hα : ∀ i, 0 < α i) :
    (↑((ofDiagonal (fun i => Real.pi ^ 2 / α i)
        (fun i => div_pos (sq_pos_of_pos Real.pi_pos) (hα i))).toSectorAction.partFn) : ℂ)
    = ↑((∏ i, α i) / Real.pi ^ r : ℝ) ^ ((1 : ℂ) / 2)
      * ↑((ofDiagonal α hα).toSectorAction.partFn) := by
  rw [ofDiagonal_partFn, ofDiagonal_partFn, Complex.ofReal_prod, Complex.ofReal_prod]
  calc ∏ i, (↑(scalarPartFn (Real.pi ^ 2 / α i)) : ℂ)
      = ∏ i, ((↑(α i / Real.pi : ℝ) : ℂ) ^ ((1 : ℂ) / 2) * ↑(scalarPartFn (α i))) :=
        Finset.prod_congr rfl (fun i _ => scalarPartFn_duality (α i) (hα i))
    _ = (∏ i, (↑(α i / Real.pi : ℝ) : ℂ) ^ ((1 : ℂ) / 2))
          * ∏ i, (↑(scalarPartFn (α i)) : ℂ) :=
        Finset.prod_mul_distrib
    _ = (↑(∏ i, α i / Real.pi : ℝ) : ℂ) ^ ((1 : ℂ) / 2)
          * ∏ i, (↑(scalarPartFn (α i)) : ℂ) := by
        rw [prod_cpow_half r (fun i => α i / Real.pi)
              (fun i => (div_pos (hα i) Real.pi_pos).le),
            Complex.ofReal_prod]
    _ = ↑((∏ i, α i) / Real.pi ^ r : ℝ) ^ ((1 : ℂ) / 2)
          * ∏ i, (↑(scalarPartFn (α i)) : ℂ) := by
        congr 3
        rw [Finset.prod_div_distrib, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin]

/-- The rank-r duality in determinant form. -/
theorem ofDiagonal_duality_det_form {r : ℕ} (α : Fin r → ℝ) (hα : ∀ i, 0 < α i) :
    (↑((ofDiagonal (fun i => Real.pi ^ 2 / α i)
        (fun i => div_pos (sq_pos_of_pos Real.pi_pos) (hα i))).toSectorAction.partFn) : ℂ)
    = ↑((ofDiagonal α hα).Q.det / Real.pi ^ r : ℝ) ^ ((1 : ℂ) / 2)
      * ↑((ofDiagonal α hα).toSectorAction.partFn) := by
  rw [ofDiagonal_det]
  exact ofDiagonal_duality α hα

/-- The rank-2 hand-built action is the `r = 2` instance of the general
diagonal family: same Gram matrix, hence same partition function. The
dedup witness connecting `ofDiagonal₂` to `ofDiagonal`. -/
theorem ofDiagonal₂_partFn_eq_ofDiagonal (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (ofDiagonal₂ α β hα hβ).toSectorAction.partFn
    = (ofDiagonal ![α, β] (fun i => by fin_cases i <;> assumption)).toSectorAction.partFn := by
  refine partFn_eq_of_Q_eq _ _ ?_
  rw [ofDiagonal_Q]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

end QuadraticAction

end Meno
