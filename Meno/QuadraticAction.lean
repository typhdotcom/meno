import Meno.SectorAction
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-! # Quadratic Action and Scalar Siegel–Poisson Duality

A `QuadraticAction r` is the analytic primitive whose sector lattice is
`Fin r → ℤ` and whose energy is `kᵀ Q k` for a symmetric positive-definite
Gram matrix `Q`. Summability of the Boltzmann weight is carried as a field
(mirroring `GroupoidObj`); it follows from `Q.PosDef` via the eigenvalue
lower bound, but we defer that derivation.

The rank-1 case `ofScalar α hα` builds `QuadraticAction 1` with `Q = !![α]`;
its partition function equals `∑' k : ℤ, exp(-α k²)`. The scalar
**T-duality** `Z(π²/α) = √(α/π) · Z(α)` is relocated here from
`Duality.lean`. Its proof goes through `jacobiTheta` and the modular
`S`-transformation.

The general matrix Siegel–Poisson duality
`Z(π²·Q⁻¹) = √(det Q / π^r) · Z(Q)` is stated as a target but not proved
in this layer: multidimensional Poisson summation over an integer lattice
in `EuclideanSpace ℝ (Fin r)` is not yet in Mathlib. -/

namespace Meno

open scoped BigOperators
open UpperHalfPlane Complex Matrix

universe u

/-- A quadratic action of rank `r`: a symmetric positive-definite Gram
form `Q : Matrix (Fin r) (Fin r) ℝ` together with summability of the
Boltzmann weight `exp(-kᵀ Q k)` on the integer lattice `Fin r → ℤ`.

`Q_symm` is redundant over ℝ (`Q_posDef.isHermitian` already gives
symmetry) but we keep it as natural data. -/
structure QuadraticAction (r : ℕ) where
  Q : Matrix (Fin r) (Fin r) ℝ
  Q_symm : Q.IsSymm
  Q_posDef : Q.PosDef
  summable : Summable (fun k : Fin r → ℤ =>
    Real.exp (-(∑ i, ∑ j, Q i j * (k i : ℝ) * (k j : ℝ))))

namespace QuadraticAction

variable {r : ℕ} (A : QuadraticAction r)

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

/-! ## Scalar quadratic action (rank 1) -/

/-- Scalar partition function `Z(α) = ∑' k : ℤ, exp(-α k²)`. -/
noncomputable def scalarPartFn (α : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp (-α * (k : ℝ) ^ 2)

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
  summable := by
    have hsumZ := summable_scalarPartFn α hα
    -- Need: Summable (fun k : Fin 1 → ℤ => exp (-(∑ i, ∑ j, !![α] i j * (k i) * (k j))))
    -- That energy = α * (k 0)²
    have heq : ∀ k : Fin 1 → ℤ,
        Real.exp (-(∑ i : Fin 1, ∑ j : Fin 1, !![α] i j * (k i : ℝ) * (k j : ℝ)))
        = Real.exp (-α * (k 0 : ℝ) ^ 2) := by
      intro k
      congr 1
      simp [Matrix.cons_val_fin_one]
      ring
    let e : (Fin 1 → ℤ) ≃ ℤ := Equiv.funUnique (Fin 1) ℤ
    refine Summable.congr (e.summable_iff.mpr hsumZ) ?_
    intro k; rw [heq k]
    show Real.exp (-α * (e k : ℝ) ^ 2) = Real.exp (-α * (k 0 : ℝ) ^ 2)
    rfl

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

private noncomputable def quadTau (α : ℝ) : ℂ :=
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

private theorem scalarPartFn_eq_jacobiTheta (α : ℝ) :
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

end QuadraticAction

end Meno
