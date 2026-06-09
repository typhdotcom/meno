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
general (non-diagonal) case remains gated on multidimensional Poisson
summation over the integer lattice, which Mathlib does not yet have. -/

private lemma summable_diag₂ (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    Summable (fun k : Fin 2 → ℤ =>
      Real.exp (-(∑ i, ∑ j, (!![α, 0; 0, β] : Matrix (Fin 2) (Fin 2) ℝ) i j
        * (k i : ℝ) * (k j : ℝ)))) := by
  have hprod : Summable (fun p : ℤ × ℤ =>
      Real.exp (-α * (p.1 : ℝ) ^ 2) * Real.exp (-β * (p.2 : ℝ) ^ 2)) :=
    (summable_scalarPartFn α hα).mul_of_nonneg (summable_scalarPartFn β hβ)
      (fun _ => le_of_lt (Real.exp_pos _)) (fun _ => le_of_lt (Real.exp_pos _))
  let e : (Fin 2 → ℤ) ≃ ℤ × ℤ := piFinTwoEquiv (fun _ => ℤ)
  refine Summable.congr (e.summable_iff.mpr hprod) ?_
  intro k
  show Real.exp (-α * (k 0 : ℝ) ^ 2) * Real.exp (-β * (k 1 : ℝ) ^ 2) = _
  rw [← Real.exp_add]
  congr 1
  simp [Fin.sum_univ_two]
  ring

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
  summable := summable_diag₂ α β hα hβ

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

end QuadraticAction

end Meno
