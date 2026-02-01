import Meno.Simplicial
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-! # Jacobi Theta Identification and T-Duality -/

namespace Simplicial

open Finset BigOperators UpperHalfPlane

private lemma tau_im_pos (n : ℕ) (hn : n ≥ 3) :
    (Complex.I / (↑Real.pi * (↑n : ℂ))).im > 0 := by
  have h : (↑Real.pi * (↑n : ℂ)) = (↑(Real.pi * ↑n : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.div_ofReal_im, Complex.I_im]
  exact div_pos one_pos (mul_pos Real.pi_pos (by positivity))

private noncomputable def cycleTau (n : ℕ) (_ : n ≥ 3) : ℂ :=
  Complex.I / (↑Real.pi * ↑n)

private lemma theta_exponent_eq (n : ℕ) (hn : n ≥ 3) (k : ℤ) :
    ↑Real.pi * Complex.I * (↑k : ℂ) ^ 2 * (cycleTau n hn) =
    ↑(-(k : ℝ) ^ 2 / (n : ℝ)) := by
  simp only [cycleTau]
  have hpi : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  have hn0 : (↑(n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast; field_simp; rw [Complex.I_sq]; ring

/-- The partition function is the Jacobi theta function at τ = i/(πn). -/
theorem partitionFn_eq_jacobiTheta (n : ℕ) (hn : n ≥ 3) :
    (↑(partitionFn n hn) : ℂ) = jacobiTheta (cycleTau n hn) := by
  simp only [partitionFn, jacobiTheta]
  rw [Complex.ofReal_tsum]
  congr 1; ext k
  rw [theta_exponent_eq n hn k, ← Complex.ofReal_exp]

/-- The upper half plane point τ = i/(πn) at which Z(Cₙ) = ϑ₃(τ). -/
noncomputable def cycleUHP (n : ℕ) (hn : n ≥ 3) : UpperHalfPlane :=
  ⟨cycleTau n hn, tau_im_pos n hn⟩

/-- The dual coupling: S-transforming τ = i/(πn) gives τ' = iπn.
    This is the content the modular transformation computes:
    the partition function at coupling 1/n maps to coupling π²n. -/
theorem cycleTau_S_transform (n : ℕ) (hn : n ≥ 3) :
    (↑(ModularGroup.S • cycleUHP n hn) : ℂ) = Complex.I * ↑Real.pi * ↑n := by
  have : (↑(cycleUHP n hn) : ℂ) = cycleTau n hn := rfl
  rw [modular_S_smul, coe_mk, this, cycleTau]
  have hpi : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  have hn0 : (↑(n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp; rw [Complex.I_sq]

/-- The modular prefactor: −iτ = 1/(πn), a positive real number.
    Under the square root this becomes (1/(πn))^(1/2) = 1/√(πn). -/
theorem cycleTau_prefactor (n : ℕ) (hn : n ≥ 3) :
    -Complex.I * (↑(cycleUHP n hn) : ℂ) = ↑(1 / (Real.pi * ↑n) : ℝ) := by
  have : (↑(cycleUHP n hn) : ℂ) = cycleTau n hn := rfl
  rw [this, cycleTau]
  have hpi : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  have hn0 : (↑(n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast; field_simp; rw [Complex.I_sq]; ring

/-- **T-duality** (explicit form): the modular S-transformation relates
    the partition function Z(Cₙ) at coupling 1/n to the dual theta function
    at coupling π²n. Concretely:
      ϑ₃(iπn) = (1/(πn))^(1/2) · Z(Cₙ)
    The dual theta ϑ₃(iπn) = Σ_k exp(−π²nk²) sums Boltzmann weights at
    coupling π²n. This is the radius-inversion duality R ↔ 1/R. -/
theorem partitionFn_T_duality (n : ℕ) (hn : n ≥ 3) :
    jacobiTheta (Complex.I * ↑Real.pi * ↑n) =
      (↑(1 / (Real.pi * ↑n) : ℝ) : ℂ) ^ ((1 : ℂ) / 2) * ↑(partitionFn n hn) := by
  have hS := jacobiTheta_S_smul (cycleUHP n hn)
  rw [cycleTau_S_transform] at hS
  rw [cycleTau_prefactor] at hS
  rw [show jacobiTheta ↑(cycleUHP n hn) = jacobiTheta (cycleTau n hn) from rfl,
      ← partitionFn_eq_jacobiTheta] at hS
  exact hS

end Simplicial
