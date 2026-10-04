import Meno.ZetaZeroCert

/-! # A graph zeta vanishing past the line of absolute convergence

The theta graph `θ(1,1,2)` — two vertices joined by paths of lengths `1`, `1`, `2` —
has cycle Gram `!![2, −1; −1, 3]`, so its harmonic carrier `H¹` prices a class with
periods `p` at `(3p₀² + 2p₀p₁ + 2p₁²)/5`: the non-principal form of discriminant `−20`,
up to the sign of `p₁`. Its zeta is therefore `Γ(s)·5^s·Z_F(s)` for `Re s > 1`
(`theta112_completedZeta_eq`), and the kernel-checked Davenport–Heilbronn zero of
`Z_F` (`DH.exists_zero`) is a zero of the graph zeta at `Re s ≈ 1.99`, inside the
half-plane where the Dirichlet series converges absolutely
(`theta112_completedZeta_zero`). A graph zeta has no Euler product. -/

namespace Meno

open scoped BigOperators

open Epstein

section Theta112

/-- Edge sources: `e₀, e₁ : 0 → 1`, `e₂ : 0 → 2`, `e₃ : 2 → 1`. -/
def theta112Src : Fin 4 → Fin 3 := ![0, 0, 0, 2]

/-- Edge targets. -/
def theta112Tgt : Fin 4 → Fin 3 := ![1, 1, 2, 1]

/-- The theta graph `θ(1,1,2)`. -/
@[reducible] def theta112 : IncidenceGraph :=
  { V := Fin 3
    E := Fin 4
    src := theta112Src
    tgt := theta112Tgt }

/-- The basis cycles `c₁ = e₀ − e₁` (length `2`) and `c₂ = e₁ − e₂ − e₃` (length `3`). -/
def theta112CyclesZ : Fin 2 → Fin 4 → ℤ := ![![1, -1, 0, 0], ![0, 1, -1, -1]]

theorem theta112_boundary_eq_sum {R : Type*} [CommRing R] (ω : Fin 4 → R) (w : Fin 3) :
    theta112.boundary ω w
      = ∑ e, ((if theta112Tgt e = w then (1 : R) else 0)
        - (if theta112Src e = w then (1 : R) else 0)) * ω e := rfl

theorem theta112CyclesZ_mem (i : Fin 2) : theta112CyclesZ i ∈ theta112.cycleLattice := by
  rw [IncidenceGraph.mem_cycleLattice]
  intro w
  rw [theta112_boundary_eq_sum]
  fin_cases i <;> fin_cases w <;> decide

/-- A closed real cochain is `ω₀·c₁ + (ω₀ + ω₁)·c₂`. -/
theorem theta112_eq_comb (ω : Fin 4 → ℝ) (h : ∀ w, theta112.boundary ω w = 0) :
    ω = fun e => ω 0 * ((theta112CyclesZ 0 e : ℤ) : ℝ)
      + (ω 0 + ω 1) * ((theta112CyclesZ 1 e : ℤ) : ℝ) := by
  have h0 := h 0
  have h2 := h 2
  rw [theta112_boundary_eq_sum] at h0 h2
  simp +decide [theta112Src, theta112Tgt, Fin.sum_univ_four] at h0 h2
  funext e
  fin_cases e <;> simp +decide [theta112CyclesZ] <;> linarith

theorem theta112_cast_independent (x : Fin 2 → ℝ)
    (hx : (fun e => ∑ i, x i * ((theta112CyclesZ i e : ℤ) : ℝ)) = 0) : x = 0 := by
  have h0 := congrFun hx 0
  have h2 := congrFun hx 2
  simp +decide [theta112CyclesZ, Fin.sum_univ_two] at h0 h2
  funext i
  fin_cases i
  · simpa using h0
  · simpa using h2

theorem theta112_integral_spanning (x : Fin 4 → ℤ) (hx : x ∈ theta112.cycleLattice) :
    ∃ a : Fin 2 → ℤ, x = fun e => ∑ i, a i * theta112CyclesZ i e := by
  have hclosed : ∀ w, theta112.boundary (fun e => ((x e : ℤ) : ℝ)) w = 0 := by
    intro w
    rw [theta112.boundary_castR, (IncidenceGraph.mem_cycleLattice _ |>.mp hx) w, Int.cast_zero]
  have hr := theta112_eq_comb (fun e => ((x e : ℤ) : ℝ)) hclosed
  refine ⟨![x 0, x 0 + x 1], ?_⟩
  funext e
  apply Int.cast_injective (α := ℝ)
  rw [congrFun hr e]
  push_cast [Fin.sum_univ_two]
  simp

/-- The lattice basis of `H₁(θ(1,1,2); ℤ)`. -/
noncomputable def theta112Basis : Module.Basis (Fin 2) ℤ theta112.cycleLattice :=
  theta112.basisOfCycles theta112CyclesZ theta112CyclesZ_mem theta112_cast_independent
    theta112_integral_spanning

theorem cyclesZ_theta112Basis : theta112.cyclesZ theta112Basis = theta112CyclesZ :=
  theta112.cyclesZ_basisOfCycles _ _ _ _

theorem theta112_b1 : theta112.b1 = 2 := (theta112.card_eq_b1 theta112Basis).symm

/-- The harmonic Gram: the inverse of the cycle Gram `!![2, −1; −1, 3]`. -/
theorem theta112_gram :
    (theta112.basisGramData theta112Basis).gram = !![3/5, 1/5; 1/5, 2/5] := by
  show (gramOf (theta112.cyclesR theta112Basis))⁻¹ = _
  have hc : theta112.cyclesR theta112Basis = fun i e => ((theta112CyclesZ i e : ℤ) : ℝ) := by
    funext i e
    show ((theta112.cyclesZ theta112Basis i e : ℤ) : ℝ) = _
    rw [cyclesZ_theta112Basis]
  have hg : gramOf (theta112.cyclesR theta112Basis) = !![2, -1; -1, 3] := by
    rw [hc]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp +decide [gramOf, dotProduct, theta112CyclesZ, Fin.sum_univ_four] <;> norm_num
  rw [hg]
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The period chart `H¹ ≃ ℤ²`, with the sign of `p₁` flipped to land on `F`. -/
noncomputable def theta112Chart : (theta112.classQuadAction).Λ ≃ ℤ × ℤ :=
  (theta112.latticeQuotEquiv theta112Basis).toEquiv.trans
    { toFun := fun p => (p 0, -p 1)
      invFun := fun k => ![k.1, -k.2]
      left_inv := fun p => by funext i; fin_cases i <;> simp
      right_inv := fun k => by simp }

/-- **The pricing is the form**: a class's harmonic energy is `F/5` at its chart. -/
theorem theta112_form (κ : (theta112.E → ℤ) ⧸ LinearMap.range (theta112.gradLin ℤ)) :
    (theta112.classQuadAction).form κ κ = (DH.F.q (theta112Chart κ) : ℝ) / 5 := by
  show theta112.classForm κ κ = _
  rw [← theta112.classForm_chart theta112Basis]
  set p := theta112.latticeQuotEquiv theta112Basis κ
  have hq : (DH.F.q (theta112Chart κ) : ℤ) = 3 * p 0 ^ 2 + 2 * p 0 * p 1 + 2 * p 1 ^ 2 := by
    rw [DH.q_cast]
    show 3 * p 0 ^ 2 - 2 * p 0 * -p 1 + 2 * (-p 1) ^ 2 = _
    ring
  have hqR : (DH.F.q (theta112Chart κ) : ℝ) = 3 * (p 0 : ℝ) ^ 2 + 2 * p 0 * p 1 + 2 * p 1 ^ 2 := by
    exact_mod_cast hq
  rw [hqR]
  show ∑ i, ∑ j, (theta112.basisGramData theta112Basis).gram i j * (p i : ℝ) * (p j : ℝ) = _
  rw [theta112_gram]
  show ∑ i : Fin 2, ∑ j : Fin 2, (!![3/5, 1/5; 1/5, 2/5] : Matrix (Fin 2) (Fin 2) ℝ) i j
    * (p i : ℝ) * (p j : ℝ) = _
  simp [Fin.sum_univ_two]
  ring

theorem theta112Chart_symm_zero : theta112Chart.symm 0 = 0 := by
  rw [Equiv.symm_apply_eq]
  show (0 : ℤ × ℤ) = ((theta112.latticeQuotEquiv theta112Basis) 0 0,
    -(theta112.latticeQuotEquiv theta112Basis) 0 1)
  rw [map_zero]
  rfl

/-- **THE GRAPH ZETA IS AN EPSTEIN ZETA**: for `Re s > 1`, the zeta of `θ(1,1,2)` is
`Γ(s)·5^s·Z_F(s)`. -/
theorem theta112_completedZeta_eq (hb : 0 < theta112.b1) {s : ℂ} (hs : 1 < s.re) :
    theta112.completedZeta hb s = Complex.Gamma s * 5 ^ s * Z DH.F s := by
  have hr : (theta112.classQuadAction).rank = 2 := by
    rw [theta112.classQuadAction_rank, theta112_b1]
  have h := (theta112.classQuadAction).hasSum_completedZeta
    (theta112.classQuadAction_rank ▸ hb) (s := s) (by rw [hr]; push_cast; linarith)
  replace h := theta112Chart.symm.hasSum_iff.mpr h
  have hsum : Summable (fun k => term DH.F s k) :=
    (DH.coercive.summable_maj hs).of_norm_bounded fun k => (norm_term s k).le
  refine h.unique ?_
  rw [Z, ← tsum_mul_left]
  refine (hsum.mul_left _).hasSum.congr_fun fun k => ?_
  simp only [Function.comp_apply]
  by_cases hk : k = 0
  · subst hk
    simp [theta112Chart_symm_zero, term, DH.coercive.q_eq_zero_iff]
  · have hk' : theta112Chart.symm k ≠ 0 := fun h0 =>
      hk (by rw [← theta112Chart.apply_symm_apply k, h0, ← theta112Chart_symm_zero,
        Equiv.apply_symm_apply])
    have hq0 : DH.F.q k ≠ 0 := fun h0 => hk (DH.coercive.q_eq_zero_iff.mp h0)
    have hf : (theta112.classQuadAction).form (theta112Chart.symm k) (theta112Chart.symm k)
        = (DH.F.q k : ℝ) / 5 := by
      have := theta112_form (theta112Chart.symm k)
      rwa [Equiv.apply_symm_apply] at this
    rw [if_neg hk', hf, term, if_neg hq0]
    have hqR : (0 : ℝ) < DH.F.q k := by exact_mod_cast Nat.pos_of_ne_zero hq0
    have h5 : ((DH.F.q k : ℕ) : ℂ) ^ s = (5 : ℂ) ^ s * ((((DH.F.q k : ℝ) / 5 : ℝ)) : ℂ) ^ s := by
      rw [← show (((5 : ℝ) : ℂ)) = 5 by norm_num,
        ← Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
      congr 1
      push_cast
      ring
    have hne : ((((DH.F.q k : ℝ) / 5 : ℝ)) : ℂ) ^ s ≠ 0 := by
      rw [Complex.cpow_ne_zero_iff_of_exponent_ne_zero (fun h => by rw [h, Complex.zero_re] at hs; linarith)]
      exact_mod_cast (by positivity : ((DH.F.q k : ℝ) / 5) ≠ 0)
    have h5' : (5 : ℂ) ^ s ≠ 0 := by
      rw [Complex.cpow_ne_zero_iff_of_exponent_ne_zero (fun h => by rw [h, Complex.zero_re] at hs; linarith)]
      norm_num
    rw [Complex.cpow_neg, h5]
    field_simp

/-- **A ZERO OF A GRAPH ZETA PAST THE LINE OF ABSOLUTE CONVERGENCE**,
kernel-checked: the zeta of `θ(1,1,2)` vanishes at some `s` with `Re s > 1.96`,
`|Im s − 23.0196| < 0.031`. -/
theorem theta112_completedZeta_zero (hb : 0 < theta112.b1) :
    ∃ s : ℂ, 196 / 100 < s.re ∧ |s.im - 230196 / 10000| < 31 / 1000 ∧
      theta112.completedZeta hb s = 0 := by
  obtain ⟨z, hz, hZ⟩ := DH.exists_zero
  have hd : ‖z - Engine.centre DH.P‖ ≤ ((DH.P.Dm : ℝ) - DH.P.D0) / DH.U :=
    mem_closedBall_iff_norm.mp hz
  have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hd))
  have him := (abs_le.mp ((Complex.abs_im_le_norm _).trans hd))
  simp only [Complex.sub_re, Complex.sub_im, Engine.centre, DH.P, DH.U] at hre him
  norm_num at hre him
  have hre' : 196 / 100 < z.re := by linarith
  refine ⟨z, hre', abs_lt.mpr ⟨by linarith, by linarith⟩, ?_⟩
  rw [theta112_completedZeta_eq hb (by linarith), hZ, mul_zero]

end Theta112

end Meno
