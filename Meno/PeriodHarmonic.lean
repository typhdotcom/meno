import Meno.SiegelPoisson
import Meno.HarmonicForm

/-! # Period-Model Harmonic Data: the General Finite-Graph API

The extraction the Phase 18 record promised: the least-norm-at-
prescribed-periods lemma (proved concretely first, for the theta
graph), now packaged as a **builder**: any family of cycle vectors
with positive-definite chain Gram matrix yields a `HarmonicGramData`
whose Gram form is the *inverse* chain Gram — with the variational
identity as a theorem, not an assertion.

The parametric cycle graph `C_n` is instantiated here: one cycle
vector (all ones), chain Gram `[[n]]`, period Gram `[[1/n]]` —
re-deriving the spine's original `1/n` through the period machinery.
The identification with the legacy walk-based route lives in
`Meno/CycleHarmonic.lean`. -/

namespace Meno

open scoped BigOperators
open Matrix

/-! ## Least norm at prescribed periods -/

section PeriodMinimization

variable {ι : Type*} [Fintype ι] {r : ℕ}

/-- Gram matrix of a family of period vectors under the standard dot
product. -/
noncomputable def gramOf (c : Fin r → ι → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => c i ⬝ᵥ c j

theorem gramOf_isSymm (c : Fin r → ι → ℝ) : (gramOf c).IsSymm := by
  ext i j
  exact dotProduct_comm (c j) (c i)

/-- The minimum-norm cochain with periods `k`: the combination of the
period vectors with coefficients `C⁻¹k`. -/
noncomputable def periodRep (c : Fin r → ι → ℝ) (k : Fin r → ℝ) : ι → ℝ :=
  fun e => ∑ i, ((gramOf c)⁻¹.mulVec k) i * c i e

/-- A dot product against a member of the family, for any coefficient
combination: `⟨∑ᵢ xᵢcᵢ, cⱼ⟩ = (x ᵥ* C) j`. -/
private lemma comb_dotProduct (c : Fin r → ι → ℝ) (x : Fin r → ℝ) (j : Fin r) :
    (fun e => ∑ i, x i * c i e) ⬝ᵥ c j = ∑ i, x i * gramOf c i j := by
  calc (fun e => ∑ i, x i * c i e) ⬝ᵥ c j
      = ∑ e, (∑ i, x i * c i e) * c j e := rfl
    _ = ∑ e, ∑ i, x i * c i e * c j e := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ i, ∑ e, x i * c i e * c j e := Finset.sum_comm
    _ = ∑ i, x i * gramOf c i j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        show _ = x i * ∑ e, c i e * c j e
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by ring

/-- The minimum-norm cochain has the prescribed periods. -/
theorem periodRep_periods (c : Fin r → ι → ℝ) (hC : IsUnit (gramOf c).det)
    (k : Fin r → ℝ) (j : Fin r) :
    periodRep c k ⬝ᵥ c j = k j := by
  rw [show periodRep c k = fun e => ∑ i, ((gramOf c)⁻¹.mulVec k) i * c i e from rfl,
    comb_dotProduct]
  have hCT : (gramOf c)ᵀ = gramOf c := gramOf_isSymm c
  have hv : (((gramOf c)⁻¹.mulVec k) ᵥ* gramOf c) j = k j := by
    calc (((gramOf c)⁻¹.mulVec k) ᵥ* gramOf c) j
        = (((gramOf c)⁻¹.mulVec k) ᵥ* ((gramOf c)ᵀ)ᵀ) j := by
          rw [Matrix.transpose_transpose]
      _ = ((gramOf c)ᵀ *ᵥ ((gramOf c)⁻¹ *ᵥ k)) j := by
          rw [Matrix.vecMul_transpose]
      _ = (gramOf c *ᵥ ((gramOf c)⁻¹ *ᵥ k)) j := by rw [hCT]
      _ = k j := by
          rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hC,
            Matrix.one_mulVec]
  exact hv

/-- Energy of the minimum-norm cochain: `kᵀC⁻¹k`. -/
theorem periodRep_energy (c : Fin r → ι → ℝ) (hC : IsUnit (gramOf c).det)
    (k : Fin r → ℝ) :
    periodRep c k ⬝ᵥ periodRep c k = k ⬝ᵥ ((gramOf c)⁻¹.mulVec k) := by
  have h1 : periodRep c k ⬝ᵥ periodRep c k
      = ∑ i, ((gramOf c)⁻¹.mulVec k) i * (periodRep c k ⬝ᵥ c i) := by
    calc periodRep c k ⬝ᵥ periodRep c k
        = ∑ e, periodRep c k e * ∑ i, ((gramOf c)⁻¹.mulVec k) i * c i e := rfl
      _ = ∑ e, ∑ i, ((gramOf c)⁻¹.mulVec k) i * (periodRep c k e * c i e) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∑ e, ((gramOf c)⁻¹.mulVec k) i * (periodRep c k e * c i e) :=
          Finset.sum_comm
      _ = ∑ i, ((gramOf c)⁻¹.mulVec k) i * (periodRep c k ⬝ᵥ c i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum]
          rfl
  rw [h1]
  calc ∑ i, ((gramOf c)⁻¹.mulVec k) i * (periodRep c k ⬝ᵥ c i)
      = ∑ i, ((gramOf c)⁻¹.mulVec k) i * k i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [periodRep_periods c hC k i]
    _ = ((gramOf c)⁻¹.mulVec k) ⬝ᵥ k := rfl
    _ = k ⬝ᵥ ((gramOf c)⁻¹.mulVec k) := dotProduct_comm _ _

/-- **Pythagoras**: any cochain with the prescribed periods has energy
at least `kᵀC⁻¹k`. -/
theorem le_energy_of_periods (c : Fin r → ι → ℝ) (hC : IsUnit (gramOf c).det)
    (k : Fin r → ℝ) (ω : ι → ℝ) (hω : ∀ j, ω ⬝ᵥ c j = k j) :
    k ⬝ᵥ ((gramOf c)⁻¹.mulVec k) ≤ ω ⬝ᵥ ω := by
  set δ : ι → ℝ := ω - periodRep c k with hδ
  have hδc : ∀ j, δ ⬝ᵥ c j = 0 := fun j => by
    rw [hδ, sub_dotProduct, hω j, periodRep_periods c hC k j, sub_self]
  have hcross : periodRep c k ⬝ᵥ δ = 0 := by
    calc periodRep c k ⬝ᵥ δ
        = ∑ e, (∑ i, ((gramOf c)⁻¹.mulVec k) i * c i e) * δ e := rfl
      _ = ∑ e, ∑ i, ((gramOf c)⁻¹.mulVec k) i * (c i e * δ e) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∑ e, ((gramOf c)⁻¹.mulVec k) i * (c i e * δ e) :=
          Finset.sum_comm
      _ = ∑ i, ((gramOf c)⁻¹.mulVec k) i * (δ ⬝ᵥ c i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun e _ => by ring
      _ = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [hδc i, mul_zero]
  have hω_eq : ω = periodRep c k + δ := by
    funext e
    simp [hδ]
  have hexpand : ω ⬝ᵥ ω
      = periodRep c k ⬝ᵥ periodRep c k + 2 * (periodRep c k ⬝ᵥ δ) + δ ⬝ᵥ δ := by
    rw [hω_eq, add_dotProduct, dotProduct_add, dotProduct_add,
      dotProduct_comm δ (periodRep c k)]
    ring
  have hδδ : 0 ≤ δ ⬝ᵥ δ :=
    Finset.sum_nonneg fun e _ => mul_self_nonneg (δ e)
  rw [hexpand, hcross, periodRep_energy c hC k]
  linarith

/-- **The variational identity, packaged**: `kᵀC⁻¹k` is the least
energy among cochains with periods `k` — attained, with witness
`periodRep`. This is the Hodge variational principle in its
cohomological (period) formulation. -/
theorem isLeast_energy_periods (c : Fin r → ι → ℝ) (hC : IsUnit (gramOf c).det)
    (k : Fin r → ℝ) :
    IsLeast {E : ℝ | ∃ ω : ι → ℝ, (∀ j, ω ⬝ᵥ c j = k j) ∧ E = ω ⬝ᵥ ω}
      (k ⬝ᵥ ((gramOf c)⁻¹.mulVec k)) :=
  ⟨⟨periodRep c k, fun j => periodRep_periods c hC k j,
      (periodRep_energy c hC k).symm⟩,
    fun _ ⟨ω, hω, hE⟩ => hE ▸ le_energy_of_periods c hC k ω hω⟩

end PeriodMinimization

/-! ## The builder: cycles to harmonic Gram data -/

section Builder

universe u

variable {V : Type u} {ι : Type*} [Fintype ι] {r : ℕ}

/-- A positive scalar 1×1 matrix is positive definite. -/
lemma posDef_fin_one (α : ℝ) (hα : 0 < α) :
    (!![α] : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · ext i j
    fin_cases i
    fin_cases j
    rfl
  · have hx0 : x 0 ≠ 0 := by
      intro h0
      exact hx (funext fun i => by fin_cases i; exact h0)
    have hcomp : star x ⬝ᵥ (!![α] : Matrix (Fin 1) (Fin 1) ℝ).mulVec x
        = α * (x 0) ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Matrix.cons_val_fin_one, Pi.star_apply]
      ring
    rw [hcomp]
    exact mul_pos hα (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx0)))

/-- **The builder**: cycle vectors with positive-definite chain Gram
yield harmonic Gram data with the inverse chain Gram as period form.
Symmetry, positive-definiteness, summability all derived. -/
noncomputable def HarmonicGramData.ofCycles (c : Fin r → ι → ℝ)
    (hC : (gramOf c).PosDef) : HarmonicGramData V where
  r := r
  gram := (gramOf c)⁻¹
  gram_symm := by
    show ((gramOf c)⁻¹)ᵀ = (gramOf c)⁻¹
    rw [Matrix.transpose_nonsing_inv,
      show (gramOf c)ᵀ = gramOf c from gramOf_isSymm c]
  gram_posDef := posDef_inv hC
  summable := summable_exp_neg_quadForm (posDef_inv hC)

/-- The builder's data satisfies the variational identity: the Gram
energy of sector `k` is the least cochain energy at periods `k`. -/
theorem HarmonicGramData.ofCycles_energy_isLeast (c : Fin r → ι → ℝ)
    (hC : (gramOf c).PosDef) (k : Fin r → ℤ) :
    IsLeast {E : ℝ | ∃ ω : ι → ℝ,
        (∀ j, ω ⬝ᵥ c j = (k j : ℝ)) ∧ E = ω ⬝ᵥ ω}
      ((HarmonicGramData.ofCycles (V := V) c hC).energy k) := by
  have hdet : IsUnit (gramOf c).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hC.det_pos)
  have h := isLeast_energy_periods c hdet (fun j => (k j : ℝ))
  have hval : (HarmonicGramData.ofCycles (V := V) c hC).energy k
      = (fun j => (k j : ℝ)) ⬝ᵥ ((gramOf c)⁻¹.mulVec (fun j => (k j : ℝ))) := by
    show ∑ i, ∑ j, (gramOf c)⁻¹ i j * (k i : ℝ) * (k j : ℝ) = _
    rw [quadForm_dotProduct]
  rw [hval]
  exact h

end Builder

/-! ## The cycle graph `C_n` through periods

Edges `e : Fin n` run from vertex `e` to vertex `e + 1` (cyclically).
One basis cycle: the all-ones cochain. Chain Gram `[[n]]`, period Gram
`[[1/n]]` — the spine's original harmonic mass, re-derived. -/

section CyclePeriods

variable (n : ℕ)

/-- Boundary operator of the cycle graph: net flow into each vertex.
Edge `e` runs `e → e + 1`. -/
noncomputable def cycleBoundary [NeZero n] (ω : Fin n → ℝ) (v : Fin n) : ℝ :=
  ∑ e, ((if e + 1 = v then (1 : ℝ) else 0)
    - (if e = v then (1 : ℝ) else 0)) * ω e

/-- The single basis cycle: the all-ones cochain. -/
noncomputable def cycleAllOnes : Fin 1 → Fin n → ℝ := fun _ _ => 1

/-- The boundary in closed form: inflow minus outflow. -/
theorem cycleBoundary_eq [NeZero n] (ω : Fin n → ℝ) (v : Fin n) :
    cycleBoundary n ω v = ω (v - 1) - ω v := by
  unfold cycleBoundary
  rw [show (fun e => ((if e + 1 = v then (1 : ℝ) else 0)
      - (if e = v then (1 : ℝ) else 0)) * ω e)
      = fun e => ((if e = v - 1 then ω e else 0) - if e = v then ω e else 0) from
    funext fun e => by
      by_cases h1 : e + 1 = v
      · have h1' : e = v - 1 := by rw [eq_sub_iff_add_eq]; exact h1
        by_cases h2 : e = v
        · rw [if_pos h1, if_pos h2, if_pos h1', if_pos h2]; ring
        · rw [if_pos h1, if_neg h2, if_pos h1', if_neg h2]; ring
      · have h1' : ¬(e = v - 1) := fun hc =>
          h1 (by rw [← eq_sub_iff_add_eq]; exact hc)
        by_cases h2 : e = v
        · rw [if_neg h1, if_pos h2, if_neg h1', if_pos h2]; ring
        · rw [if_neg h1, if_neg h2, if_neg h1', if_neg h2]; ring]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ (v - 1) ω,
    Finset.sum_ite_eq' Finset.univ v ω]
  simp

/-- The all-ones cochain is a cycle. -/
theorem cycleBoundary_allOnes [NeZero n] (v : Fin n) :
    cycleBoundary n (cycleAllOnes n 0) v = 0 := by
  rw [cycleBoundary_eq]
  show (1 : ℝ) - 1 = 0
  ring

/-- **`b₁(C_n) = 1`**: a cochain with vanishing boundary is constant,
hence a multiple of the all-ones cycle. -/
theorem eq_smul_allOnes_of_cycleBoundary_eq_zero [NeZero n] (ω : Fin n → ℝ)
    (h : ∀ v, cycleBoundary n ω v = 0) :
    ω = fun e => ω 0 * cycleAllOnes n 0 e := by
  have hstep : ∀ v : Fin n, ω (v - 1) = ω v := by
    intro v
    have := h v
    rw [cycleBoundary_eq] at this
    linarith
  have hsucc : ∀ v : Fin n, ω v = ω (v + 1) := fun v => by
    have := hstep (v + 1)
    rwa [add_sub_cancel_right] at this
  have hval : ∀ (m : ℕ) (hm : m < n), ω ⟨m, hm⟩ = ω 0 := by
    intro m
    induction m with
    | zero =>
      intro hm
      have h0 : (⟨0, hm⟩ : Fin n) = 0 := Fin.ext (by simp)
      rw [h0]
    | succ m ih =>
      intro hm
      have hm' : m < n := Nat.lt_of_succ_lt hm
      have hmk : (⟨m + 1, hm⟩ : Fin n) = ⟨m, hm'⟩ + 1 := by
        apply Fin.ext
        rw [Fin.val_add]
        have h1 : (1 : Fin n).val = 1 := by
          rw [Fin.val_one']
          exact Nat.mod_eq_of_lt (by omega)
        rw [h1]
        exact (Nat.mod_eq_of_lt hm).symm
      rw [hmk, ← hsucc ⟨m, hm'⟩]
      exact ih hm'
  funext e
  show ω e = ω 0 * 1
  rw [mul_one, show e = ⟨e.val, e.isLt⟩ from (Fin.eta e e.isLt).symm,
    hval e.val e.isLt]

/-- The chain Gram of the cycle graph: `[[n]]`. -/
theorem gramOf_cycleAllOnes : gramOf (cycleAllOnes n) = !![(n : ℝ)] := by
  ext i j
  fin_cases i
  fin_cases j
  show (cycleAllOnes n 0) ⬝ᵥ (cycleAllOnes n 0) = (n : ℝ)
  simp [cycleAllOnes, dotProduct]

/-- The period-model harmonic Gram data of the cycle graph. -/
noncomputable def cyclePeriodData (hn : 0 < n) : HarmonicGramData (Fin n) :=
  HarmonicGramData.ofCycles (cycleAllOnes n)
    (by
      rw [gramOf_cycleAllOnes]
      exact posDef_fin_one _ (by exact_mod_cast hn))

/-- Its Gram form is `[[1/n]]` — the spine's original harmonic mass,
derived through the period machinery. -/
theorem cyclePeriodData_gram (hn : 0 < n) :
    (cyclePeriodData n hn).gram = !![1 / (n : ℝ)] := by
  show (gramOf (cycleAllOnes n))⁻¹ = _
  rw [gramOf_cycleAllOnes,
    inv_fin_one (n : ℝ) (by exact_mod_cast hn.ne'), one_div]

end CyclePeriods

/-! ## The wedge of two cycles through periods

`C_{n₁} ∨ C_{n₂}`: two cycles joined at a basepoint. This is the space
that *falsified* the naive categorical route — its loop monoid is
nonabelian (free on two generators), so no `SectorPresentation` exists
at any rank (`SectorPresentation.end_comm`). The period machinery works
directly on the abelianization `H¹` and handles it without incident.

Vertex model: `Fin n₁ ⊕ Fin n₂`, with the right cycle's basepoint
routed through the left basepoint `Sum.inl 0`; the vertex `Sum.inr 0`
is left isolated, which changes neither boundaries nor cycles (it adds
an edgeless component, so `b₁` is unaffected). This avoids a quotient
vertex type entirely.

Edges: `Fin n₁ ⊕ Fin n₂`; left edge `e` runs `e → e + 1` in the left
cycle, right edge `e` runs `e → e + 1` in the right cycle with `0`
read as the shared basepoint. Two disjoint-support basis cycles give
chain Gram `diag(n₁, n₂)`, hence period Gram `diag(1/n₁, 1/n₂)` — the
matrix `wedgeHarmonicGramData` (`Meno/CycleHarmonic.lean`) asserts,
now derived. -/

section WedgePeriods

/-- A function on `Fin n` with a backward-step identity at every
nonzero vertex is constant. The induction workhorse for spanning
arguments: cycle constancy needs steps only away from the basepoint. -/
theorem apply_eq_apply_zero_of_step {n : ℕ} [NeZero n] (f : Fin n → ℝ)
    (hstep : ∀ v : Fin n, v ≠ 0 → f (v - 1) = f v) (v : Fin n) :
    f v = f 0 := by
  have hval : ∀ (m : ℕ) (hm : m < n), f ⟨m, hm⟩ = f 0 := by
    intro m
    induction m with
    | zero =>
      intro hm
      have h0 : (⟨0, hm⟩ : Fin n) = 0 := Fin.ext (by simp)
      rw [h0]
    | succ m ih =>
      intro hm
      have hm' : m < n := Nat.lt_of_succ_lt hm
      have hmk : (⟨m + 1, hm⟩ : Fin n) = ⟨m, hm'⟩ + 1 := by
        apply Fin.ext
        rw [Fin.val_add]
        have h1 : (1 : Fin n).val = 1 := by
          rw [Fin.val_one']
          exact Nat.mod_eq_of_lt (by omega)
        rw [h1]
        exact (Nat.mod_eq_of_lt hm).symm
      have hne : (⟨m + 1, hm⟩ : Fin n) ≠ 0 := by
        intro hc
        have hv := congrArg Fin.val hc
        rw [Fin.val_zero] at hv
        exact Nat.succ_ne_zero m hv
      have hsub : (⟨m + 1, hm⟩ : Fin n) - 1 = ⟨m, hm'⟩ := by
        rw [hmk, add_sub_cancel_right]
      have hs := hstep ⟨m + 1, hm⟩ hne
      rw [hsub] at hs
      rw [← hs]
      exact ih hm'
  have h := hval v.val v.isLt
  rwa [Fin.eta] at h

variable (n₁ n₂ : ℕ)

/-- The wedge's vertex map for the right cycle: vertex `v` of `C_{n₂}`,
with the basepoint `0` identified with the left basepoint `Sum.inl 0`. -/
def wedgeVertex [NeZero n₁] [NeZero n₂] (v : Fin n₂) : Fin n₁ ⊕ Fin n₂ :=
  if v = 0 then Sum.inl 0 else Sum.inr v

/-- Edge sources: left edge `e` starts at left vertex `e`; right edge
`e` starts at the basepoint-routed right vertex `e`. -/
def wedgeSrc [NeZero n₁] [NeZero n₂] : Fin n₁ ⊕ Fin n₂ → Fin n₁ ⊕ Fin n₂ :=
  Sum.elim (fun e => Sum.inl e) (fun e => wedgeVertex n₁ n₂ e)

/-- Edge targets: left edge `e` ends at left vertex `e + 1`; right edge
`e` ends at the basepoint-routed right vertex `e + 1`. -/
def wedgeTgt [NeZero n₁] [NeZero n₂] : Fin n₁ ⊕ Fin n₂ → Fin n₁ ⊕ Fin n₂ :=
  Sum.elim (fun e => Sum.inl (e + 1)) (fun e => wedgeVertex n₁ n₂ (e + 1))

/-- Boundary operator of the wedge: net flow into each vertex. -/
noncomputable def wedgeBoundary [NeZero n₁] [NeZero n₂]
    (ω : Fin n₁ ⊕ Fin n₂ → ℝ) (v : Fin n₁ ⊕ Fin n₂) : ℝ :=
  ∑ e, ((if wedgeTgt n₁ n₂ e = v then (1 : ℝ) else 0)
    - (if wedgeSrc n₁ n₂ e = v then (1 : ℝ) else 0)) * ω e

/-- The two basis cycles: all-ones on the left cycle's edges, all-ones
on the right cycle's edges. Disjoint supports. -/
noncomputable def wedgeCycles : Fin 2 → Fin n₁ ⊕ Fin n₂ → ℝ :=
  ![Sum.elim (fun _ => 1) (fun _ => 0), Sum.elim (fun _ => 0) (fun _ => 1)]

/-! ### Indicator bookkeeping -/

private lemma ite_inl_eq_inl (a b : Fin n₁) :
    (if (Sum.inl a : Fin n₁ ⊕ Fin n₂) = Sum.inl b then (1 : ℝ) else 0)
      = if a = b then (1 : ℝ) else 0 := by
  by_cases h : a = b
  · rw [if_pos (by rw [h]), if_pos h]
  · rw [if_neg (fun hc => h (Sum.inl.inj hc)), if_neg h]

lemma wedgeVertex_eq_inl_iff [NeZero n₁] [NeZero n₂] (v : Fin n₂) (w : Fin n₁) :
    wedgeVertex n₁ n₂ v = Sum.inl w ↔ v = 0 ∧ w = 0 := by
  unfold wedgeVertex
  by_cases h : v = 0
  · rw [if_pos h]
    constructor
    · intro hc
      exact ⟨h, (Sum.inl.inj hc).symm⟩
    · intro hw
      rw [hw.2]
  · rw [if_neg h]
    constructor
    · intro hc
      exact Sum.noConfusion hc
    · intro hw
      exact absurd hw.1 h

lemma wedgeVertex_eq_inr_iff [NeZero n₁] [NeZero n₂] (v w : Fin n₂) :
    wedgeVertex n₁ n₂ v = Sum.inr w ↔ v = w ∧ v ≠ 0 := by
  unfold wedgeVertex
  by_cases h : v = 0
  · rw [if_pos h]
    constructor
    · intro hc
      exact Sum.noConfusion hc
    · intro hw
      exact absurd h hw.2
  · rw [if_neg h]
    constructor
    · intro hc
      exact ⟨Sum.inr.inj hc, h⟩
    · intro hw
      rw [hw.1]

private lemma ite_wedgeVertex_inl_zero [NeZero n₁] [NeZero n₂] (v : Fin n₂) :
    (if wedgeVertex n₁ n₂ v = Sum.inl (0 : Fin n₁) then (1 : ℝ) else 0)
      = if v = 0 then (1 : ℝ) else 0 := by
  by_cases h : v = 0
  · rw [if_pos ((wedgeVertex_eq_inl_iff n₁ n₂ v 0).mpr ⟨h, rfl⟩), if_pos h]
  · rw [if_neg (fun hc => h ((wedgeVertex_eq_inl_iff n₁ n₂ v 0).mp hc).1), if_neg h]

private lemma ite_wedgeVertex_inl_ne [NeZero n₁] [NeZero n₂] (v : Fin n₂)
    (w : Fin n₁) (hw : w ≠ 0) :
    (if wedgeVertex n₁ n₂ v = Sum.inl w then (1 : ℝ) else 0) = 0 :=
  if_neg (fun hc => hw ((wedgeVertex_eq_inl_iff n₁ n₂ v w).mp hc).2)

private lemma ite_wedgeVertex_inr_zero [NeZero n₁] [NeZero n₂] (v : Fin n₂) :
    (if wedgeVertex n₁ n₂ v = Sum.inr (0 : Fin n₂) then (1 : ℝ) else 0) = 0 :=
  if_neg (fun hc => ((wedgeVertex_eq_inr_iff n₁ n₂ v 0).mp hc).2
    ((wedgeVertex_eq_inr_iff n₁ n₂ v 0).mp hc).1)

private lemma ite_wedgeVertex_inr_ne [NeZero n₁] [NeZero n₂] (v w : Fin n₂)
    (hw : w ≠ 0) :
    (if wedgeVertex n₁ n₂ v = Sum.inr w then (1 : ℝ) else 0)
      = if v = w then (1 : ℝ) else 0 := by
  by_cases h : v = w
  · rw [if_pos ((wedgeVertex_eq_inr_iff n₁ n₂ v w).mpr
      ⟨h, by rw [h]; exact hw⟩), if_pos h]
  · rw [if_neg (fun hc => h ((wedgeVertex_eq_inr_iff n₁ n₂ v w).mp hc).1), if_neg h]

/-! ### Boundary in closed form -/

/-- Boundary at a left vertex: the left cycle's boundary, plus — at the
shared basepoint only — the right cycle's basepoint flow. -/
theorem wedgeBoundary_inl [NeZero n₁] [NeZero n₂]
    (ω : Fin n₁ ⊕ Fin n₂ → ℝ) (w : Fin n₁) :
    wedgeBoundary n₁ n₂ ω (Sum.inl w)
      = cycleBoundary n₁ (fun e => ω (Sum.inl e)) w
        + (if w = 0 then cycleBoundary n₂ (fun e => ω (Sum.inr e)) 0 else 0) := by
  unfold wedgeBoundary
  rw [Fintype.sum_sum_type]
  show (∑ e : Fin n₁,
        ((if (Sum.inl (e + 1) : Fin n₁ ⊕ Fin n₂) = Sum.inl w then (1 : ℝ) else 0)
          - (if (Sum.inl e : Fin n₁ ⊕ Fin n₂) = Sum.inl w then (1 : ℝ) else 0))
            * ω (Sum.inl e))
      + (∑ e : Fin n₂,
        ((if wedgeVertex n₁ n₂ (e + 1) = Sum.inl w then (1 : ℝ) else 0)
          - (if wedgeVertex n₁ n₂ e = Sum.inl w then (1 : ℝ) else 0))
            * ω (Sum.inr e))
      = cycleBoundary n₁ (fun e => ω (Sum.inl e)) w
        + (if w = 0 then cycleBoundary n₂ (fun e => ω (Sum.inr e)) 0 else 0)
  congr 1
  · unfold cycleBoundary
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [ite_inl_eq_inl n₁ n₂ (e + 1) w, ite_inl_eq_inl n₁ n₂ e w]
  · by_cases hw : w = 0
    · subst hw
      rw [if_pos rfl]
      unfold cycleBoundary
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [ite_wedgeVertex_inl_zero n₁ n₂ (e + 1), ite_wedgeVertex_inl_zero n₁ n₂ e]
    · rw [if_neg hw]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [ite_wedgeVertex_inl_ne n₁ n₂ (e + 1) w hw,
        ite_wedgeVertex_inl_ne n₁ n₂ e w hw]
      ring

/-- Boundary at a right vertex: the right cycle's boundary away from
the basepoint; zero at the unused vertex `Sum.inr 0`. -/
theorem wedgeBoundary_inr [NeZero n₁] [NeZero n₂]
    (ω : Fin n₁ ⊕ Fin n₂ → ℝ) (w : Fin n₂) :
    wedgeBoundary n₁ n₂ ω (Sum.inr w)
      = if w = 0 then 0 else cycleBoundary n₂ (fun e => ω (Sum.inr e)) w := by
  unfold wedgeBoundary
  rw [Fintype.sum_sum_type]
  show (∑ e : Fin n₁,
        ((if (Sum.inl (e + 1) : Fin n₁ ⊕ Fin n₂) = Sum.inr w then (1 : ℝ) else 0)
          - (if (Sum.inl e : Fin n₁ ⊕ Fin n₂) = Sum.inr w then (1 : ℝ) else 0))
            * ω (Sum.inl e))
      + (∑ e : Fin n₂,
        ((if wedgeVertex n₁ n₂ (e + 1) = Sum.inr w then (1 : ℝ) else 0)
          - (if wedgeVertex n₁ n₂ e = Sum.inr w then (1 : ℝ) else 0))
            * ω (Sum.inr e))
      = if w = 0 then 0 else cycleBoundary n₂ (fun e => ω (Sum.inr e)) w
  have hleft : (∑ e : Fin n₁,
      ((if (Sum.inl (e + 1) : Fin n₁ ⊕ Fin n₂) = Sum.inr w then (1 : ℝ) else 0)
        - (if (Sum.inl e : Fin n₁ ⊕ Fin n₂) = Sum.inr w then (1 : ℝ) else 0))
          * ω (Sum.inl e)) = 0 := by
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [if_neg (fun hc => Sum.noConfusion hc), if_neg (fun hc => Sum.noConfusion hc)]
    ring
  rw [hleft, zero_add]
  by_cases hw : w = 0
  · subst hw
    rw [if_pos rfl]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [ite_wedgeVertex_inr_zero n₁ n₂ (e + 1), ite_wedgeVertex_inr_zero n₁ n₂ e]
    ring
  · rw [if_neg hw]
    unfold cycleBoundary
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [ite_wedgeVertex_inr_ne n₁ n₂ (e + 1) w hw, ite_wedgeVertex_inr_ne n₁ n₂ e w hw]

/-! ### The two vectors are cycles, and they span -/

/-- Both basis vectors have vanishing boundary everywhere. -/
theorem wedgeBoundary_cycles [NeZero n₁] [NeZero n₂] (i : Fin 2)
    (v : Fin n₁ ⊕ Fin n₂) :
    wedgeBoundary n₁ n₂ (wedgeCycles n₁ n₂ i) v = 0 := by
  fin_cases i
  · cases v with
    | inl w =>
      rw [wedgeBoundary_inl, cycleBoundary_eq, cycleBoundary_eq]
      show ((1 : ℝ) - 1) + (if w = 0 then ((0 : ℝ) - 0) else 0) = 0
      by_cases hw : w = 0
      · rw [if_pos hw]; ring
      · rw [if_neg hw]; ring
    | inr w =>
      rw [wedgeBoundary_inr]
      by_cases hw : w = 0
      · rw [if_pos hw]
      · rw [if_neg hw, cycleBoundary_eq]
        show (0 : ℝ) - 0 = 0
        ring
  · cases v with
    | inl w =>
      rw [wedgeBoundary_inl, cycleBoundary_eq, cycleBoundary_eq]
      show ((0 : ℝ) - 0) + (if w = 0 then ((1 : ℝ) - 1) else 0) = 0
      by_cases hw : w = 0
      · rw [if_pos hw]; ring
      · rw [if_neg hw]; ring
    | inr w =>
      rw [wedgeBoundary_inr]
      by_cases hw : w = 0
      · rw [if_pos hw]
      · rw [if_neg hw, cycleBoundary_eq]
        show (1 : ℝ) - 1 = 0
        ring

/-- **`b₁(C_{n₁} ∨ C_{n₂}) = 2`**: a cochain with vanishing boundary is
a combination of the two basis cycles. The mixed flow condition at the
shared basepoint is automatically satisfied — consistent with the
wedge's Euler count `E − V + 1 = 2`. -/
theorem eq_comb_of_wedgeBoundary_eq_zero [NeZero n₁] [NeZero n₂]
    (ω : Fin n₁ ⊕ Fin n₂ → ℝ) (h : ∀ v, wedgeBoundary n₁ n₂ ω v = 0) :
    ω = fun e => ω (Sum.inl 0) * wedgeCycles n₁ n₂ 0 e
      + ω (Sum.inr 0) * wedgeCycles n₁ n₂ 1 e := by
  have hL : ∀ w : Fin n₁, ω (Sum.inl w) = ω (Sum.inl 0) := by
    intro w
    refine apply_eq_apply_zero_of_step (fun e => ω (Sum.inl e)) (fun v hv => ?_) w
    have hb := h (Sum.inl v)
    rw [wedgeBoundary_inl, if_neg hv, add_zero, cycleBoundary_eq] at hb
    linarith
  have hR : ∀ w : Fin n₂, ω (Sum.inr w) = ω (Sum.inr 0) := by
    intro w
    refine apply_eq_apply_zero_of_step (fun e => ω (Sum.inr e)) (fun v hv => ?_) w
    have hb := h (Sum.inr v)
    rw [wedgeBoundary_inr, if_neg hv, cycleBoundary_eq] at hb
    linarith
  funext e
  cases e with
  | inl a =>
    show ω (Sum.inl a) = ω (Sum.inl 0) * 1 + ω (Sum.inr 0) * 0
    rw [mul_one, mul_zero, add_zero]
    exact hL a
  | inr b =>
    show ω (Sum.inr b) = ω (Sum.inl 0) * 0 + ω (Sum.inr 0) * 1
    rw [mul_one, mul_zero, zero_add]
    exact hR b

/-! ### Chain Gram, period Gram -/

/-- The chain Gram of the wedge: `diag(n₁, n₂)`. Disjoint edge supports
keep the off-diagonal at zero. -/
theorem gramOf_wedgeCycles :
    gramOf (wedgeCycles n₁ n₂) = !![(n₁ : ℝ), 0; 0, (n₂ : ℝ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramOf, dotProduct, wedgeCycles, Fintype.sum_sum_type]

/-- The chain Gram is positive definite. -/
theorem gramOf_wedgeCycles_posDef (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    (gramOf (wedgeCycles n₁ n₂)).PosDef := by
  rw [gramOf_wedgeCycles]
  exact (QuadraticAction.ofDiagonal₂ (n₁ : ℝ) (n₂ : ℝ)
    (by exact_mod_cast h₁) (by exact_mod_cast h₂)).Q_posDef

/-- The period-model harmonic Gram data of the wedge. -/
noncomputable def wedgePeriodData (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    HarmonicGramData (Fin n₁ ⊕ Fin n₂) :=
  HarmonicGramData.ofCycles (wedgeCycles n₁ n₂)
    (gramOf_wedgeCycles_posDef n₁ n₂ h₁ h₂)

/-- Its Gram form: `diag(1/n₁, 1/n₂)` — the direct sum of the two
cycles' period forms. Sharing zero edges means zero off-diagonal,
zero interaction, zero binding. -/
theorem wedgePeriodData_gram (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    (wedgePeriodData n₁ n₂ h₁ h₂).gram
      = !![1 / (n₁ : ℝ), 0; 0, 1 / (n₂ : ℝ)] := by
  have hn₁ : (n₁ : ℝ) ≠ 0 := by exact_mod_cast h₁.ne'
  have hn₂ : (n₂ : ℝ) ≠ 0 := by exact_mod_cast h₂.ne'
  show (gramOf (wedgeCycles n₁ n₂))⁻¹ = _
  rw [gramOf_wedgeCycles]
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;>
    field_simp

end WedgePeriods

end Meno
