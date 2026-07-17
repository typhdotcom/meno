import Meno.PeriodHarmonic

/-! # Cycle Presentation: a finite graph with a chosen cycle basis

The general home for the graph-level facts that Phases 18–21 proved
per instance. A `CyclePresentation V ι` is edge data `(src, tgt)` on
finite vertex/edge types together with a **chosen** family of cycle
vectors that is closed (zero boundary), spans the cycle space, and has
positive-definite chain Gram matrix.

From this data alone:

* **Discrete Stokes** (`grad_dotProduct_eq`, `grad_period`): the
  pairing of a gradient against any cycle vanishes — local
  re-description is invisible to periods.
* **Exactness** (`period_eq_zero_iff_exists_grad`): a cochain has
  vanishing periods *iff* it is a gradient. Generic — **no
  connectivity hypothesis**: connectivity governs uniqueness of the
  potential (modulo locally constant functions), never existence. The
  proof is rank counting: `range gradᵀ` and `ker ∂` intersect
  trivially (a sum-of-squares argument) and their dimensions add up to
  the edge count (`rank Bᵀ = rank B` + rank–nullity).
* **The incompressible residue** (`cochainQuotEquiv`,
  `finrank_cochainQuot`): cochains modulo gradients ≃ `ℝ^r` via the
  period map. What survives quotienting by local re-description is
  exactly the period data — the mathematical half of the keystone.

**Chosen basis, not canonical**: `k ∈ ℤ^r` means periods *against this
basis*. Rescaling or re-basing the cycles changes the meaning of `k`.
The unimodular (`GL(r, ℤ)`) change-of-basis invariance theorem is the
design gate for any coordinate-independence claim; it is **not yet
formalized** (recorded in PLAN, Phase 22). -/

namespace Meno

open scoped BigOperators
open Matrix

universe u v

/-- Net flow of a 1-cochain into a vertex, for edge data `(src, tgt)`:
each edge contributes `+ω e` at its target and `−ω e` at its source. -/
noncomputable def flowBoundary {V : Type u} {ι : Type v} [Fintype ι]
    [DecidableEq V] (src tgt : ι → V) (ω : ι → ℝ) (v : V) : ℝ :=
  ∑ e, ((if tgt e = v then (1 : ℝ) else 0)
    - (if src e = v then (1 : ℝ) else 0)) * ω e

/-- A finite graph presented with a chosen cycle basis: edge data,
`r` closed cycle vectors spanning the cycle space, with
positive-definite chain Gram matrix. -/
structure CyclePresentation (V : Type u) (ι : Type v)
    [Fintype V] [Fintype ι] [DecidableEq V] where
  /-- Edge sources. -/
  src : ι → V
  /-- Edge targets. -/
  tgt : ι → V
  /-- Number of basis cycles (the intended `b₁`). -/
  r : ℕ
  /-- The chosen cycle vectors. -/
  cycles : Fin r → ι → ℝ
  /-- Each basis vector is a cycle: zero boundary at every vertex. -/
  cycles_closed : ∀ i v, flowBoundary src tgt (cycles i) v = 0
  /-- The basis spans the cycle space. -/
  spanning : ∀ ω : ι → ℝ, (∀ v, flowBoundary src tgt ω v = 0) →
    ∃ a : Fin r → ℝ, ω = fun e => ∑ i, a i * cycles i e
  /-- The chain Gram matrix is positive definite (in particular the
  cycles are linearly independent). -/
  gram_posDef : (gramOf cycles).PosDef

namespace CyclePresentation

variable {V : Type u} {ι : Type v} [Fintype V] [Fintype ι] [DecidableEq V]
variable (P : CyclePresentation V ι)

/-- The harmonic Gram data of the presentation, through the Phase-20
builder: Gram form is the inverse chain Gram, and the variational
identity holds by `HarmonicGramData.ofCycles_energy_isLeast`. -/
noncomputable def toGramData : HarmonicGramData V :=
  HarmonicGramData.ofCycles (V := V) P.cycles P.gram_posDef

/-- The gradient (coboundary) of a vertex potential. -/
noncomputable def grad (f : V → ℝ) : ι → ℝ :=
  fun e => f (P.tgt e) - f (P.src e)

/-! ## The boundary matrix and discrete Stokes -/

/-- The boundary matrix: rows are vertices, columns are edges. -/
noncomputable def boundaryMatrix : Matrix V ι ℝ :=
  Matrix.of fun v e => (if P.tgt e = v then (1 : ℝ) else 0)
    - (if P.src e = v then (1 : ℝ) else 0)

theorem boundaryMatrix_mulVec (ω : ι → ℝ) (v : V) :
    (P.boundaryMatrix *ᵥ ω) v = flowBoundary P.src P.tgt ω v := rfl

private lemma sum_ite_one_mul (f : V → ℝ) (a : V) :
    ∑ v, (if a = v then (1 : ℝ) else 0) * f v = f a := by
  rw [show (fun v => (if a = v then (1 : ℝ) else 0) * f v)
      = fun v => if a = v then f v else 0 from funext fun v => by
    by_cases h : a = v
    · rw [if_pos h, if_pos h, one_mul]
    · rw [if_neg h, if_neg h, zero_mul]]
  rw [Finset.sum_ite_eq Finset.univ a f]
  simp

/-- The transpose of the boundary matrix computes the gradient. -/
theorem transpose_boundaryMatrix_mulVec (f : V → ℝ) :
    P.boundaryMatrixᵀ *ᵥ f = P.grad f := by
  funext e
  show ∑ v, ((if P.tgt e = v then (1 : ℝ) else 0)
      - (if P.src e = v then (1 : ℝ) else 0)) * f v
    = f (P.tgt e) - f (P.src e)
  calc ∑ v, ((if P.tgt e = v then (1 : ℝ) else 0)
        - (if P.src e = v then (1 : ℝ) else 0)) * f v
      = (∑ v, (if P.tgt e = v then (1 : ℝ) else 0) * f v)
        - ∑ v, (if P.src e = v then (1 : ℝ) else 0) * f v := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun v _ => by ring
    _ = f (P.tgt e) - f (P.src e) := by
        rw [sum_ite_one_mul f (P.tgt e), sum_ite_one_mul f (P.src e)]

/-- **Discrete Stokes / summation by parts**: pairing a gradient
against a cochain is pairing the potential against the boundary. -/
theorem grad_dotProduct_eq (f : V → ℝ) (ω : ι → ℝ) :
    P.grad f ⬝ᵥ ω = ∑ v, f v * flowBoundary P.src P.tgt ω v := by
  rw [← P.transpose_boundaryMatrix_mulVec f]
  calc (P.boundaryMatrixᵀ *ᵥ f) ⬝ᵥ ω
      = (f ᵥ* P.boundaryMatrix) ⬝ᵥ ω := by rw [Matrix.mulVec_transpose]
    _ = f ⬝ᵥ (P.boundaryMatrix *ᵥ ω) :=
        (Matrix.dotProduct_mulVec f P.boundaryMatrix ω).symm
    _ = ∑ v, f v * flowBoundary P.src P.tgt ω v := by
        show ∑ v, f v * (P.boundaryMatrix *ᵥ ω) v = _
        exact Finset.sum_congr rfl fun v _ => by rw [P.boundaryMatrix_mulVec]

/-- Gradients have vanishing periods: local re-description is
invisible to the sectors. -/
theorem grad_period (f : V → ℝ) (i : Fin P.r) :
    P.grad f ⬝ᵥ P.cycles i = 0 := by
  rw [P.grad_dotProduct_eq]
  exact Finset.sum_eq_zero fun v _ => by rw [P.cycles_closed i v, mul_zero]

/-! ## Exactness, generically -/

/-- **Exactness**: a cochain has vanishing periods against the cycle
basis iff it is a gradient. No connectivity hypothesis — connectivity
controls uniqueness of the potential, never existence.

Proof of the forward direction: `range (∂ᵀ)` and `ker ∂` intersect
trivially (if `x = ∂ᵀf` and `∂x = 0` then `⟨x,x⟩ = ⟨f, ∂x⟩ = 0`) and
their dimensions sum to the edge count (`rank ∂ᵀ = rank ∂` plus
rank–nullity), so together they fill the edge space. Decompose
`ω = ∂ᵀf + z`; the residual `z` is boundary-free, hence by spanning a
cycle combination, hence orthogonal to `ω` (zero periods) and to
`∂ᵀf` (Stokes) — so orthogonal to itself, so zero. -/
theorem period_eq_zero_iff_exists_grad (ω : ι → ℝ) :
    (∀ i, ω ⬝ᵥ P.cycles i = 0) ↔ ∃ f : V → ℝ, P.grad f = ω := by
  constructor
  · intro hper
    classical
    -- Dimension bookkeeping.
    have hrank : Module.finrank ℝ
          (LinearMap.range P.boundaryMatrixᵀ.mulVecLin)
        + Module.finrank ℝ (LinearMap.ker P.boundaryMatrix.mulVecLin)
        = Fintype.card ι := by
      have h1 : Module.finrank ℝ
            (LinearMap.range P.boundaryMatrixᵀ.mulVecLin)
          = P.boundaryMatrixᵀ.rank := rfl
      have h2 : P.boundaryMatrixᵀ.rank = P.boundaryMatrix.rank :=
        Matrix.rank_transpose P.boundaryMatrix
      have h3 := LinearMap.finrank_range_add_finrank_ker
        P.boundaryMatrix.mulVecLin
      rw [Module.finrank_fintype_fun_eq_card] at h3
      rw [h1, h2]
      exact h3
    -- Trivial intersection.
    have hdisj : LinearMap.range P.boundaryMatrixᵀ.mulVecLin
        ⊓ LinearMap.ker P.boundaryMatrix.mulVecLin = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨hxR, hxK⟩ := Submodule.mem_inf.mp hx
      obtain ⟨f, hf⟩ := hxR
      have hBx : P.boundaryMatrix *ᵥ x = 0 := by
        have := LinearMap.mem_ker.mp hxK
        rwa [Matrix.mulVecLin_apply] at this
      have hfx : P.boundaryMatrixᵀ *ᵥ f = x := by
        rw [← hf, Matrix.mulVecLin_apply]
      have hxx : x ⬝ᵥ x = 0 := by
        calc x ⬝ᵥ x = (P.boundaryMatrixᵀ *ᵥ f) ⬝ᵥ x := by rw [hfx]
          _ = (f ᵥ* P.boundaryMatrix) ⬝ᵥ x := by rw [Matrix.mulVec_transpose]
          _ = f ⬝ᵥ (P.boundaryMatrix *ᵥ x) :=
              (Matrix.dotProduct_mulVec f P.boundaryMatrix x).symm
          _ = f ⬝ᵥ (0 : V → ℝ) := by rw [hBx]
          _ = 0 := dotProduct_zero f
      funext e
      have hnn : ∀ e ∈ Finset.univ, (0 : ℝ) ≤ x e * x e :=
        fun e _ => mul_self_nonneg (x e)
      have hze := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hxx e
        (Finset.mem_univ e)
      exact mul_self_eq_zero.mp hze
    -- The two fill the edge space.
    have hsup : LinearMap.range P.boundaryMatrixᵀ.mulVecLin
        ⊔ LinearMap.ker P.boundaryMatrix.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq
        (LinearMap.range P.boundaryMatrixᵀ.mulVecLin)
        (LinearMap.ker P.boundaryMatrix.mulVecLin)
      rw [hdisj, finrank_bot] at hsum
      have hfin : Module.finrank ℝ
          ↥(LinearMap.range P.boundaryMatrixᵀ.mulVecLin
            ⊔ LinearMap.ker P.boundaryMatrix.mulVecLin)
          = Fintype.card ι := by omega
      rw [hfin, Module.finrank_fintype_fun_eq_card]
    -- Decompose ω.
    have hmem : ω ∈ LinearMap.range P.boundaryMatrixᵀ.mulVecLin
        ⊔ LinearMap.ker P.boundaryMatrix.mulVecLin := by
      rw [hsup]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨f, hf⟩ := hy
    have hyg : y = P.grad f := by
      rw [← hf, Matrix.mulVecLin_apply, P.transpose_boundaryMatrix_mulVec]
    have hzB : P.boundaryMatrix *ᵥ z = 0 := by
      have := LinearMap.mem_ker.mp hz
      rwa [Matrix.mulVecLin_apply] at this
    obtain ⟨a, ha⟩ := P.spanning z (fun v => by
      rw [← P.boundaryMatrix_mulVec, hzB]
      rfl)
    have hzper : ∀ j, z ⬝ᵥ P.cycles j = 0 := by
      intro j
      have hzeq : z = ω - y := eq_sub_of_add_eq' hyz
      rw [hzeq, sub_dotProduct, hper j, hyg, P.grad_period f j]
      ring
    have hzz : z ⬝ᵥ z = 0 := by
      calc z ⬝ᵥ z = z ⬝ᵥ (fun e => ∑ i, a i * P.cycles i e) := by rw [← ha]
        _ = ∑ e, z e * ∑ i, a i * P.cycles i e := rfl
        _ = ∑ e, ∑ i, a i * (z e * P.cycles i e) := by
            refine Finset.sum_congr rfl fun e _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = ∑ i, ∑ e, a i * (z e * P.cycles i e) := Finset.sum_comm
        _ = ∑ i, a i * (z ⬝ᵥ P.cycles i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.mul_sum]
            rfl
        _ = 0 := Finset.sum_eq_zero fun i _ => by rw [hzper i, mul_zero]
    have hz0 : z = 0 := by
      funext e
      have hnn : ∀ e ∈ Finset.univ, (0 : ℝ) ≤ z e * z e :=
        fun e _ => mul_self_nonneg (z e)
      have hze := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzz e
        (Finset.mem_univ e)
      exact mul_self_eq_zero.mp hze
    refine ⟨f, ?_⟩
    rw [← hyg, ← hyz, hz0, add_zero]
  · rintro ⟨f, rfl⟩ i
    exact P.grad_period f i

/-! ## The incompressible residue: cochains mod gradients ≃ periods -/

/-- The gradient as a linear map. -/
noncomputable def gradLin : (V → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun f := P.grad f
  map_add' f g := funext fun e => by
    show (f + g) (P.tgt e) - (f + g) (P.src e)
      = (f (P.tgt e) - f (P.src e)) + (g (P.tgt e) - g (P.src e))
    simp only [Pi.add_apply]
    ring
  map_smul' c f := funext fun e => by
    show (c • f) (P.tgt e) - (c • f) (P.src e)
      = c * (f (P.tgt e) - f (P.src e))
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- The period map as a linear map. -/
noncomputable def periodLin : (ι → ℝ) →ₗ[ℝ] (Fin P.r → ℝ) where
  toFun ω := fun i => ω ⬝ᵥ P.cycles i
  map_add' ω η := funext fun i => add_dotProduct ω η (P.cycles i)
  map_smul' c ω := funext fun i => smul_dotProduct c ω (P.cycles i)

/-- Exactness at the submodule level: the kernel of the period map is
exactly the image of the gradient. -/
theorem range_gradLin_eq_ker_periodLin :
    LinearMap.range P.gradLin = LinearMap.ker P.periodLin := by
  ext ω
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨f, rfl⟩
    funext i
    exact P.grad_period f i
  · intro h
    exact (P.period_eq_zero_iff_exists_grad ω).mp (fun i => congrFun h i)

/-- The period map is surjective: `periodRep` realizes every period
vector. -/
theorem periodLin_surjective : Function.Surjective P.periodLin := by
  intro k
  have hdet : IsUnit (gramOf P.cycles).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt P.gram_posDef.det_pos)
  exact ⟨periodRep P.cycles k,
    funext fun j => periodRep_periods P.cycles hdet k j⟩

/-- **The incompressible residue** (the keystone's mathematical half):
cochains modulo gradients — descriptions modulo local re-description —
are exactly the period space `ℝ^r`, via the period map. -/
noncomputable def cochainQuotEquiv :
    ((ι → ℝ) ⧸ LinearMap.range P.gradLin) ≃ₗ[ℝ] (Fin P.r → ℝ) :=
  (Submodule.quotEquivOfEq _ _ P.range_gradLin_eq_ker_periodLin).trans
    (P.periodLin.quotKerEquivOfSurjective P.periodLin_surjective)

/-- What survives quotienting by local re-description has dimension
exactly `r` — the chosen cycle rank is the incompressible residue. -/
theorem finrank_cochainQuot :
    Module.finrank ℝ ((ι → ℝ) ⧸ LinearMap.range P.gradLin) = P.r := by
  rw [P.cochainQuotEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]

end CyclePresentation

/-! ## Instances: the cycle graph and the wedge -/

/-- The cycle graph `C_n` as a presentation: edges `e : e → e + 1`,
one basis cycle (all ones). -/
noncomputable def cyclePresentation (n : ℕ) (hn : 0 < n) :
    CyclePresentation (Fin n) (Fin n) :=
  haveI : NeZero n := ⟨hn.ne'⟩
  { src := fun e => e
    tgt := fun e => e + 1
    r := 1
    cycles := cycleAllOnes n
    cycles_closed := fun _ v => cycleBoundary_allOnes n v
    spanning := fun ω hω => by
      refine ⟨![ω 0], ?_⟩
      have h := eq_smul_allOnes_of_cycleBoundary_eq_zero n ω (fun v => hω v)
      funext e
      rw [congrFun h e, Fin.sum_univ_one]
      rfl
    gram_posDef := by
      rw [gramOf_cycleAllOnes]
      exact posDef_fin_one _ (by exact_mod_cast hn) }

/-- The wedge of two cycles as a presentation: the Phase-21 graph,
two disjoint-support basis cycles. -/
noncomputable def wedgePresentation (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    CyclePresentation (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) :=
  haveI : NeZero n₁ := ⟨h₁.ne'⟩
  haveI : NeZero n₂ := ⟨h₂.ne'⟩
  { src := wedgeSrc n₁ n₂
    tgt := wedgeTgt n₁ n₂
    r := 2
    cycles := wedgeCycles n₁ n₂
    cycles_closed := fun i v => wedgeBoundary_cycles n₁ n₂ i v
    spanning := fun ω hω => by
      refine ⟨![ω (Sum.inl 0), ω (Sum.inr 0)], ?_⟩
      have h := eq_comb_of_wedgeBoundary_eq_zero n₁ n₂ ω (fun v => hω v)
      funext e
      rw [congrFun h e, Fin.sum_univ_two]
      rfl
    gram_posDef := gramOf_wedgeCycles_posDef n₁ n₂ h₁ h₂ }

end Meno
