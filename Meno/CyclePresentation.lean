import Meno.IncidenceGraph
import Meno.PeriodHarmonic

/-! # Cycle Presentation: a graph with a chosen cycle basis

The general home for the graph-level facts that Phases 18–21 proved
per instance, refactored in Phase 29 (Completion Path C1) to present
an `IncidenceGraph` rather than carry its own edge data. A
`CyclePresentation G` is a **chosen** family of cycle vectors on the
graph `G` that is closed (zero boundary), spans the cycle space, and
has positive-definite chain Gram matrix. The boundary, gradient, and
discrete Stokes live on `G` (`Meno/IncidenceGraph.lean`) — defined
once, over any commutative ring.

From this data alone:

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

**Chosen basis, invariant physics**: `k ∈ ℤ^r` means periods *against
this basis* — the label is basis-relative. The `GL(r, ℤ)` gate for
coordinate-independence claims is closed (Phase 23): `rebase` carries
a presentation to any unimodularly recombined basis, `rebase_energy`
shows energies are invariant under the relabeling `k ↦ Uk`, and
`rebase_partFn` shows the partition function does not move at all.
Matter transport is `MatterSector.rebaseEquiv` (`Meno/Matter.lean`). -/

namespace Meno

open scoped BigOperators
open Matrix

universe u v

/-- A chosen cycle basis on the graph `G`: `r` closed cycle vectors
spanning the cycle space, with positive-definite chain Gram matrix. -/
structure CyclePresentation (G : IncidenceGraph.{u, v}) where
  /-- Number of basis cycles (the intended `b₁`). -/
  r : ℕ
  /-- The chosen cycle vectors. -/
  cycles : Fin r → G.E → ℝ
  /-- Each basis vector is a cycle: zero boundary at every vertex. -/
  cycles_closed : ∀ i v, G.boundary (cycles i) v = 0
  /-- The basis spans the cycle space. -/
  spanning : ∀ ω : G.E → ℝ, (∀ v, G.boundary ω v = 0) →
    ∃ a : Fin r → ℝ, ω = fun e => ∑ i, a i * cycles i e
  /-- The chain Gram matrix is positive definite (in particular the
  cycles are linearly independent). The basis is *chosen*: sector
  labels are basis-relative, physics is not (`rebase_energy`,
  `rebase_partFn`). -/
  gram_posDef : (gramOf cycles).PosDef

namespace CyclePresentation

variable {G : IncidenceGraph.{u, v}} (P : CyclePresentation G)

/-- The harmonic Gram data of the presentation, through the Phase-20
builder: Gram form is the inverse chain Gram, and the variational
identity holds by `HarmonicGramData.ofCycles_energy_isLeast`. -/
noncomputable def toGramData : HarmonicGramData G.V :=
  HarmonicGramData.ofCycles (V := G.V) P.cycles P.gram_posDef

/-- Gradients have vanishing periods: local re-description is
invisible to the sectors. -/
theorem grad_period (f : G.V → ℝ) (i : Fin P.r) :
    G.grad f ⬝ᵥ P.cycles i = 0 := by
  rw [G.grad_dotProduct_eq]
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
theorem period_eq_zero_iff_exists_grad (ω : G.E → ℝ) :
    (∀ i, ω ⬝ᵥ P.cycles i = 0) ↔ ∃ f : G.V → ℝ, G.grad f = ω := by
  constructor
  · intro hper
    classical
    -- Dimension bookkeeping.
    have hrank : Module.finrank ℝ
          (LinearMap.range (G.boundaryMatrix ℝ)ᵀ.mulVecLin)
        + Module.finrank ℝ (LinearMap.ker (G.boundaryMatrix ℝ).mulVecLin)
        = Fintype.card G.E := by
      have h1 : Module.finrank ℝ
            (LinearMap.range (G.boundaryMatrix ℝ)ᵀ.mulVecLin)
          = (G.boundaryMatrix ℝ)ᵀ.rank := rfl
      have h2 : (G.boundaryMatrix ℝ)ᵀ.rank = (G.boundaryMatrix ℝ).rank :=
        Matrix.rank_transpose (G.boundaryMatrix ℝ)
      have h3 := LinearMap.finrank_range_add_finrank_ker
        (G.boundaryMatrix ℝ).mulVecLin
      rw [Module.finrank_fintype_fun_eq_card] at h3
      rw [h1, h2]
      exact h3
    -- Trivial intersection.
    have hdisj : LinearMap.range (G.boundaryMatrix ℝ)ᵀ.mulVecLin
        ⊓ LinearMap.ker (G.boundaryMatrix ℝ).mulVecLin = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨hxR, hxK⟩ := Submodule.mem_inf.mp hx
      obtain ⟨f, hf⟩ := hxR
      have hBx : G.boundaryMatrix ℝ *ᵥ x = 0 := by
        have := LinearMap.mem_ker.mp hxK
        rwa [Matrix.mulVecLin_apply] at this
      have hfx : (G.boundaryMatrix ℝ)ᵀ *ᵥ f = x := by
        rw [← hf, Matrix.mulVecLin_apply]
      have hxx : x ⬝ᵥ x = 0 := by
        calc x ⬝ᵥ x = ((G.boundaryMatrix ℝ)ᵀ *ᵥ f) ⬝ᵥ x := by rw [hfx]
          _ = (f ᵥ* G.boundaryMatrix ℝ) ⬝ᵥ x := by rw [Matrix.mulVec_transpose]
          _ = f ⬝ᵥ (G.boundaryMatrix ℝ *ᵥ x) :=
              (Matrix.dotProduct_mulVec f (G.boundaryMatrix ℝ) x).symm
          _ = f ⬝ᵥ (0 : G.V → ℝ) := by rw [hBx]
          _ = 0 := dotProduct_zero f
      funext e
      have hnn : ∀ e ∈ Finset.univ, (0 : ℝ) ≤ x e * x e :=
        fun e _ => mul_self_nonneg (x e)
      have hze := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hxx e
        (Finset.mem_univ e)
      exact mul_self_eq_zero.mp hze
    -- The two fill the edge space.
    have hsup : LinearMap.range (G.boundaryMatrix ℝ)ᵀ.mulVecLin
        ⊔ LinearMap.ker (G.boundaryMatrix ℝ).mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq
        (LinearMap.range (G.boundaryMatrix ℝ)ᵀ.mulVecLin)
        (LinearMap.ker (G.boundaryMatrix ℝ).mulVecLin)
      rw [hdisj, finrank_bot] at hsum
      have hfin : Module.finrank ℝ
          ↥(LinearMap.range (G.boundaryMatrix ℝ)ᵀ.mulVecLin
            ⊔ LinearMap.ker (G.boundaryMatrix ℝ).mulVecLin)
          = Fintype.card G.E := by omega
      rw [hfin, Module.finrank_fintype_fun_eq_card]
    -- Decompose ω.
    have hmem : ω ∈ LinearMap.range (G.boundaryMatrix ℝ)ᵀ.mulVecLin
        ⊔ LinearMap.ker (G.boundaryMatrix ℝ).mulVecLin := by
      rw [hsup]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨f, hf⟩ := hy
    have hyg : y = G.grad f := by
      rw [← hf, Matrix.mulVecLin_apply, G.transpose_boundaryMatrix_mulVec]
    have hzB : G.boundaryMatrix ℝ *ᵥ z = 0 := by
      have := LinearMap.mem_ker.mp hz
      rwa [Matrix.mulVecLin_apply] at this
    obtain ⟨a, ha⟩ := P.spanning z (fun v => by
      rw [← G.boundaryMatrix_mulVec, hzB]
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

/-- The period map as a linear map. -/
noncomputable def periodLin : (G.E → ℝ) →ₗ[ℝ] (Fin P.r → ℝ) where
  toFun ω := fun i => ω ⬝ᵥ P.cycles i
  map_add' ω η := funext fun i => add_dotProduct ω η (P.cycles i)
  map_smul' c ω := funext fun i => smul_dotProduct c ω (P.cycles i)

/-- Exactness at the submodule level: the kernel of the period map is
exactly the image of the gradient. -/
theorem range_gradLin_eq_ker_periodLin :
    LinearMap.range (G.gradLin ℝ) = LinearMap.ker P.periodLin := by
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
are exactly the period space `ℝ^r`, via the period map. Note the
quotient depends only on the graph; the presentation supplies the
coordinates. -/
noncomputable def cochainQuotEquiv :
    ((G.E → ℝ) ⧸ LinearMap.range (G.gradLin ℝ)) ≃ₗ[ℝ] (Fin P.r → ℝ) :=
  (Submodule.quotEquivOfEq _ _ P.range_gradLin_eq_ker_periodLin).trans
    (P.periodLin.quotKerEquivOfSurjective P.periodLin_surjective)

/-- What survives quotienting by local re-description has dimension
exactly `r` — the chosen cycle rank is the incompressible residue. -/
theorem finrank_cochainQuot :
    Module.finrank ℝ ((G.E → ℝ) ⧸ LinearMap.range (G.gradLin ℝ)) = P.r := by
  rw [P.cochainQuotEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]

/-- **The parameter split**: describing a cochain takes `rank ∂`
re-describable (gauge) parameters plus exactly `r` incompressible
ones. The counting shadow of the incompressible-residue equivalence —
and the ℝ-dimensional form of the keystone's description-cost split. -/
theorem card_edges_eq_finrank_gauge_add_r :
    Fintype.card G.E
      = Module.finrank ℝ (LinearMap.range (G.gradLin ℝ)) + P.r := by
  have h := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (G.gradLin ℝ))
  rw [P.finrank_cochainQuot, Module.finrank_fintype_fun_eq_card] at h
  omega

/-- **Euler's formula for presentations**: the cycle rank is the edge
count minus vertex count plus component count. Combines the parameter
split, rank–nullity for the gradient, and the gauge theorem (C1). -/
theorem r_eq_card_edges_sub_card_vertices_add_components :
    (P.r : ℤ) = (Fintype.card G.E : ℤ) - Fintype.card G.V
      + G.componentCard := by
  have hsplit := P.card_edges_eq_finrank_gauge_add_r
  have hrn := LinearMap.finrank_range_add_finrank_ker (G.gradLin ℝ)
  rw [Module.finrank_fintype_fun_eq_card, G.finrank_gauge] at hrn
  omega

end CyclePresentation

/-! ## Unimodular change of basis: the gate, closed

A change of cycle basis by `U ∈ GL(r, ℤ)` relabels sectors `k ↦ Uk`,
transforms the chain Gram by congruence `C ↦ U C Uᵀ` — and changes
nothing physical: energies are invariant under the relabeling
(`rebase_energy`), and the partition function is invariant outright
(`rebase_partFn`). Matter transport lives in `Meno/Matter.lean`. -/

section Rebase

/-- Multiplication by an integer matrix with unit determinant is a
bijection of the sector lattice `ℤ^n`. -/
noncomputable def mulVecEquiv {n : ℕ} (U : Matrix (Fin n) (Fin n) ℤ)
    (hU : IsUnit U.det) : (Fin n → ℤ) ≃ (Fin n → ℤ) where
  toFun k := U *ᵥ k
  invFun k := U⁻¹ *ᵥ k
  left_inv k := by
    show U⁻¹ *ᵥ (U *ᵥ k) = k
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
  right_inv k := by
    show U *ᵥ (U⁻¹ *ᵥ k) = k
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]

/-- Unit determinant survives the cast to `ℝ`. -/
private lemma isUnit_det_map {n : ℕ} (U : Matrix (Fin n) (Fin n) ℤ)
    (hU : IsUnit U.det) : IsUnit (U.map (Int.cast : ℤ → ℝ)).det := by
  have h := RingHom.map_det (Int.castRingHom ℝ) U
  rw [RingHom.mapMatrix_apply] at h
  rw [show U.map (Int.cast : ℤ → ℝ) = U.map ⇑(Int.castRingHom ℝ) from rfl, ← h]
  exact hU.map (Int.castRingHom ℝ)

/-- Casting commutes with the lattice action: the real coordinates of
`U *ᵥ k` are `Uℝ *ᵥ kℝ`. -/
private lemma cast_mulVec {n : ℕ} (U : Matrix (Fin n) (Fin n) ℤ)
    (k : Fin n → ℤ) :
    (fun i => ((U.mulVec k) i : ℝ))
      = (U.map (Int.cast : ℤ → ℝ)).mulVec (fun j => (k j : ℝ)) := by
  funext i
  show ((∑ j, U i j * k j : ℤ) : ℝ) = ∑ j, (U i j : ℝ) * (k j : ℝ)
  push_cast
  rfl

/-- Congruence preserves positive-definiteness (over `ℝ`, with
invertible congruence matrix). -/
private lemma posDef_mul_mul_transpose {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (U : Matrix (Fin n) (Fin n) ℝ) (hU : IsUnit U.det) :
    (U * A * Uᵀ).PosDef := by
  have hct : ∀ (X : Matrix (Fin n) (Fin n) ℝ), Xᴴ = Xᵀ := fun X => by
    ext p q
    show star (X q p) = X q p
    exact star_trivial _
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · have hAH : Aᴴ = A := (posDef_iff_dotProduct_mulVec.mp hA).1
    calc (U * A * Uᵀ)ᴴ
        = (Uᵀ)ᴴ * (U * A)ᴴ := Matrix.conjTranspose_mul _ _
      _ = (Uᵀ)ᴴ * (Aᴴ * Uᴴ) := by rw [Matrix.conjTranspose_mul]
      _ = U * (A * Uᵀ) := by
          rw [hAH, hct, hct, Matrix.transpose_transpose]
      _ = U * A * Uᵀ := (Matrix.mul_assoc U A Uᵀ).symm
  · have hUT : IsUnit Uᵀ.det := by rwa [Matrix.det_transpose]
    have hy : Uᵀ *ᵥ x ≠ 0 := by
      intro h0
      apply hx
      have hinv : (Uᵀ)⁻¹ *ᵥ (Uᵀ *ᵥ x) = x := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hUT,
          Matrix.one_mulVec]
      rw [← hinv, h0, Matrix.mulVec_zero]
    have hpos := (posDef_iff_dotProduct_mulVec.mp hA).2 hy
    have hsy : star (Uᵀ *ᵥ x) = Uᵀ *ᵥ x := funext fun i => star_trivial _
    rw [hsy] at hpos
    have hsx : star x = x := funext fun i => star_trivial _
    rw [hsx]
    calc x ⬝ᵥ ((U * A * Uᵀ) *ᵥ x)
        = x ⬝ᵥ (U *ᵥ ((A * Uᵀ) *ᵥ x)) := by
          rw [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = (x ᵥ* U) ⬝ᵥ ((A * Uᵀ) *ᵥ x) := Matrix.dotProduct_mulVec x U _
      _ = (Uᵀ *ᵥ x) ⬝ᵥ (A *ᵥ (Uᵀ *ᵥ x)) := by
          rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec]
      _ > 0 := hpos

/-- Gram matrix of an integer-recombined family: congruence by the
cast of the recombination matrix. -/
private lemma gramOf_map_mul {ι : Type v} [Fintype ι] {r : ℕ}
    (U : Matrix (Fin r) (Fin r) ℤ)
    (c : Fin r → ι → ℝ) :
    gramOf (fun i e => ∑ j, (U i j : ℝ) * c j e)
      = U.map (Int.cast : ℤ → ℝ) * gramOf c
        * (U.map (Int.cast : ℤ → ℝ))ᵀ := by
  ext i j
  have hRHS : (U.map (Int.cast : ℤ → ℝ) * gramOf c
        * (U.map (Int.cast : ℤ → ℝ))ᵀ) i j
      = ∑ b, ∑ a, (U i a : ℝ) * gramOf c a b * (U j b : ℝ) := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.map_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hRHS]
  show (fun e => ∑ a, (U i a : ℝ) * c a e) ⬝ᵥ (fun e => ∑ b, (U j b : ℝ) * c b e)
    = ∑ b, ∑ a, (U i a : ℝ) * gramOf c a b * (U j b : ℝ)
  calc (fun e => ∑ a, (U i a : ℝ) * c a e)
        ⬝ᵥ (fun e => ∑ b, (U j b : ℝ) * c b e)
      = ∑ e, ∑ a, ∑ b, ((U i a : ℝ) * c a e) * ((U j b : ℝ) * c b e) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_mul_sum]
    _ = ∑ a, ∑ e, ∑ b, ((U i a : ℝ) * c a e) * ((U j b : ℝ) * c b e) :=
        Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ e, ((U i a : ℝ) * c a e) * ((U j b : ℝ) * c b e) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Finset.sum_comm
    _ = ∑ a, ∑ b, (U i a : ℝ) * gramOf c a b * (U j b : ℝ) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        show _ = (U i a : ℝ) * (∑ e, c a e * c b e) * (U j b : ℝ)
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun e _ => by ring
    _ = ∑ b, ∑ a, (U i a : ℝ) * gramOf c a b * (U j b : ℝ) := Finset.sum_comm

/-- The boundary of an `ℝ`-combination of cochains is the combination
of the boundaries. -/
private lemma flowBoundary_comb {V : Type u} {ι : Type v} [Fintype ι]
    [DecidableEq V] {r' : ℕ} (src tgt : ι → V)
    (a : Fin r' → ℝ) (c : Fin r' → ι → ℝ) (v : V) :
    flowBoundary src tgt (fun e => ∑ j, a j * c j e) v
      = ∑ j, a j * flowBoundary src tgt (c j) v := by
  unfold flowBoundary
  calc ∑ e, ((if tgt e = v then (1 : ℝ) else 0)
        - (if src e = v then (1 : ℝ) else 0)) * ∑ j, a j * c j e
      = ∑ e, ∑ j, a j * (((if tgt e = v then (1 : ℝ) else 0)
          - (if src e = v then (1 : ℝ) else 0)) * c j e) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j, ∑ e, a j * (((if tgt e = v then (1 : ℝ) else 0)
          - (if src e = v then (1 : ℝ) else 0)) * c j e) := Finset.sum_comm
    _ = ∑ j, a j * ∑ e, ((if tgt e = v then (1 : ℝ) else 0)
          - (if src e = v then (1 : ℝ) else 0)) * c j e := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]

namespace CyclePresentation

variable {G : IncidenceGraph.{u, v}} (P : CyclePresentation G)
variable (U : Matrix (Fin P.r) (Fin P.r) ℤ) (hU : IsUnit U.det)

/-- **Re-basing**: the same graph presented with the unimodularly
recombined cycle basis `cᵢ' = Σⱼ Uᵢⱼ cⱼ`. -/
noncomputable def rebase : CyclePresentation G where
  r := P.r
  cycles := fun i e => ∑ j, (U i j : ℝ) * P.cycles j e
  cycles_closed := fun i v => by
    show flowBoundary G.src G.tgt
      (fun e => ∑ j, (U i j : ℝ) * P.cycles j e) v = 0
    rw [flowBoundary_comb]
    exact Finset.sum_eq_zero fun j _ => by
      rw [show flowBoundary G.src G.tgt (P.cycles j) v
          = G.boundary (P.cycles j) v from rfl,
        P.cycles_closed j v, mul_zero]
  spanning := fun ω hω => by
    obtain ⟨a, ha⟩ := P.spanning ω hω
    refine ⟨a ᵥ* (U.map (Int.cast : ℤ → ℝ))⁻¹, ?_⟩
    have hb : (a ᵥ* (U.map (Int.cast : ℤ → ℝ))⁻¹)
        ᵥ* (U.map (Int.cast : ℤ → ℝ)) = a := by
      rw [Matrix.vecMul_vecMul,
        Matrix.nonsing_inv_mul _ (isUnit_det_map U hU), Matrix.vecMul_one]
    rw [ha]
    funext e
    calc ∑ j, a j * P.cycles j e
        = ∑ j, ((a ᵥ* (U.map (Int.cast : ℤ → ℝ))⁻¹)
            ᵥ* (U.map (Int.cast : ℤ → ℝ))) j * P.cycles j e := by rw [hb]
      _ = ∑ j, (∑ i, (a ᵥ* (U.map (Int.cast : ℤ → ℝ))⁻¹) i * (U i j : ℝ))
            * P.cycles j e := rfl
      _ = ∑ j, ∑ i, (a ᵥ* (U.map (Int.cast : ℤ → ℝ))⁻¹) i
            * ((U i j : ℝ) * P.cycles j e) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∑ j, (a ᵥ* (U.map (Int.cast : ℤ → ℝ))⁻¹) i
            * ((U i j : ℝ) * P.cycles j e) := Finset.sum_comm
      _ = ∑ i, (a ᵥ* (U.map (Int.cast : ℤ → ℝ))⁻¹) i
            * ∑ j, (U i j : ℝ) * P.cycles j e := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
  gram_posDef := by
    show (gramOf (fun i e => ∑ j, (U i j : ℝ) * P.cycles j e)).PosDef
    rw [gramOf_map_mul]
    exact posDef_mul_mul_transpose (gramOf P.cycles) P.gram_posDef
      (U.map (Int.cast : ℤ → ℝ)) (isUnit_det_map U hU)

/-- Re-basing preserves the rank. -/
theorem rebase_r : (P.rebase U hU).r = P.r := rfl

/-- **Energy is basis-invariant**: the sector labeled `k` in the old
basis is labeled `Uk` in the new one, and its energy is unchanged. -/
theorem rebase_energy (k : Fin P.r → ℤ) :
    (P.rebase U hU).toGramData.energy (U.mulVec k)
      = P.toGramData.energy k := by
  have hUℝ := isUnit_det_map U hU
  show ∑ i, ∑ j, (gramOf (fun i e => ∑ j, (U i j : ℝ) * P.cycles j e))⁻¹ i j
      * ((U.mulVec k) i : ℝ) * ((U.mulVec k) j : ℝ)
    = ∑ i, ∑ j, (gramOf P.cycles)⁻¹ i j * (k i : ℝ) * (k j : ℝ)
  rw [quadForm_dotProduct, quadForm_dotProduct, gramOf_map_mul, cast_mulVec]
  have hcollapse : (U.map (Int.cast : ℤ → ℝ))⁻¹
      *ᵥ ((U.map (Int.cast : ℤ → ℝ)) *ᵥ (fun j => (k j : ℝ)))
      = fun j => (k j : ℝ) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hUℝ,
      Matrix.one_mulVec]
  have hinv : (U.map (Int.cast : ℤ → ℝ) * gramOf P.cycles
        * (U.map (Int.cast : ℤ → ℝ))ᵀ)⁻¹
      = ((U.map (Int.cast : ℤ → ℝ))ᵀ)⁻¹
        * ((gramOf P.cycles)⁻¹ * (U.map (Int.cast : ℤ → ℝ))⁻¹) := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have hkey : (U.map (Int.cast : ℤ → ℝ) * gramOf P.cycles
        * (U.map (Int.cast : ℤ → ℝ))ᵀ)⁻¹
        *ᵥ ((U.map (Int.cast : ℤ → ℝ)) *ᵥ (fun j => (k j : ℝ)))
      = ((U.map (Int.cast : ℤ → ℝ))ᵀ)⁻¹
        *ᵥ ((gramOf P.cycles)⁻¹ *ᵥ (fun j => (k j : ℝ))) := by
    rw [hinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcollapse]
  rw [hkey, Matrix.dotProduct_mulVec, ← Matrix.transpose_nonsing_inv,
    ← Matrix.mulVec_transpose, Matrix.transpose_transpose, hcollapse]

/-- **The partition function is basis-invariant**: re-basing permutes
the sector lattice, and the Boltzmann sum does not see the labels. -/
theorem rebase_partFn :
    (P.rebase U hU).toGramData.toQuadraticAction.toSectorAction.partFn
      = P.toGramData.toQuadraticAction.toSectorAction.partFn := by
  show ∑' k : Fin P.r → ℤ,
      Real.exp (-((P.rebase U hU).toGramData.energy k))
    = ∑' k : Fin P.r → ℤ, Real.exp (-(P.toGramData.energy k))
  rw [← Equiv.tsum_eq (mulVecEquiv U hU)
    (fun k => Real.exp (-((P.rebase U hU).toGramData.energy k)))]
  refine tsum_congr fun k => ?_
  show Real.exp (-((P.rebase U hU).toGramData.energy (U.mulVec k)))
    = Real.exp (-(P.toGramData.energy k))
  rw [P.rebase_energy U hU k]

end CyclePresentation

end Rebase

/-! ## Instances: the cycle graph -/

/-- The cycle graph `C_n` as a presentation: one basis cycle (all
ones) on `cycleGraph n`. -/
@[reducible] noncomputable def cyclePresentation (n : ℕ) (hn : 0 < n) :
    CyclePresentation (cycleGraph n hn) :=
  haveI : NeZero n := ⟨hn.ne'⟩
  { r := 1
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

/-! ## Integral primitivity

The chosen bases are *primitive*: an integer-valued cochain with zero
boundary is an **integer** combination of the basis cycles — the
period lattice is the full integral cycle lattice, not a finite-index
sublattice. This is inherited from the real spanning proofs, whose
coefficients are evaluations of the cochain itself. (The wedge's
instance lives with its genuine graph in
`Meno/WedgePresentation.lean`; C3's `exists_int_coords` proves
primitivity for every integral presentation.)

Primitivity is the load-bearing hypothesis of the keystone's
finite-resolution form (see PLAN, Phase 24): it is what makes the
mod-`q` period map surjective, hence the compression residue exactly
`b₁` resolution-digits. The theta instance lives in
`Meno/ThetaHarmonic.lean`. -/

/-- The cycle graph's all-ones basis is integrally primitive. -/
theorem cycle_integral_spanning (n : ℕ) [NeZero n] (ω : Fin n → ℤ)
    (h : ∀ v, cycleBoundary n (fun e => (ω e : ℝ)) v = 0) :
    ∃ a : Fin 1 → ℤ, ∀ e, (ω e : ℝ) = ∑ i, (a i : ℝ) * cycleAllOnes n i e := by
  refine ⟨![ω 0], fun e => ?_⟩
  have hr := eq_smul_allOnes_of_cycleBoundary_eq_zero n
    (fun e => (ω e : ℝ)) h
  calc (ω e : ℝ) = (ω 0 : ℝ) * cycleAllOnes n 0 e := congrFun hr e
    _ = ∑ i, ((![ω 0] : Fin 1 → ℤ) i : ℝ) * cycleAllOnes n i e := by
        rw [Fin.sum_univ_one]
        rfl


end Meno
