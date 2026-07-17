import Meno.PeriodLattice

/-! # The Fundamental Presentation (C2)

**Every finite incidence graph carries an integral cycle
presentation** — the Completion Path's C2, retiring the review's
central conditionality: `IntegralCyclePresentation`'s fields
(`periods_onto`, `integral_potentials`) stop being per-instance
obligations and become theorems available for every finite graph.

The construction:

* `cycleLattice` — `H₁(G;ℤ) := ker ∂ℤ`, the integral cycle lattice.
  It is **saturated** (`mem_of_smul_mem`): the quotient by it is
  torsion-free, hence free over `ℤ`, hence projective — so the
  quotient map splits (`quotSection`) and the ambient lattice
  **retracts** onto the cycle lattice (`cycleRetract`).
* `cycleBasis` — a `ℤ`-basis of the cycle lattice via the PID
  structure theorem (`Submodule.basisOfPid`); its rank is the first
  Betti number `b1`.
* `coordMap` — basis coordinates extended to all of `ℤ^E` along the
  retraction. This single integer matrix `P` with `P Cᵀ = 1` powers
  three fields at once: **independence** of the cast basis (apply
  `P̂` over `ℝ`), hence the **positive-definite Gram**; and
  **period surjectivity** (`τ := Pᵀ k`).
* Walk integration (`Meno/IncidenceGraph.lean`) powers the other two:
  a cochain with vanishing periods against the basis kills every
  closed-walk sum (`closedWalkSum_eq_zero` — the basis spans the
  lattice, and chains of closed walks lie in it), so integrating
  along chosen walks produces a potential — over `ℤ` this is
  `integral_potentials`; over `ℝ`, combined with the Gram inverse as
  a concrete orthogonal projection, it yields **spanning**.

Consumers (the "for any presented graph → for any finite graph"
upgrades): `h1QuotEquiv` (integer cochains modulo integer gradients
are `ℤ^{b₁}` — intrinsic `H¹` coordinates), `b1_eq` (Euler's formula
`b₁ = |E| − |V| + c`); `card_quotient_eq` (K1 at every resolution,
for every finite graph) lives downstream in
`Meno/ResolutionCount.lean`, keeping this file in the topology
layer. -/

namespace Meno

open scoped BigOperators
open Matrix

universe u v

namespace IncidenceGraph

variable (G : IncidenceGraph.{u, v})

/-! ## The integral cycle lattice `H₁(G;ℤ)` -/

/-- The integral cycle lattice: `H₁(G;ℤ) = ker ∂ℤ`. -/
def cycleLattice : Submodule ℤ (G.E → ℤ) := LinearMap.ker (G.boundaryLin ℤ)

theorem mem_cycleLattice {ω : G.E → ℤ} :
    ω ∈ G.cycleLattice ↔ ∀ v, G.boundary ω v = 0 := by
  rw [cycleLattice, LinearMap.mem_ker]
  constructor
  · intro h v
    exact congrFun h v
  · intro h
    funext v
    exact h v

/-- Chains of closed walks are cycles. -/
theorem chain_mem_cycleLattice {w : G.V} (c : G.Walk w w) :
    c.chain ℤ ∈ G.cycleLattice :=
  G.mem_cycleLattice.mpr (Walk.boundary_chain_closed c)

/-- **Saturation**: the cycle lattice is division-closed — a multiple
of a cochain is a cycle only if the cochain is. This is where
torsion-freeness of `ℤ^E ⧸ H₁` comes from. -/
theorem mem_of_smul_mem {c : ℤ} (hc : c ≠ 0) {x : G.E → ℤ}
    (h : c • x ∈ G.cycleLattice) : x ∈ G.cycleLattice := by
  rw [mem_cycleLattice] at h ⊢
  intro v
  have hv := h v
  rw [G.boundary_smul] at hv
  rcases mul_eq_zero.mp hv with h0 | h0
  · exact absurd h0 hc
  · exact h0

instance : NoZeroSMulDivisors ℤ ((G.E → ℤ) ⧸ G.cycleLattice) := by
  refine ⟨fun {c x} h => ?_⟩
  rcases eq_or_ne c 0 with rfl | hc
  · exact Or.inl rfl
  · refine Or.inr ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    rw [Submodule.Quotient.mk_eq_zero]
    exact G.mem_of_smul_mem hc h

instance : Module.Finite ℤ ((G.E → ℤ) ⧸ G.cycleLattice) :=
  Module.Finite.of_surjective G.cycleLattice.mkQ
    (Submodule.Quotient.mk_surjective _)

instance : Module.Free ℤ ((G.E → ℤ) ⧸ G.cycleLattice) :=
  Module.free_of_finite_type_torsion_free'

/-! ## The splitting and the retraction -/

/-- A `ℤ`-linear section of the quotient map, from projectivity of
the free quotient. -/
noncomputable def quotSection :
    ((G.E → ℤ) ⧸ G.cycleLattice) →ₗ[ℤ] (G.E → ℤ) :=
  (Module.projective_lifting_property G.cycleLattice.mkQ LinearMap.id
    (Submodule.Quotient.mk_surjective _)).choose

theorem mkQ_comp_quotSection :
    G.cycleLattice.mkQ ∘ₗ G.quotSection = LinearMap.id :=
  (Module.projective_lifting_property G.cycleLattice.mkQ LinearMap.id
    (Submodule.Quotient.mk_surjective _)).choose_spec

/-- The retraction of `ℤ^E` onto the cycle lattice along the chosen
splitting. -/
noncomputable def cycleRetract : (G.E → ℤ) →ₗ[ℤ] (G.E → ℤ) :=
  LinearMap.id - G.quotSection ∘ₗ G.cycleLattice.mkQ

theorem cycleRetract_mem (x : G.E → ℤ) :
    G.cycleRetract x ∈ G.cycleLattice := by
  have h := LinearMap.congr_fun G.mkQ_comp_quotSection (G.cycleLattice.mkQ x)
  have hz : G.cycleLattice.mkQ (G.cycleRetract x) = 0 := by
    show G.cycleLattice.mkQ (x - G.quotSection (G.cycleLattice.mkQ x)) = 0
    rw [map_sub, show G.cycleLattice.mkQ (G.quotSection (G.cycleLattice.mkQ x))
        = G.cycleLattice.mkQ x from h, sub_self]
  rwa [← Submodule.ker_mkQ G.cycleLattice, LinearMap.mem_ker]

theorem cycleRetract_of_mem {x : G.E → ℤ} (hx : x ∈ G.cycleLattice) :
    G.cycleRetract x = x := by
  show x - G.quotSection (G.cycleLattice.mkQ x) = x
  rw [show G.cycleLattice.mkQ x = 0 from by
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero],
    map_zero, sub_zero]

/-! ## The fundamental cycle basis and its coordinates -/

/-- The chosen basis package of the cycle lattice, via the PID
structure theorem. -/
noncomputable def cycleBasisSigma :
    (n : ℕ) × Module.Basis (Fin n) ℤ G.cycleLattice :=
  Submodule.basisOfPid (Pi.basisFun ℤ G.E) G.cycleLattice

/-- The first Betti number: the rank of the integral cycle lattice. -/
noncomputable def b1 : ℕ := G.cycleBasisSigma.1

/-- The chosen fundamental cycle basis of `H₁(G;ℤ)`. -/
noncomputable def cycleBasis : Module.Basis (Fin G.b1) ℤ G.cycleLattice :=
  G.cycleBasisSigma.2

/-- The fundamental integer cycles, as cochains. -/
noncomputable def fundCyclesZ : Fin G.b1 → G.E → ℤ :=
  fun i => (G.cycleBasis i : G.E → ℤ)

/-- The fundamental cycles, cast to `ℝ`. -/
noncomputable def fundCyclesR : Fin G.b1 → G.E → ℝ :=
  fun i e => ((G.fundCyclesZ i e : ℤ) : ℝ)

theorem fundCyclesZ_mem (i : Fin G.b1) :
    G.fundCyclesZ i ∈ G.cycleLattice := (G.cycleBasis i).2

/-- Basis coordinates extended to the ambient lattice along the
retraction: the integer matrix `P` with `P Cᵀ = 1`. -/
noncomputable def coordMap : (G.E → ℤ) →ₗ[ℤ] (Fin G.b1 → ℤ) :=
  (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin G.b1)).toLinearMap
    ∘ₗ G.cycleBasis.repr.toLinearMap
    ∘ₗ LinearMap.codRestrict G.cycleLattice G.cycleRetract G.cycleRetract_mem

theorem coordMap_fundCyclesZ (i : Fin G.b1) :
    G.coordMap (G.fundCyclesZ i) = Pi.single i 1 := by
  have hfix : LinearMap.codRestrict G.cycleLattice G.cycleRetract
      G.cycleRetract_mem (G.fundCyclesZ i) = G.cycleBasis i := by
    apply Subtype.ext
    show G.cycleRetract (G.fundCyclesZ i) = (G.cycleBasis i : G.E → ℤ)
    exact G.cycleRetract_of_mem (G.fundCyclesZ_mem i)
  show (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin G.b1))
      (G.cycleBasis.repr (LinearMap.codRestrict G.cycleLattice G.cycleRetract
        G.cycleRetract_mem (G.fundCyclesZ i))) = Pi.single i 1
  rw [hfix, Module.Basis.repr_self]
  funext j
  rcases eq_or_ne j i with h | h
  · subst h
    show Finsupp.single j (1 : ℤ) j = (Pi.single j 1 : Fin G.b1 → ℤ) j
    rw [Finsupp.single_eq_same, Pi.single_eq_same]
  · show Finsupp.single i (1 : ℤ) j = (Pi.single i 1 : Fin G.b1 → ℤ) j
    rw [Finsupp.single_eq_of_ne h, Pi.single_eq_of_ne h]

/-- The coordinate matrix of `coordMap` in the standard bases. -/
noncomputable def coordMatrix : Matrix (Fin G.b1) G.E ℤ :=
  LinearMap.toMatrix' G.coordMap

theorem coordMatrix_mulVec (x : G.E → ℤ) :
    G.coordMatrix *ᵥ x = G.coordMap x := by
  rw [coordMatrix, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

/-! ## Cast bookkeeping -/

private lemma cast_mulVec_apply {α : Type*} (M : Matrix α G.E ℤ)
    (x : G.E → ℤ) (i : α) :
    (((M *ᵥ x) i : ℤ) : ℝ)
      = ((M.map (Int.cast : ℤ → ℝ)) *ᵥ (fun e => ((x e : ℤ) : ℝ))) i := by
  show ((∑ e, M i e * x e : ℤ) : ℝ) = ∑ e, (M i e : ℝ) * ((x e : ℤ) : ℝ)
  push_cast
  rfl

theorem cast_single {α : Type*} [DecidableEq α] (a j : α) :
    (((Pi.single a (1 : ℤ) : α → ℤ) j : ℤ) : ℝ)
      = (Pi.single a (1 : ℝ) : α → ℝ) j := by
  rcases eq_or_ne j a with h | h
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same]
    norm_num
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h]
    norm_num

theorem boundary_castR (ω : G.E → ℤ) (v : G.V) :
    G.boundary (fun e => ((ω e : ℤ) : ℝ)) v = ((G.boundary ω v : ℤ) : ℝ) := by
  rw [boundary_eq_sum, boundary_eq_sum]
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 1
  rw [G.bcoeff_def, G.bcoeff_def]
  push_cast [apply_ite (Int.cast : ℤ → ℝ)]
  norm_num

/-- The cast fundamental cycles are closed. -/
theorem fundCyclesR_closed (i : Fin G.b1) (v : G.V) :
    G.boundary (G.fundCyclesR i) v = 0 := by
  have hmem := G.fundCyclesZ_mem i
  rw [mem_cycleLattice] at hmem
  show G.boundary (fun e => ((G.fundCyclesZ i e : ℤ) : ℝ)) v = 0
  rw [G.boundary_castR, hmem v, Int.cast_zero]

/-! ## Independence and the positive-definite Gram -/

/-- **Independence of the cast basis**, from the integer retraction:
a real dependency dies on applying the cast coordinate matrix. -/
theorem fund_cast_independent (x : Fin G.b1 → ℝ)
    (hx : (fun e => ∑ i, x i * G.fundCyclesR i e) = 0) : x = 0 := by
  have hPC : ∀ i : Fin G.b1,
      (G.coordMatrix.map (Int.cast : ℤ → ℝ)) *ᵥ
        (fun e => ((G.fundCyclesZ i e : ℤ) : ℝ)) = Pi.single i (1 : ℝ) := by
    intro i
    funext j
    rw [← G.cast_mulVec_apply, G.coordMatrix_mulVec, G.coordMap_fundCyclesZ]
    exact cast_single i j
  have hlin : (G.coordMatrix.map (Int.cast : ℤ → ℝ)) *ᵥ
      (fun e => ∑ i, x i * G.fundCyclesR i e) = fun j => x j := by
    funext j
    show ∑ e, (G.coordMatrix.map (Int.cast : ℤ → ℝ)) j e
        * (∑ i, x i * G.fundCyclesR i e) = x j
    calc ∑ e, (G.coordMatrix.map (Int.cast : ℤ → ℝ)) j e
          * (∑ i, x i * G.fundCyclesR i e)
        = ∑ e, ∑ i, x i * ((G.coordMatrix.map (Int.cast : ℤ → ℝ)) j e
            * G.fundCyclesR i e) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∑ e, x i * ((G.coordMatrix.map (Int.cast : ℤ → ℝ)) j e
            * G.fundCyclesR i e) := Finset.sum_comm
      _ = ∑ i, x i * ∑ e, (G.coordMatrix.map (Int.cast : ℤ → ℝ)) j e
            * G.fundCyclesR i e := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ i, x i * (Pi.single i (1 : ℝ) : Fin G.b1 → ℝ) j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 1
          exact congrFun (hPC i) j
      _ = x j := by
          rw [show (fun i => x i * (Pi.single i (1 : ℝ) : Fin G.b1 → ℝ) j)
              = fun i => if j = i then x i else 0 from funext fun i => by
            rcases eq_or_ne j i with h | h
            · subst h
              rw [if_pos rfl, Pi.single_eq_same, mul_one]
            · rw [if_neg h, Pi.single_eq_of_ne h, mul_zero]]
          rw [Finset.sum_ite_eq Finset.univ j x]
          simp
  rw [hx, Matrix.mulVec_zero] at hlin
  funext j
  exact (congrFun hlin j).symm

theorem dotProduct_gramOf_mulVec {r : ℕ} {ι : Type*} [Fintype ι]
    (c : Fin r → ι → ℝ) (x : Fin r → ℝ) :
    x ⬝ᵥ (gramOf c *ᵥ x)
      = (fun e => ∑ i, x i * c i e) ⬝ᵥ (fun e => ∑ i, x i * c i e) := by
  show ∑ i, x i * (∑ j, gramOf c i j * x j)
    = ∑ e, (∑ i, x i * c i e) * (∑ j, x j * c j e)
  calc ∑ i, x i * (∑ j, gramOf c i j * x j)
      = ∑ i, ∑ j, x i * x j * (∑ e, c i e * c j e) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        show x i * (gramOf c i j * x j) = x i * x j * (∑ e, c i e * c j e)
        rw [show gramOf c i j = ∑ e, c i e * c j e from rfl]
        ring
    _ = ∑ i, ∑ j, ∑ e, x i * x j * (c i e * c j e) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ i, ∑ e, ∑ j, x i * x j * (c i e * c j e) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ e, ∑ i, ∑ j, x i * x j * (c i e * c j e) := Finset.sum_comm
    _ = ∑ e, (∑ i, x i * c i e) * (∑ j, x j * c j e) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => by ring

/-- The fundamental Gram matrix is positive definite. -/
theorem gramOf_fund_posDef : (gramOf G.fundCyclesR).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · ext p q'
    show star (gramOf G.fundCyclesR q' p) = gramOf G.fundCyclesR p q'
    rw [star_trivial]
    show ∑ e, G.fundCyclesR q' e * G.fundCyclesR p e
      = ∑ e, G.fundCyclesR p e * G.fundCyclesR q' e
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _
  · have hsx : star x = x := funext fun i => star_trivial _
    rw [hsx, dotProduct_gramOf_mulVec]
    have hynn : (0 : ℝ) ≤ (fun e => ∑ i, x i * G.fundCyclesR i e)
        ⬝ᵥ (fun e => ∑ i, x i * G.fundCyclesR i e) :=
      Finset.sum_nonneg fun e _ => mul_self_nonneg _
    have hyne : (fun e => ∑ i, x i * G.fundCyclesR i e) ≠ 0 :=
      fun h0 => hx (G.fund_cast_independent x h0)
    have hne : (fun e => ∑ i, x i * G.fundCyclesR i e)
        ⬝ᵥ (fun e => ∑ i, x i * G.fundCyclesR i e) ≠ 0 :=
      fun h0 => hyne (dotProduct_self_eq_zero.mp h0)
    exact lt_of_le_of_ne hynn (Ne.symm hne)

/-! ## Closed-walk sums from vanishing periods -/

/-- **Vanishing periods kill closed-walk sums** — over any commutative
ring. The chain of a closed walk lies in the cycle lattice; expanding
it in the fundamental basis reduces its pairing to the vanishing
periods. This is the bridge from the linear algebra to the walk
engine. -/
theorem closedWalkSum_eq_zero {R : Type*} [CommRing R] (ω : G.E → R)
    (hper : ∀ j, ω ⬝ᵥ (fun e => ((G.fundCyclesZ j e : ℤ) : R)) = 0)
    {w : G.V} (c : G.Walk w w) : c.sum ω = 0 := by
  rw [Walk.sum_eq_dotProduct]
  have hmem : c.chain ℤ ∈ G.cycleLattice := G.chain_mem_cycleLattice c
  have hexp := G.cycleBasis.sum_repr ⟨c.chain ℤ, hmem⟩
  have hcoe : ∑ i, G.cycleBasis.repr ⟨c.chain ℤ, hmem⟩ i • G.fundCyclesZ i
      = c.chain ℤ := by
    have hval := congrArg Subtype.val hexp
    rw [AddSubmonoidClass.coe_finset_sum] at hval
    exact hval
  have hcast : ∀ e, c.chain R e
      = ∑ i, ((G.cycleBasis.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
          * ((G.fundCyclesZ i e : ℤ) : R) := by
    intro e
    rw [← Walk.chain_cast c e, ← congrFun hcoe e]
    show (((∑ i, G.cycleBasis.repr ⟨c.chain ℤ, hmem⟩ i • G.fundCyclesZ i) e
        : ℤ) : R) = _
    rw [show (∑ i, G.cycleBasis.repr ⟨c.chain ℤ, hmem⟩ i • G.fundCyclesZ i) e
        = ∑ i, G.cycleBasis.repr ⟨c.chain ℤ, hmem⟩ i * G.fundCyclesZ i e from by
      rw [Finset.sum_apply]
      rfl]
    push_cast
    rfl
  calc ω ⬝ᵥ c.chain R
      = ∑ e, ω e * ∑ i, ((G.cycleBasis.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
          * ((G.fundCyclesZ i e : ℤ) : R) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hcast e]
    _ = ∑ i, ((G.cycleBasis.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
          * ∑ e, ω e * ((G.fundCyclesZ i e : ℤ) : R) := by
        calc ∑ e, ω e * ∑ i, ((G.cycleBasis.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
              * ((G.fundCyclesZ i e : ℤ) : R)
            = ∑ e, ∑ i, ((G.cycleBasis.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
                * (ω e * ((G.fundCyclesZ i e : ℤ) : R)) := by
              refine Finset.sum_congr rfl fun e _ => ?_
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
          _ = ∑ i, ∑ e, ((G.cycleBasis.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
                * (ω e * ((G.fundCyclesZ i e : ℤ) : R)) := Finset.sum_comm
          _ = ∑ i, ((G.cycleBasis.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
                * ∑ e, ω e * ((G.fundCyclesZ i e : ℤ) : R) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
    _ = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [show (∑ e, ω e * ((G.fundCyclesZ i e : ℤ) : R))
            = ω ⬝ᵥ (fun e => ((G.fundCyclesZ i e : ℤ) : R)) from rfl,
          hper i, mul_zero]

/-! ## The four fields, as theorems -/

/-- **Integral potentials for every finite graph**: vanishing periods
against the fundamental basis yield an integer potential, by walk
integration. -/
theorem fund_integral_potentials (ω : G.E → ℤ)
    (h : ∀ j, ω ⬝ᵥ G.fundCyclesZ j = 0) :
    ∃ g : G.V → ℤ, G.grad g = ω := by
  have hper : ∀ j, ω ⬝ᵥ (fun e => ((G.fundCyclesZ j e : ℤ) : ℤ)) = 0 := by
    intro j
    rw [show (fun e => ((G.fundCyclesZ j e : ℤ) : ℤ)) = G.fundCyclesZ j from
      funext fun e => Int.cast_id]
    exact h j
  exact ⟨G.integrate ω,
    G.grad_integrate ω (fun w c => G.closedWalkSum_eq_zero ω hper c)⟩

/-- **Period surjectivity for every finite graph**: `τ := Pᵀ k`
realizes any prescribed integer periods, `P` the coordinate matrix. -/
theorem fund_periods_onto (k : Fin G.b1 → ℤ) :
    ∃ τ : G.E → ℤ, ∀ j, τ ⬝ᵥ G.fundCyclesZ j = k j := by
  refine ⟨fun e => ∑ i, G.coordMatrix i e * k i, fun j => ?_⟩
  have hPC : ∀ i, (G.coordMatrix *ᵥ G.fundCyclesZ j) i
      = (Pi.single j (1 : ℤ) : Fin G.b1 → ℤ) i := by
    intro i
    rw [G.coordMatrix_mulVec, G.coordMap_fundCyclesZ]
  show ∑ e, (∑ i, G.coordMatrix i e * k i) * G.fundCyclesZ j e = k j
  calc ∑ e, (∑ i, G.coordMatrix i e * k i) * G.fundCyclesZ j e
      = ∑ e, ∑ i, k i * (G.coordMatrix i e * G.fundCyclesZ j e) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, ∑ e, k i * (G.coordMatrix i e * G.fundCyclesZ j e) :=
        Finset.sum_comm
    _ = ∑ i, k i * ∑ e, G.coordMatrix i e * G.fundCyclesZ j e := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ i, k i * (Pi.single j (1 : ℤ) : Fin G.b1 → ℤ) i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        exact hPC i
    _ = k j := by
        rw [show (fun i => k i * (Pi.single j (1 : ℤ) : Fin G.b1 → ℤ) i)
            = fun i => if i = j then k i else 0 from funext fun i => by
          rcases eq_or_ne i j with h | h
          · subst h
            rw [if_pos rfl, Pi.single_eq_same, mul_one]
          · rw [if_neg h, Pi.single_eq_of_ne h, mul_zero]]
        rw [Finset.sum_ite_eq' Finset.univ j k]
        simp

/-- **Spanning for every finite graph**: a closed real cochain is a
combination of the fundamental cycles. The Gram inverse supplies the
coefficients (a concrete orthogonal projection); the residual has
vanishing periods, hence — by the walk engine — is a gradient, and a
closed gradient is zero by Stokes. -/
theorem fund_spanning (ω : G.E → ℝ) (hω : ∀ v, G.boundary ω v = 0) :
    ∃ a : Fin G.b1 → ℝ, ω = fun e => ∑ i, a i * G.fundCyclesR i e := by
  have hdet : IsUnit (gramOf G.fundCyclesR).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt G.gramOf_fund_posDef.det_pos)
  set p : Fin G.b1 → ℝ := fun j => ω ⬝ᵥ G.fundCyclesR j with hp
  refine ⟨(gramOf G.fundCyclesR)⁻¹ *ᵥ p, ?_⟩
  set a : Fin G.b1 → ℝ := (gramOf G.fundCyclesR)⁻¹ *ᵥ p with ha
  set ω' : G.E → ℝ := fun e => ω e - ∑ i, a i * G.fundCyclesR i e with hω'
  -- The residual is closed.
  have hcomb : ∀ v, G.boundary (fun e => ∑ i, a i * G.fundCyclesR i e) v
      = ∑ i, a i * G.boundary (G.fundCyclesR i) v := by
    intro v
    rw [boundary_eq_sum]
    calc ∑ e, G.bcoeff v e * ∑ i, a i * G.fundCyclesR i e
        = ∑ e, ∑ i, a i * (G.bcoeff v e * G.fundCyclesR i e) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∑ e, a i * (G.bcoeff v e * G.fundCyclesR i e) :=
          Finset.sum_comm
      _ = ∑ i, a i * ∑ e, G.bcoeff v e * G.fundCyclesR i e := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ i, a i * G.boundary (G.fundCyclesR i) v :=
          Finset.sum_congr rfl fun i _ => by rw [← boundary_eq_sum]
  have hclosed' : ∀ v, G.boundary ω' v = 0 := by
    intro v
    have hsub : G.boundary ω' v = G.boundary ω v
        - G.boundary (fun e => ∑ i, a i * G.fundCyclesR i e) v := by
      have h1 := G.boundary_add ω
        (-(fun e => ∑ i, a i * G.fundCyclesR i e)) v
      rw [G.boundary_neg] at h1
      rw [show ω' = ω + -(fun e => ∑ i, a i * G.fundCyclesR i e) from
        funext fun e => by
          show ω e - ∑ i, a i * G.fundCyclesR i e = ω e + -(∑ i, a i * G.fundCyclesR i e)
          ring]
      rw [h1]
      ring
    rw [hsub, hω v, hcomb v]
    rw [Finset.sum_eq_zero fun i _ => by rw [G.fundCyclesR_closed i v, mul_zero]]
    ring
  -- The residual has vanishing periods.
  have hper' : ∀ j, ω' ⬝ᵥ G.fundCyclesR j = 0 := by
    intro j
    have hsum : ω' ⬝ᵥ G.fundCyclesR j
        = p j - ∑ i, a i * gramOf G.fundCyclesR i j := by
      show ∑ e, (ω e - ∑ i, a i * G.fundCyclesR i e) * G.fundCyclesR j e = _
      calc ∑ e, (ω e - ∑ i, a i * G.fundCyclesR i e) * G.fundCyclesR j e
          = ∑ e, (ω e * G.fundCyclesR j e
              - (∑ i, a i * G.fundCyclesR i e) * G.fundCyclesR j e) := by
            refine Finset.sum_congr rfl fun e _ => ?_
            ring
        _ = (∑ e, ω e * G.fundCyclesR j e)
            - ∑ e, (∑ i, a i * G.fundCyclesR i e) * G.fundCyclesR j e :=
            Finset.sum_sub_distrib _ _
        _ = p j - ∑ i, a i * gramOf G.fundCyclesR i j := by
            congr 1
            calc ∑ e, (∑ i, a i * G.fundCyclesR i e) * G.fundCyclesR j e
                = ∑ e, ∑ i, a i * (G.fundCyclesR i e * G.fundCyclesR j e) := by
                  refine Finset.sum_congr rfl fun e _ => ?_
                  rw [Finset.sum_mul]
                  exact Finset.sum_congr rfl fun i _ => by ring
              _ = ∑ i, ∑ e, a i * (G.fundCyclesR i e * G.fundCyclesR j e) :=
                  Finset.sum_comm
              _ = ∑ i, a i * ∑ e, G.fundCyclesR i e * G.fundCyclesR j e := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.mul_sum]
              _ = ∑ i, a i * gramOf G.fundCyclesR i j :=
                  Finset.sum_congr rfl fun i _ => rfl
    have hcollapse : ∑ i, a i * gramOf G.fundCyclesR i j = p j := by
      have h1 : ∑ i, a i * gramOf G.fundCyclesR i j
          = (gramOf G.fundCyclesR *ᵥ a) j := by
        show _ = ∑ i, gramOf G.fundCyclesR j i * a i
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show gramOf G.fundCyclesR j i = gramOf G.fundCyclesR i j from by
          show ∑ e, G.fundCyclesR j e * G.fundCyclesR i e
            = ∑ e, G.fundCyclesR i e * G.fundCyclesR j e
          exact Finset.sum_congr rfl fun e _ => mul_comm _ _]
        ring
      rw [h1, ha, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet,
        Matrix.one_mulVec]
    rw [hsum, hcollapse]
    ring
  -- Hence a gradient; a closed gradient is zero.
  have hcast : ∀ j, ω' ⬝ᵥ (fun e => ((G.fundCyclesZ j e : ℤ) : ℝ)) = 0 :=
    fun j => hper' j
  obtain ⟨f, hf⟩ : ∃ f : G.V → ℝ, G.grad f = ω' :=
    ⟨G.integrate ω',
      G.grad_integrate ω' (fun w c => G.closedWalkSum_eq_zero ω' hcast c)⟩
  have hzz : ω' ⬝ᵥ ω' = 0 := by
    calc ω' ⬝ᵥ ω' = G.grad f ⬝ᵥ ω' := by rw [hf]
      _ = ∑ v, f v * G.boundary ω' v := G.grad_dotProduct_eq f ω'
      _ = 0 := Finset.sum_eq_zero fun v _ => by rw [hclosed' v, mul_zero]
  have hz : ω' = 0 := dotProduct_self_eq_zero.mp hzz
  funext e
  have he := congrFun hz e
  show ω e = ∑ i, a i * G.fundCyclesR i e
  have he' : ω e - ∑ i, a i * G.fundCyclesR i e = 0 := he
  linarith

/-! ## The fundamental presentation -/

/-- **The fundamental-presentation theorem (C2)**: every finite
incidence graph carries an integral cycle presentation — a primitive
integer basis of its cycle lattice with periods realizability and
integral potentials **derived, not stored**. The keystone's interface
is a theorem for every finite graph. -/
noncomputable def fundamentalPresentation : IntegralCyclePresentation G where
  r := G.b1
  cycles := G.fundCyclesR
  cycles_closed := G.fundCyclesR_closed
  spanning := G.fund_spanning
  gram_posDef := G.gramOf_fund_posDef
  cyclesZ := G.fundCyclesZ
  cyclesZ_cast := fun _ _ => rfl
  periods_onto := G.fund_periods_onto
  integral_potentials := G.fund_integral_potentials

/-! ## Consumers: the "for every finite graph" upgrades -/

/-- `H₁(G;ℤ)` is free of rank `b₁`. -/
instance : Module.Free ℤ G.cycleLattice := Module.Free.of_basis G.cycleBasis

theorem finrank_cycleLattice : Module.finrank ℤ G.cycleLattice = G.b1 := by
  rw [Module.finrank_eq_card_basis G.cycleBasis, Fintype.card_fin]

/-- **Intrinsic `H¹` coordinates for every finite graph** (C2
acceptance): integer cochains modulo integer gradients are `ℤ^{b₁}` —
through the fundamental presentation, with no per-graph fields. -/
noncomputable def h1QuotEquiv :
    ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) ≃ₗ[ℤ] (Fin G.b1 → ℤ) :=
  G.fundamentalPresentation.latticeQuotEquiv

/-- **Euler's formula for every finite graph**:
`b₁ = |E| − |V| + c`. -/
theorem b1_eq :
    (G.b1 : ℤ) = (Fintype.card G.E : ℤ) - Fintype.card G.V
      + G.componentCard :=
  G.fundamentalPresentation.r_eq_card_edges_sub_card_vertices_add_components

/-! ## The real cycle space and the spanning criterion -/

/-- The real cycle space has dimension `b₁`: rank–nullity twice, the
transpose rank equality, and Euler (`b1_eq`). -/
theorem finrank_ker_boundaryLin :
    Module.finrank ℝ (LinearMap.ker (G.boundaryLin ℝ)) = G.b1 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (G.boundaryLin ℝ)
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker (G.gradLin ℝ)
  rw [Module.finrank_fintype_fun_eq_card, G.finrank_gauge] at h2
  have hbm : G.boundaryLin ℝ = (G.boundaryMatrix ℝ).mulVecLin := by
    apply LinearMap.ext
    intro ω
    funext v
    rw [Matrix.mulVecLin_apply, G.boundaryMatrix_mulVec]
    rfl
  have hgm : G.gradLin ℝ = ((G.boundaryMatrix ℝ)ᵀ).mulVecLin := by
    apply LinearMap.ext
    intro f
    rw [Matrix.mulVecLin_apply, G.transpose_boundaryMatrix_mulVec]
    rfl
  have hrank : Module.finrank ℝ (LinearMap.range (G.boundaryLin ℝ))
      = Module.finrank ℝ (LinearMap.range (G.gradLin ℝ)) := by
    rw [hbm, hgm]
    show (G.boundaryMatrix ℝ).rank = ((G.boundaryMatrix ℝ)ᵀ).rank
    exact (Matrix.rank_transpose _).symm
  have hb := G.b1_eq
  omega

/-- **The spanning criterion** (C5's tool): a closed, linearly
independent family of `b₁` cycle vectors spans the cycle space — by
Euler, with no per-graph constancy argument. -/
theorem spanning_of_card_eq_b1 {r : ℕ} (hr : r = G.b1)
    (c : Fin r → G.E → ℝ)
    (hclosed : ∀ i v, G.boundary (c i) v = 0)
    (hindep : ∀ x : Fin r → ℝ,
      (fun e => ∑ i, x i * c i e) = 0 → x = 0)
    (ω : G.E → ℝ) (hω : ∀ v, G.boundary ω v = 0) :
    ∃ a : Fin r → ℝ, ω = fun e => ∑ i, a i * c i e := by
  have hmemc : ∀ i, c i ∈ LinearMap.ker (G.boundaryLin ℝ) := by
    intro i
    rw [LinearMap.mem_ker]
    funext v
    exact hclosed i v
  set c' : Fin r → LinearMap.ker (G.boundaryLin ℝ) :=
    fun i => ⟨c i, hmemc i⟩ with hc'
  have hsum_coe : ∀ (g : Fin r → ℝ),
      ((∑ i, g i • c' i : LinearMap.ker (G.boundaryLin ℝ)) : G.E → ℝ)
        = fun e => ∑ i, g i * c i e := by
    intro g
    rw [AddSubmonoidClass.coe_finset_sum]
    funext e
    rw [Finset.sum_apply]
    rfl
  have hli : LinearIndependent ℝ c' := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hcoe := congrArg Subtype.val hg
    rw [hsum_coe g] at hcoe
    have hgz := hindep g hcoe
    intro i
    exact congrFun hgz i
  have hcard : Fintype.card (Fin r)
      = Module.finrank ℝ (LinearMap.ker (G.boundaryLin ℝ)) := by
    rw [Fintype.card_fin, G.finrank_ker_boundaryLin, hr]
  have hspan : Submodule.span ℝ (Set.range c') = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, hcard]
  have hmem : (⟨ω, by rw [LinearMap.mem_ker]; funext v; exact hω v⟩ :
      LinearMap.ker (G.boundaryLin ℝ)) ∈ Submodule.span ℝ (Set.range c') := by
    rw [hspan]
    trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  refine ⟨a, ?_⟩
  have hcoe := congrArg Subtype.val ha
  rw [hsum_coe a] at hcoe
  exact hcoe.symm

end IncidenceGraph

/-- **Rank well-definedness** (the first C3 brick): every integral
presentation of a graph has rank `b₁` — the chosen basis size is not
a choice at all. Both keystone equivalences target the same quotient;
composing them equates the ranks. -/
theorem IntegralCyclePresentation.r_eq_b1 {G : IncidenceGraph.{u, v}}
    (Q : IntegralCyclePresentation G) : Q.r = G.b1 := by
  have e := Q.latticeQuotEquiv.symm.trans G.h1QuotEquiv
  have h := e.finrank_eq
  rwa [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin, Fintype.card_fin] at h

end Meno
