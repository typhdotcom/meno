import Meno.IncidenceGraph
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Graph Homology: the pure topology layer

Everything a finite graph's first homology provides — lattice, basis,
exactness, quotient, rank, and Euler results — in one file importing
only the substrate (review #5, finding 1; review #6, finding 2: no
Gram object, no positive-definiteness, no matrix inversion — the
unit-edge Gram and every priced consequence live in the
variational layer, `Meno/PeriodHarmonic.lean`):

* freeness of `ℤ^E ⧸ H₁`, the splitting, and the retraction of `ℤ^E`
  onto the cycle lattice;
* **the derived data of an arbitrary lattice basis**
  `B : Module.Basis (Fin n) ℤ G.cycleLattice` (review #5, finding 2 —
  the presentation *is* the basis; every former field is a theorem):
  integer cycles `cyclesZ`, real casts `cyclesR`, closedness,
  coordinates `coordMap`, real independence `cast_independent`,
  integer potentials, period surjectivity (`ℤ` and `ℝ`), real
  spanning, exactness, and the keystone quotient equivalences over
  `ℤ` and `ℝ`;
* the **fundamental basis** `cycleBasis` (PID structure theorem):
  existence of a lattice basis for every finite graph — C2's content,
  with nothing stored;
* the **real cycle-space rank** (`finrank_ker_boundaryLin`), **Euler's
  formula** (`b1_eq`), and the **spanning criterion**
  (`spanning_of_card_eq_b1`);
* `basisOfCycles` — the concrete-instance bridge: closed, independent,
  integrally spanning integer cycles assemble into a lattice basis.

What remains of the metric is the period *pairing* `⬝ᵥ` against the
basis cycles and the discrete Stokes identity — periods, not a chosen
Gram: real spanning solves the period system by
injectivity-implies-surjectivity of the pairing operator on the
finite-dimensional coefficient space (review #6), with no Gram
matrix, no positivity, and no inverse. -/

namespace Meno

open scoped BigOperators
open Matrix

universe u v

namespace IncidenceGraph

variable (G : IncidenceGraph.{u, v})

/-! ## Freeness of the cochain quotient, the splitting, the retraction

`H₁(G;ℤ) = ker ∂ℤ` is saturated (`mem_of_smul_mem`,
`Meno/IncidenceGraph.lean`), so `ℤ^E ⧸ H₁` is torsion-free, hence free,
hence projective — the quotient map splits and `ℤ^E` retracts onto the
cycle lattice. -/

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

/-! ## The derived data of an arbitrary lattice basis

The presentation **is** a basis `B : Module.Basis (Fin n) ℤ
G.cycleLattice` (review #5, finding 2). Everything the retired
structures stored is a theorem of `B`: the integer cycles and their
real casts, closedness, independence, Gram positivity, integer
potentials, period surjectivity, spanning, exactness, and the keystone
quotient equivalences. Every basis automatically has `n = b₁`
(`card_eq_b1`). -/

section LatticeBasis

variable {n : ℕ} (B : Module.Basis (Fin n) ℤ G.cycleLattice)

/-- The integer cycle vectors of a lattice basis, as cochains. -/
noncomputable def cyclesZ : Fin n → G.E → ℤ :=
  fun i => (B i : G.E → ℤ)

/-- The cycle vectors of a lattice basis, cast to `ℝ`. -/
noncomputable def cyclesR : Fin n → G.E → ℝ :=
  fun i e => ((G.cyclesZ B i e : ℤ) : ℝ)

theorem cyclesZ_mem (i : Fin n) : G.cyclesZ B i ∈ G.cycleLattice :=
  (B i).2

/-- The cast cycle vectors are closed. -/
theorem cyclesR_closed (i : Fin n) (v : G.V) :
    G.boundary (G.cyclesR B i) v = 0 := by
  have hmem := G.cyclesZ_mem B i
  rw [mem_cycleLattice] at hmem
  show G.boundary (fun e => ((G.cyclesZ B i e : ℤ) : ℝ)) v = 0
  rw [G.boundary_castR, hmem v, Int.cast_zero]

/-- Basis coordinates extended to the ambient lattice along the
retraction: the integer matrix `P` with `P Cᵀ = 1`. -/
noncomputable def coordMap : (G.E → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
  (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).toLinearMap
    ∘ₗ B.repr.toLinearMap
    ∘ₗ LinearMap.codRestrict G.cycleLattice G.cycleRetract G.cycleRetract_mem

theorem coordMap_cyclesZ (i : Fin n) :
    G.coordMap B (G.cyclesZ B i) = Pi.single i 1 := by
  have hfix : LinearMap.codRestrict G.cycleLattice G.cycleRetract
      G.cycleRetract_mem (G.cyclesZ B i) = B i := by
    apply Subtype.ext
    show G.cycleRetract (G.cyclesZ B i) = (B i : G.E → ℤ)
    exact G.cycleRetract_of_mem (G.cyclesZ_mem B i)
  show (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n))
      (B.repr (LinearMap.codRestrict G.cycleLattice G.cycleRetract
        G.cycleRetract_mem (G.cyclesZ B i))) = Pi.single i 1
  rw [hfix, Module.Basis.repr_self]
  funext j
  rcases eq_or_ne j i with h | h
  · subst h
    show Finsupp.single j (1 : ℤ) j = (Pi.single j 1 : Fin n → ℤ) j
    rw [Finsupp.single_eq_same, Pi.single_eq_same]
  · show Finsupp.single i (1 : ℤ) j = (Pi.single i 1 : Fin n → ℤ) j
    rw [Finsupp.single_eq_of_ne h, Pi.single_eq_of_ne h]

/-- The coordinate matrix of `coordMap` in the standard bases. -/
noncomputable def coordMatrix : Matrix (Fin n) G.E ℤ :=
  LinearMap.toMatrix' (G.coordMap B)

theorem coordMatrix_mulVec (x : G.E → ℤ) :
    G.coordMatrix B *ᵥ x = G.coordMap B x := by
  rw [coordMatrix, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

/-- **Independence of the cast basis**, from the integer retraction:
a real dependency dies on applying the cast coordinate matrix. -/
theorem cast_independent (x : Fin n → ℝ)
    (hx : (fun e => ∑ i, x i * G.cyclesR B i e) = 0) : x = 0 := by
  have hPC : ∀ i : Fin n,
      ((G.coordMatrix B).map (Int.cast : ℤ → ℝ)) *ᵥ
        (fun e => ((G.cyclesZ B i e : ℤ) : ℝ)) = Pi.single i (1 : ℝ) := by
    intro i
    funext j
    rw [← G.cast_mulVec_apply, G.coordMatrix_mulVec, G.coordMap_cyclesZ]
    exact cast_single i j
  have hlin : ((G.coordMatrix B).map (Int.cast : ℤ → ℝ)) *ᵥ
      (fun e => ∑ i, x i * G.cyclesR B i e) = fun j => x j := by
    funext j
    show ∑ e, ((G.coordMatrix B).map (Int.cast : ℤ → ℝ)) j e
        * (∑ i, x i * G.cyclesR B i e) = x j
    calc ∑ e, ((G.coordMatrix B).map (Int.cast : ℤ → ℝ)) j e
          * (∑ i, x i * G.cyclesR B i e)
        = ∑ e, ∑ i, x i * (((G.coordMatrix B).map (Int.cast : ℤ → ℝ)) j e
            * G.cyclesR B i e) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∑ e, x i * (((G.coordMatrix B).map (Int.cast : ℤ → ℝ)) j e
            * G.cyclesR B i e) := Finset.sum_comm
      _ = ∑ i, x i * ∑ e, ((G.coordMatrix B).map (Int.cast : ℤ → ℝ)) j e
            * G.cyclesR B i e := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ i, x i * (Pi.single i (1 : ℝ) : Fin n → ℝ) j := by
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 1
          exact congrFun (hPC i) j
      _ = x j := by
          rw [show (fun i => x i * (Pi.single i (1 : ℝ) : Fin n → ℝ) j)
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

/-- **Vanishing periods kill closed-walk sums** — over any commutative
ring. The chain of a closed walk lies in the cycle lattice; expanding
it in the basis reduces its pairing to the vanishing periods. -/
theorem closedWalkSum_eq_zero {R : Type*} [CommRing R] (ω : G.E → R)
    (hper : ∀ j, ω ⬝ᵥ (fun e => ((G.cyclesZ B j e : ℤ) : R)) = 0)
    {w : G.V} (c : G.Walk w w) : c.sum ω = 0 := by
  rw [Walk.sum_eq_dotProduct]
  have hmem : c.chain ℤ ∈ G.cycleLattice := G.chain_mem_cycleLattice c
  have hexp := B.sum_repr ⟨c.chain ℤ, hmem⟩
  have hcoe : ∑ i, B.repr ⟨c.chain ℤ, hmem⟩ i • G.cyclesZ B i
      = c.chain ℤ := by
    have hval := congrArg Subtype.val hexp
    rw [AddSubmonoidClass.coe_finset_sum] at hval
    exact hval
  have hcast : ∀ e, c.chain R e
      = ∑ i, ((B.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
          * ((G.cyclesZ B i e : ℤ) : R) := by
    intro e
    rw [← Walk.chain_cast c e, ← congrFun hcoe e]
    show (((∑ i, B.repr ⟨c.chain ℤ, hmem⟩ i • G.cyclesZ B i) e
        : ℤ) : R) = _
    rw [show (∑ i, B.repr ⟨c.chain ℤ, hmem⟩ i • G.cyclesZ B i) e
        = ∑ i, B.repr ⟨c.chain ℤ, hmem⟩ i * G.cyclesZ B i e from by
      rw [Finset.sum_apply]
      rfl]
    push_cast
    rfl
  calc ω ⬝ᵥ c.chain R
      = ∑ e, ω e * ∑ i, ((B.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
          * ((G.cyclesZ B i e : ℤ) : R) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [hcast e]
    _ = ∑ i, ((B.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
          * ∑ e, ω e * ((G.cyclesZ B i e : ℤ) : R) := by
        calc ∑ e, ω e * ∑ i, ((B.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
              * ((G.cyclesZ B i e : ℤ) : R)
            = ∑ e, ∑ i, ((B.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
                * (ω e * ((G.cyclesZ B i e : ℤ) : R)) := by
              refine Finset.sum_congr rfl fun e _ => ?_
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
          _ = ∑ i, ∑ e, ((B.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
                * (ω e * ((G.cyclesZ B i e : ℤ) : R)) := Finset.sum_comm
          _ = ∑ i, ((B.repr ⟨c.chain ℤ, hmem⟩ i : ℤ) : R)
                * ∑ e, ω e * ((G.cyclesZ B i e : ℤ) : R) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
    _ = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [show (∑ e, ω e * ((G.cyclesZ B i e : ℤ) : R))
            = ω ⬝ᵥ (fun e => ((G.cyclesZ B i e : ℤ) : R)) from rfl,
          hper i, mul_zero]

/-- **Integral potentials, derived**: vanishing periods against the
basis yield an integer potential, by walk integration. -/
theorem integral_potentials (ω : G.E → ℤ)
    (h : ∀ j, ω ⬝ᵥ G.cyclesZ B j = 0) :
    ∃ g : G.V → ℤ, G.grad g = ω := by
  have hper : ∀ j, ω ⬝ᵥ (fun e => ((G.cyclesZ B j e : ℤ) : ℤ)) = 0 := by
    intro j
    rw [show (fun e => ((G.cyclesZ B j e : ℤ) : ℤ)) = G.cyclesZ B j from
      funext fun e => Int.cast_id]
    exact h j
  exact ⟨G.integrate ω,
    G.grad_integrate ω (fun w c => G.closedWalkSum_eq_zero B ω hper c)⟩

/-- **Integer period surjectivity, derived**: `τ := Pᵀ k` realizes any
prescribed integer periods, `P` the coordinate matrix. -/
theorem periods_onto (k : Fin n → ℤ) :
    ∃ τ : G.E → ℤ, ∀ j, τ ⬝ᵥ G.cyclesZ B j = k j := by
  refine ⟨fun e => ∑ i, G.coordMatrix B i e * k i, fun j => ?_⟩
  have hPC : ∀ i, (G.coordMatrix B *ᵥ G.cyclesZ B j) i
      = (Pi.single j (1 : ℤ) : Fin n → ℤ) i := by
    intro i
    rw [G.coordMatrix_mulVec, G.coordMap_cyclesZ]
  show ∑ e, (∑ i, G.coordMatrix B i e * k i) * G.cyclesZ B j e = k j
  calc ∑ e, (∑ i, G.coordMatrix B i e * k i) * G.cyclesZ B j e
      = ∑ e, ∑ i, k i * (G.coordMatrix B i e * G.cyclesZ B j e) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, ∑ e, k i * (G.coordMatrix B i e * G.cyclesZ B j e) :=
        Finset.sum_comm
    _ = ∑ i, k i * ∑ e, G.coordMatrix B i e * G.cyclesZ B j e := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ i, k i * (Pi.single j (1 : ℤ) : Fin n → ℤ) i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        exact hPC i
    _ = k j := by
        rw [show (fun i => k i * (Pi.single j (1 : ℤ) : Fin n → ℤ) i)
            = fun i => if i = j then k i else 0 from funext fun i => by
          rcases eq_or_ne i j with h | h
          · subst h
            rw [if_pos rfl, Pi.single_eq_same, mul_one]
          · rw [if_neg h, Pi.single_eq_of_ne h, mul_zero]]
        rw [Finset.sum_ite_eq' Finset.univ j k]
        simp

/-- **Real period surjectivity, derived**: the cast coordinate matrix
realizes any prescribed real periods. -/
theorem periodsR_onto (k : Fin n → ℝ) :
    ∃ ω : G.E → ℝ, ∀ j, ω ⬝ᵥ G.cyclesR B j = k j := by
  refine ⟨fun e => ∑ i, ((G.coordMatrix B i e : ℤ) : ℝ) * k i, fun j => ?_⟩
  have hPC : ∀ i, ∑ e, ((G.coordMatrix B i e : ℤ) : ℝ) * G.cyclesR B j e
      = (Pi.single j (1 : ℝ) : Fin n → ℝ) i := by
    intro i
    have hcast : ∑ e, ((G.coordMatrix B i e : ℤ) : ℝ) * G.cyclesR B j e
        = (((G.coordMatrix B *ᵥ G.cyclesZ B j) i : ℤ) : ℝ) := by
      show _ = ((∑ e, G.coordMatrix B i e * G.cyclesZ B j e : ℤ) : ℝ)
      push_cast
      rfl
    rw [hcast, G.coordMatrix_mulVec, G.coordMap_cyclesZ]
    exact cast_single j i
  show ∑ e, (∑ i, ((G.coordMatrix B i e : ℤ) : ℝ) * k i) * G.cyclesR B j e
    = k j
  calc ∑ e, (∑ i, ((G.coordMatrix B i e : ℤ) : ℝ) * k i) * G.cyclesR B j e
      = ∑ e, ∑ i, k i * (((G.coordMatrix B i e : ℤ) : ℝ) * G.cyclesR B j e) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, ∑ e, k i * (((G.coordMatrix B i e : ℤ) : ℝ) * G.cyclesR B j e) :=
        Finset.sum_comm
    _ = ∑ i, k i * ∑ e, ((G.coordMatrix B i e : ℤ) : ℝ) * G.cyclesR B j e := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ i, k i * (Pi.single j (1 : ℝ) : Fin n → ℝ) i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        exact hPC i
    _ = k j := by
        rw [show (fun i => k i * (Pi.single j (1 : ℝ) : Fin n → ℝ) i)
            = fun i => if i = j then k i else 0 from funext fun i => by
          rcases eq_or_ne i j with h | h
          · subst h
            rw [if_pos rfl, Pi.single_eq_same, mul_one]
          · rw [if_neg h, Pi.single_eq_of_ne h, mul_zero]]
        rw [Finset.sum_ite_eq' Finset.univ j k]
        simp

/-- **Real spanning, derived** — with no Gram matrix, no positivity,
and no inversion (review #6, finding 2): the period-pairing operator
on the finite-dimensional coefficient space is injective by
independence, hence surjective, so coefficients matching the cochain's
periods exist; the residual has vanishing periods, hence — by the walk
engine — is a gradient, and a closed gradient is zero by Stokes. -/
theorem spanning (ω : G.E → ℝ) (hω : ∀ v, G.boundary ω v = 0) :
    ∃ a : Fin n → ℝ, ω = fun e => ∑ i, a i * G.cyclesR B i e := by
  -- Pairing a cochain against a coefficient combination.
  have hswap : ∀ (x : G.E → ℝ) (b : Fin n → ℝ),
      x ⬝ᵥ (fun e => ∑ j, b j * G.cyclesR B j e)
        = ∑ j, b j * (x ⬝ᵥ G.cyclesR B j) := by
    intro x b
    calc x ⬝ᵥ (fun e => ∑ j, b j * G.cyclesR B j e)
        = ∑ e, x e * ∑ j, b j * G.cyclesR B j e := rfl
      _ = ∑ e, ∑ j, b j * (x e * G.cyclesR B j e) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j, ∑ e, b j * (x e * G.cyclesR B j e) := Finset.sum_comm
      _ = ∑ j, b j * (x ⬝ᵥ G.cyclesR B j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.mul_sum]
          rfl
  -- The period-pairing operator on coefficient space.
  set T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun b => fun j => ∑ i, b i * (G.cyclesR B i ⬝ᵥ G.cyclesR B j)
      map_add' := fun b b' => by
        funext j
        show ∑ i, (b i + b' i) * (G.cyclesR B i ⬝ᵥ G.cyclesR B j) = _
        rw [show (∑ i, (b i + b' i) * (G.cyclesR B i ⬝ᵥ G.cyclesR B j))
            = ∑ i, (b i * (G.cyclesR B i ⬝ᵥ G.cyclesR B j)
              + b' i * (G.cyclesR B i ⬝ᵥ G.cyclesR B j)) from
          Finset.sum_congr rfl fun i _ => by ring]
        rw [Finset.sum_add_distrib]
        rfl
      map_smul' := fun c b => by
        funext j
        show ∑ i, (c * b i) * (G.cyclesR B i ⬝ᵥ G.cyclesR B j)
          = c * ∑ i, b i * (G.cyclesR B i ⬝ᵥ G.cyclesR B j)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring } with hT
  -- The operator computes the periods of the combination.
  have hTcomb : ∀ (b : Fin n → ℝ) (j : Fin n),
      T b j = (fun e => ∑ i, b i * G.cyclesR B i e) ⬝ᵥ G.cyclesR B j := by
    intro b j
    show ∑ i, b i * (G.cyclesR B i ⬝ᵥ G.cyclesR B j)
      = ∑ e, (∑ i, b i * G.cyclesR B i e) * G.cyclesR B j e
    calc ∑ i, b i * (G.cyclesR B i ⬝ᵥ G.cyclesR B j)
        = ∑ i, ∑ e, b i * (G.cyclesR B i e * G.cyclesR B j e) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          show b i * (∑ e, G.cyclesR B i e * G.cyclesR B j e) = _
          rw [Finset.mul_sum]
      _ = ∑ e, ∑ i, b i * (G.cyclesR B i e * G.cyclesR B j e) :=
          Finset.sum_comm
      _ = ∑ e, (∑ i, b i * G.cyclesR B i e) * G.cyclesR B j e := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
  -- Injective by independence, hence surjective on ℝⁿ.
  have hker : ∀ b, T b = 0 → b = 0 := by
    intro b hb
    have hzz : (fun e => ∑ i, b i * G.cyclesR B i e)
        ⬝ᵥ (fun e => ∑ i, b i * G.cyclesR B i e) = 0 := by
      rw [hswap]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← hTcomb b j, hb]
      show b j * (0 : Fin n → ℝ) j = 0
      rw [show (0 : Fin n → ℝ) j = 0 from rfl, mul_zero]
    exact G.cast_independent B b (dotProduct_self_eq_zero.mp hzz)
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot]
    exact LinearMap.ker_eq_bot'.mpr hker
  have hTsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective).mp hTinj
  obtain ⟨a, ha⟩ := hTsurj (fun j => ω ⬝ᵥ G.cyclesR B j)
  refine ⟨a, ?_⟩
  set ω' : G.E → ℝ := fun e => ω e - ∑ i, a i * G.cyclesR B i e with hω'
  -- The residual is closed.
  have hcomb : ∀ v, G.boundary (fun e => ∑ i, a i * G.cyclesR B i e) v
      = ∑ i, a i * G.boundary (G.cyclesR B i) v := by
    intro v
    rw [boundary_eq_sum]
    calc ∑ e, G.bcoeff v e * ∑ i, a i * G.cyclesR B i e
        = ∑ e, ∑ i, a i * (G.bcoeff v e * G.cyclesR B i e) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∑ e, a i * (G.bcoeff v e * G.cyclesR B i e) :=
          Finset.sum_comm
      _ = ∑ i, a i * ∑ e, G.bcoeff v e * G.cyclesR B i e := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ i, a i * G.boundary (G.cyclesR B i) v :=
          Finset.sum_congr rfl fun i _ => by rw [← boundary_eq_sum]
  have hclosed' : ∀ v, G.boundary ω' v = 0 := by
    intro v
    have hsub : G.boundary ω' v = G.boundary ω v
        - G.boundary (fun e => ∑ i, a i * G.cyclesR B i e) v := by
      have h1 := G.boundary_add ω
        (-(fun e => ∑ i, a i * G.cyclesR B i e)) v
      rw [G.boundary_neg] at h1
      rw [show ω' = ω + -(fun e => ∑ i, a i * G.cyclesR B i e) from
        funext fun e => by
          show ω e - ∑ i, a i * G.cyclesR B i e
            = ω e + -(∑ i, a i * G.cyclesR B i e)
          ring]
      rw [h1]
      ring
    rw [hsub, hω v, hcomb v]
    rw [Finset.sum_eq_zero fun i _ => by
      rw [G.cyclesR_closed B i v, mul_zero]]
    ring
  -- The residual has vanishing periods: its periods are the target
  -- periods minus the operator's output, which `ha` matches exactly.
  have hper' : ∀ j, ω' ⬝ᵥ G.cyclesR B j = 0 := by
    intro j
    have hsub : ω' ⬝ᵥ G.cyclesR B j
        = ω ⬝ᵥ G.cyclesR B j
          - (fun e => ∑ i, a i * G.cyclesR B i e) ⬝ᵥ G.cyclesR B j := by
      show ∑ e, (ω e - ∑ i, a i * G.cyclesR B i e) * G.cyclesR B j e = _
      rw [show (∑ e, (ω e - ∑ i, a i * G.cyclesR B i e) * G.cyclesR B j e)
          = ∑ e, (ω e * G.cyclesR B j e
            - (∑ i, a i * G.cyclesR B i e) * G.cyclesR B j e) from
        Finset.sum_congr rfl fun e _ => by ring]
      rw [Finset.sum_sub_distrib]
      rfl
    rw [hsub, ← hTcomb a j, congrFun ha j]
    exact sub_self _
  -- Hence a gradient; a closed gradient is zero.
  have hcast : ∀ j, ω' ⬝ᵥ (fun e => ((G.cyclesZ B j e : ℤ) : ℝ)) = 0 :=
    fun j => hper' j
  obtain ⟨f, hf⟩ : ∃ f : G.V → ℝ, G.grad f = ω' :=
    ⟨G.integrate ω',
      G.grad_integrate ω' (fun w c => G.closedWalkSum_eq_zero B ω' hcast c)⟩
  have hzz : ω' ⬝ᵥ ω' = 0 := by
    calc ω' ⬝ᵥ ω' = G.grad f ⬝ᵥ ω' := by rw [hf]
      _ = ∑ v, f v * G.boundary ω' v := G.grad_dotProduct_eq f ω'
      _ = 0 := Finset.sum_eq_zero fun v _ => by rw [hclosed' v, mul_zero]
  have hz : ω' = 0 := dotProduct_self_eq_zero.mp hzz
  funext e
  have he := congrFun hz e
  show ω e = ∑ i, a i * G.cyclesR B i e
  have he' : ω e - ∑ i, a i * G.cyclesR B i e = 0 := he
  linarith

/-! ### Stokes and exactness -/

/-- Real Stokes: gradients have vanishing periods against the cast
basis. -/
theorem grad_period (f : G.V → ℝ) (i : Fin n) :
    G.grad f ⬝ᵥ G.cyclesR B i = 0 := by
  rw [G.grad_dotProduct_eq]
  exact Finset.sum_eq_zero fun v _ => by
    rw [G.cyclesR_closed B i v, mul_zero]

/-- Integer Stokes: integer gradients have vanishing integer periods. -/
theorem gradZ_period (g : G.V → ℤ) (j : Fin n) :
    G.grad g ⬝ᵥ G.cyclesZ B j = 0 := by
  rw [G.grad_dotProduct_eq]
  exact Finset.sum_eq_zero fun v _ => by
    rw [(G.mem_cycleLattice.mp (G.cyclesZ_mem B j)) v, mul_zero]

/-- **Exactness**: a cochain has vanishing periods against the cast
basis iff it is a gradient. No connectivity hypothesis — connectivity
controls uniqueness of the potential, never existence. Forward
direction by the walk engine: vanishing periods kill closed-walk sums,
so integration from component basepoints produces a potential. -/
theorem period_eq_zero_iff_exists_grad (ω : G.E → ℝ) :
    (∀ i, ω ⬝ᵥ G.cyclesR B i = 0) ↔ ∃ f : G.V → ℝ, G.grad f = ω := by
  constructor
  · intro hper
    exact ⟨G.integrate ω,
      G.grad_integrate ω (fun w c =>
        G.closedWalkSum_eq_zero B ω (fun j => hper j) c)⟩
  · rintro ⟨f, rfl⟩ i
    exact G.grad_period B f i

/-! ### The keystone quotient equivalences -/

/-- The integer period map of a lattice basis. -/
noncomputable def periodLinZ : (G.E → ℤ) →ₗ[ℤ] (Fin n → ℤ) where
  toFun ω := fun j => ω ⬝ᵥ G.cyclesZ B j
  map_add' ω η := funext fun j => add_dotProduct ω η (G.cyclesZ B j)
  map_smul' c ω := funext fun j => smul_dotProduct c ω (G.cyclesZ B j)

/-- Lattice exactness: the kernel of the integer period map is exactly
the image of the integer gradient. -/
theorem range_gradLinZ_eq_ker_periodLinZ :
    LinearMap.range (G.gradLin ℤ) = LinearMap.ker (G.periodLinZ B) := by
  ext ω
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨g, rfl⟩
    funext j
    exact G.gradZ_period B g j
  · intro h
    exact G.integral_potentials B ω (fun j => congrFun h j)

theorem periodLinZ_surjective : Function.Surjective (G.periodLinZ B) := by
  intro k
  obtain ⟨ω, hω⟩ := G.periods_onto B k
  exact ⟨ω, funext hω⟩

/-- **THE KEYSTONE, ℤ-form**: integer descriptions modulo integer
local re-description are exactly the period lattice `ℤ^n` — through
any lattice basis. The quotient depends only on the graph. -/
noncomputable def latticeQuotEquiv :
    ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) ≃ₗ[ℤ] (Fin n → ℤ) :=
  (Submodule.quotEquivOfEq _ _ (G.range_gradLinZ_eq_ker_periodLinZ B)).trans
    ((G.periodLinZ B).quotKerEquivOfSurjective (G.periodLinZ_surjective B))

/-- The keystone coordinates of a class, on representatives. -/
theorem latticeQuotEquiv_mk (τ : G.E → ℤ) :
    G.latticeQuotEquiv B (Submodule.Quotient.mk τ)
      = fun j => τ ⬝ᵥ G.cyclesZ B j := rfl

/-- The real period map of a lattice basis. -/
noncomputable def periodLin : (G.E → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun ω := fun j => ω ⬝ᵥ G.cyclesR B j
  map_add' ω η := funext fun j => add_dotProduct ω η (G.cyclesR B j)
  map_smul' c ω := funext fun j => smul_dotProduct c ω (G.cyclesR B j)

theorem range_gradLin_eq_ker_periodLin :
    LinearMap.range (G.gradLin ℝ) = LinearMap.ker (G.periodLin B) := by
  ext ω
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨f, rfl⟩
    funext i
    exact G.grad_period B f i
  · intro h
    exact (G.period_eq_zero_iff_exists_grad B ω).mp (fun i => congrFun h i)

theorem periodLin_surjective : Function.Surjective (G.periodLin B) := by
  intro k
  obtain ⟨ω, hω⟩ := G.periodsR_onto B k
  exact ⟨ω, funext hω⟩

/-- **The incompressible residue, ℝ-form**: real cochains modulo
gradients — descriptions modulo local re-description — are exactly the
period space `ℝ^n`, via the period map. -/
noncomputable def cochainQuotEquiv :
    ((G.E → ℝ) ⧸ LinearMap.range (G.gradLin ℝ)) ≃ₗ[ℝ] (Fin n → ℝ) :=
  (Submodule.quotEquivOfEq _ _ (G.range_gradLin_eq_ker_periodLin B)).trans
    ((G.periodLin B).quotKerEquivOfSurjective (G.periodLin_surjective B))

include B in
theorem finrank_cochainQuot :
    Module.finrank ℝ ((G.E → ℝ) ⧸ LinearMap.range (G.gradLin ℝ)) = n := by
  rw [(G.cochainQuotEquiv B).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]

include B in
/-- **The parameter split**: describing a cochain takes `rank ∂`
re-describable (gauge) parameters plus exactly `n` incompressible
ones. -/
theorem card_edges_eq_finrank_gauge_add :
    Fintype.card G.E
      = Module.finrank ℝ (LinearMap.range (G.gradLin ℝ)) + n := by
  have h := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (G.gradLin ℝ))
  rw [G.finrank_cochainQuot B, Module.finrank_fintype_fun_eq_card] at h
  omega

include B in
/-- **Every lattice basis has exactly `b₁` elements** — the rank is
never a choice (the C3 well-definedness brick, now definitional in
the basis abstraction). -/
theorem card_eq_b1 : n = G.b1 := by
  have h := Module.finrank_eq_card_basis B
  rw [Fintype.card_fin] at h
  exact h.symm

end LatticeBasis

/-! ## The fundamental basis: existence for every finite graph

C2's content with nothing stored: the PID structure theorem produces a
basis of the cycle lattice; `cycleBasisSigma_fst` proves the
construction meets the intrinsic invariant `b₁`. -/

/-- The chosen basis package of the cycle lattice, via the PID
structure theorem. -/
noncomputable def cycleBasisSigma :
    (m : ℕ) × Module.Basis (Fin m) ℤ G.cycleLattice :=
  Submodule.basisOfPid (Pi.basisFun ℤ G.E) G.cycleLattice

/-- **The construction meets the intrinsic invariant**: the PID basis
of the cycle lattice has exactly `b₁ = finrank ℤ H₁(G;ℤ)` elements. -/
theorem cycleBasisSigma_fst : G.cycleBasisSigma.1 = G.b1 :=
  G.card_eq_b1 G.cycleBasisSigma.2

/-- **The fundamental basis of `H₁(G;ℤ)`** — every finite incidence
graph carries a lattice basis, indexed by the intrinsic `b₁`. This is
the fundamental-presentation theorem (C2) in basis form: every former
presentation field is a theorem of this object (review #5). -/
noncomputable def cycleBasis : Module.Basis (Fin G.b1) ℤ G.cycleLattice :=
  G.cycleBasisSigma.2.reindex (finCongr G.cycleBasisSigma_fst)

instance : Module.Free ℤ G.cycleLattice := Module.Free.of_basis G.cycleBasis

theorem finrank_cycleLattice : Module.finrank ℤ G.cycleLattice = G.b1 :=
  rfl

/-- The fundamental integer cycles, as cochains. -/
noncomputable def fundCyclesZ : Fin G.b1 → G.E → ℤ :=
  G.cyclesZ G.cycleBasis

/-- The fundamental cycles, cast to `ℝ`. -/
noncomputable def fundCyclesR : Fin G.b1 → G.E → ℝ :=
  G.cyclesR G.cycleBasis

/-- **Intrinsic `H¹` coordinates for every finite graph** (C2
acceptance): integer cochains modulo integer gradients are `ℤ^{b₁}`,
through the fundamental basis. -/
noncomputable def h1QuotEquiv :
    ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) ≃ₗ[ℤ] (Fin G.b1 → ℤ) :=
  G.latticeQuotEquiv G.cycleBasis

/-- The intrinsic `H¹` coordinates of a class, on representatives. -/
theorem h1QuotEquiv_mk (τ : G.E → ℤ) :
    G.h1QuotEquiv (Submodule.Quotient.mk τ)
      = fun j => τ ⬝ᵥ G.fundCyclesZ j := rfl

/-- Real cochains modulo gradients are `ℝ^{b₁}` — for every finite
graph (C4 acceptance), through the fundamental basis. -/
noncomputable def cochainQuotEquivR :
    ((G.E → ℝ) ⧸ LinearMap.range (G.gradLin ℝ)) ≃ₗ[ℝ] (Fin G.b1 → ℝ) :=
  G.cochainQuotEquiv G.cycleBasis

theorem finrank_cochainQuotR :
    Module.finrank ℝ ((G.E → ℝ) ⧸ LinearMap.range (G.gradLin ℝ))
      = G.b1 :=
  G.finrank_cochainQuot G.cycleBasis

/-! ## The real cycle-space rank, Euler's formula, spanning criterion -/

/-- The real cycle space has dimension `b₁`: the cast fundamental
cycles are a basis of `ker ∂ℝ` — independent by `cast_independent`,
spanning by `spanning`. -/
theorem finrank_ker_boundaryLin :
    Module.finrank ℝ (LinearMap.ker (G.boundaryLin ℝ)) = G.b1 := by
  have hmemc : ∀ i, G.fundCyclesR i ∈ LinearMap.ker (G.boundaryLin ℝ) := by
    intro i
    rw [LinearMap.mem_ker]
    funext v
    exact G.cyclesR_closed G.cycleBasis i v
  set c' : Fin G.b1 → LinearMap.ker (G.boundaryLin ℝ) :=
    fun i => ⟨G.fundCyclesR i, hmemc i⟩ with hc'
  have hsum_coe : ∀ (g : Fin G.b1 → ℝ),
      ((∑ i, g i • c' i : LinearMap.ker (G.boundaryLin ℝ)) : G.E → ℝ)
        = fun e => ∑ i, g i * G.fundCyclesR i e := by
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
    have hgz := G.cast_independent G.cycleBasis g hcoe
    intro i
    exact congrFun hgz i
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range c') := by
    rintro ⟨ω, hω⟩ _
    obtain ⟨a, ha⟩ := G.spanning G.cycleBasis ω (fun v => by
      have := LinearMap.mem_ker.mp hω
      exact congrFun this v)
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨a, ?_⟩
    apply Subtype.ext
    rw [hsum_coe a]
    exact ha.symm
  have h := Module.finrank_eq_card_basis (Module.Basis.mk hli hspan)
  rw [Fintype.card_fin] at h
  exact h

/-- **Euler's formula for every finite graph**, proved in the topology
layer (review #5, finding 1): `b₁ = |E| − |V| + c`, by the real
cycle-space rank, rank–nullity twice, the transpose rank equality, and
the gauge theorem. -/
theorem b1_eq :
    (G.b1 : ℤ) = (Fintype.card G.E : ℤ) - Fintype.card G.V
      + G.componentCard := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (G.boundaryLin ℝ)
  rw [Module.finrank_fintype_fun_eq_card, G.finrank_ker_boundaryLin] at h1
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
  omega

/-- **The spanning criterion** (C5's tool): a closed, linearly
independent family of `b₁` cycle vectors spans the cycle space — by
the real cycle-space rank, with no per-graph constancy argument. -/
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

/-! ## Building a basis from integral cycle data

The concrete-instance bridge: a family of integer cycles that is
closed, real-independent after casting, and integrally spanning
assembles into a lattice basis — from which everything else is
derived, including its own count `r = b₁`. -/

/-- Assemble a lattice basis from closed, independent, integrally
spanning integer cycles. -/
noncomputable def basisOfCycles {r : ℕ} (c : Fin r → G.E → ℤ)
    (hmem : ∀ i, c i ∈ G.cycleLattice)
    (hindep : ∀ x : Fin r → ℝ,
      (fun e => ∑ i, x i * ((c i e : ℤ) : ℝ)) = 0 → x = 0)
    (hspan : ∀ x, x ∈ G.cycleLattice →
      ∃ a : Fin r → ℤ, x = fun e => ∑ i, a i * c i e) :
    Module.Basis (Fin r) ℤ G.cycleLattice := by
  have hli : LinearIndependent ℤ
      (fun i => (⟨c i, hmem i⟩ : G.cycleLattice)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hval := congrArg Subtype.val hg
    rw [AddSubmonoidClass.coe_finset_sum] at hval
    have hcast : (fun e => ∑ i, ((g i : ℝ)) * ((c i e : ℤ) : ℝ)) = 0 := by
      funext e
      have he := congrFun hval e
      rw [Finset.sum_apply] at he
      have heZ : ∑ i, g i * c i e = 0 := he
      show ∑ i, ((g i : ℝ)) * ((c i e : ℤ) : ℝ) = 0
      calc ∑ i, ((g i : ℝ)) * ((c i e : ℤ) : ℝ)
          = ((∑ i, g i * c i e : ℤ) : ℝ) := by push_cast; rfl
        _ = 0 := by rw [heZ, Int.cast_zero]
    have hgz := hindep (fun i => (g i : ℝ)) hcast
    intro i
    have hz : ((g i : ℤ) : ℝ) = 0 := congrFun hgz i
    exact_mod_cast hz
  have hsp : ⊤ ≤ Submodule.span ℤ
      (Set.range fun i => (⟨c i, hmem i⟩ : G.cycleLattice)) := by
    rintro ⟨x, hx⟩ _
    obtain ⟨a, ha⟩ := hspan x hx
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨a, ?_⟩
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    funext e
    rw [Finset.sum_apply]
    exact (congrFun ha e).symm
  exact Module.Basis.mk hli hsp

/-- The assembled basis's integer cycles are the given family. -/
theorem cyclesZ_basisOfCycles {r : ℕ} (c : Fin r → G.E → ℤ)
    (hmem : ∀ i, c i ∈ G.cycleLattice)
    (hindep : ∀ x : Fin r → ℝ,
      (fun e => ∑ i, x i * ((c i e : ℤ) : ℝ)) = 0 → x = 0)
    (hspan : ∀ x, x ∈ G.cycleLattice →
      ∃ a : Fin r → ℤ, x = fun e => ∑ i, a i * c i e) :
    G.cyclesZ (G.basisOfCycles c hmem hindep hspan) = c := by
  funext i
  show ((G.basisOfCycles c hmem hindep hspan) i : G.E → ℤ) = c i
  rw [basisOfCycles, Module.Basis.mk_apply]

private lemma cast_dotProduct {ι : Type v} [Fintype ι] (x y : ι → ℤ) :
    ((x ⬝ᵥ y : ℤ) : ℝ) = (fun e => (x e : ℝ)) ⬝ᵥ (fun e => (y e : ℝ)) := by
  show ((∑ e, x e * y e : ℤ) : ℝ) = ∑ e, (x e : ℝ) * (y e : ℝ)
  push_cast
  rfl

/-- **Primitivity from real spanning and unit-period realizers** (C3's
argument, generalized to raw integral families): if the cast family
spans the real cycle space and every integer period vector is
realized by an integer cochain, then every integral cycle is an
**integer** combination of the family — the real coordinates are the
integers `⟨τ⁽ⁱ⁾, x⟩` for unit-period realizers `τ⁽ⁱ⁾`. -/
theorem exists_int_coords {r : ℕ} (c : Fin r → G.E → ℤ)
    (hspanR : ∀ ω : G.E → ℝ, (∀ v, G.boundary ω v = 0) →
      ∃ a : Fin r → ℝ, ω = fun e => ∑ i, a i * ((c i e : ℤ) : ℝ))
    (honto : ∀ k : Fin r → ℤ, ∃ τ : G.E → ℤ, ∀ j, τ ⬝ᵥ c j = k j)
    {x : G.E → ℤ} (hx : x ∈ G.cycleLattice) :
    ∃ a : Fin r → ℤ, x = fun e => ∑ i, a i * c i e := by
  have hclosed : ∀ v, G.boundary (fun e => ((x e : ℤ) : ℝ)) v = 0 := by
    intro v
    rw [G.boundary_castR, (G.mem_cycleLattice.mp hx) v, Int.cast_zero]
  obtain ⟨aR, haR⟩ := hspanR (fun e => ((x e : ℤ) : ℝ)) hclosed
  choose τ hτ using honto
  refine ⟨fun i => τ (Pi.single i 1) ⬝ᵥ x, ?_⟩
  have key : ∀ i, aR i = ((τ (Pi.single i 1) ⬝ᵥ x : ℤ) : ℝ) := by
    intro i
    have hchain : (fun e => ((τ (Pi.single i 1) e : ℤ) : ℝ))
        ⬝ᵥ (fun e => ∑ j, aR j * ((c j e : ℤ) : ℝ)) = aR i := by
      calc (fun e => ((τ (Pi.single i 1) e : ℤ) : ℝ))
          ⬝ᵥ (fun e => ∑ j, aR j * ((c j e : ℤ) : ℝ))
          = ∑ e, ((τ (Pi.single i 1) e : ℤ) : ℝ)
              * ∑ j, aR j * ((c j e : ℤ) : ℝ) := rfl
        _ = ∑ j, aR j * ∑ e, ((τ (Pi.single i 1) e : ℤ) : ℝ)
              * ((c j e : ℤ) : ℝ) := by
            calc ∑ e, ((τ (Pi.single i 1) e : ℤ) : ℝ)
                  * ∑ j, aR j * ((c j e : ℤ) : ℝ)
                = ∑ e, ∑ j, aR j * (((τ (Pi.single i 1) e : ℤ) : ℝ)
                    * ((c j e : ℤ) : ℝ)) := by
                  refine Finset.sum_congr rfl fun e _ => ?_
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl fun j _ => by ring
              _ = ∑ j, ∑ e, aR j * (((τ (Pi.single i 1) e : ℤ) : ℝ)
                    * ((c j e : ℤ) : ℝ)) := Finset.sum_comm
              _ = ∑ j, aR j * ∑ e, ((τ (Pi.single i 1) e : ℤ) : ℝ)
                    * ((c j e : ℤ) : ℝ) := by
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [Finset.mul_sum]
        _ = ∑ j, aR j * (Pi.single i (1 : ℝ) : Fin r → ℝ) j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            congr 1
            have h1 : (∑ e, ((τ (Pi.single i 1) e : ℤ) : ℝ) * ((c j e : ℤ) : ℝ))
                = ((τ (Pi.single i 1) ⬝ᵥ c j : ℤ) : ℝ) := by
              rw [cast_dotProduct]
              rfl
            rw [h1, hτ (Pi.single i 1) j]
            exact cast_single i j
        _ = aR i := by
            rw [show (fun j => aR j * (Pi.single i (1 : ℝ) : Fin r → ℝ) j)
                = fun j => if j = i then aR j else 0 from funext fun j => by
              rcases eq_or_ne j i with h | h
              · subst h
                rw [if_pos rfl, Pi.single_eq_same, mul_one]
              · rw [if_neg h, Pi.single_eq_of_ne h, mul_zero]]
            rw [Finset.sum_ite_eq' Finset.univ i aR]
            simp
    rw [cast_dotProduct, show (fun e => ((x e : ℤ) : ℝ))
        = fun e => ∑ j, aR j * ((c j e : ℤ) : ℝ) from haR, hchain]
  funext e
  apply Int.cast_injective (α := ℝ)
  have hxe := congrFun haR e
  rw [hxe]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← key i]

end IncidenceGraph

end Meno
