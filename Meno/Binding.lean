import Meno.Matter

/-! # Geometric Binding: attaching faces kills matter (C7)

**The space-changing binding theorem** — the Completion Path's C7, the
original Goal 7. A `TwoComplex` attaches faces to a graph along
integral cycles. On cohomology:

* `TwoComplex.h1` — the complex's `H¹`: cochains with vanishing
  periods around every attached face, modulo gradients.
* `TwoComplex.restrict` — the map induced by `G ↪ X` on `H¹`. It is
  **injective** (`restrict_injective`), with range exactly the
  classes annihilating the attached cycles (`range_restrict`) — the
  acceptance's `attach_dual_image`.
* **`binding_kills_matter`** — a matter sector with nonzero period
  around an attached face does not extend to the filled space. Not
  "its image has zero energy": *there is no image*. The variational
  problem for the killed class is infeasible in `X`
  (`TwoComplex.energy_isLeast` shows the face constraints are free
  for survivors; killed classes fail them at every realizer).
* On homology, `attach_h1`: attaching one face along `c` presents
  `H₁(X) = H₁(G) ⧸ ⟨c⟩`; for **primitive** `c` (some integer cochain
  pairs with it to `1` — equivalently, unit content in the lattice),
  the quotient is **free of rank `b₁ − 1`**
  (`finrank_attach_h1Homology`), by the `IsCompl` splitting
  `H₁(G) = ℤ·c ⊕ ker φ`.
* Spectrally: survivors keep their exact mass
  (`TwoComplex.energy_isLeast` — same `IsLeast` set as in `G`), and
  the spectrum **partitions exactly**: the graph's partition function
  is the complex's plus the killed classes' sum
  (`partFn_add_killed`, an equality). Corollaries: the partition
  function strictly decreases, by at least the killed sector's full
  Boltzmann weight (`attach_partFn_add_le`, `attach_partFn_lt`).
  These are statements about removed *weight* — `exp(−m.mass)` leaves
  the spectrum because the sector leaves the space. No energy is
  claimed to move: the killed sector has no image to carry one. The
  theorem that genuinely releases an energy equal to a rest mass is
  algebraic annihilation (`MatterSector.annihilation`).

The concrete instance — the theta graph with its first basis cycle
filled: `thetaMatter` dies (`theta_binding_kills`), `b₁` drops
`2 → 1` (`theta_attach_finrank`), and the removed weight is at least
`exp(−1/3)` (`theta_removed_weight`) — lives in
`Meno/ThetaBinding.lean` (review #3: this file is generic binding
theory and imports only the matter layer).

With this file, `killed_releases_mass` — the Phase-27 placeholder
that accepted an arbitrary killing map — is deleted from
`Meno/Matter.lean` (discipline 1c): the induced map now exists, and
the theorem is about *it*. -/

namespace Meno

open scoped BigOperators
open Matrix

universe u v w

variable {G : IncidenceGraph.{u, v}}

/-! ## Pairing classes with cycles -/

/-- Pairing with a fixed integer cochain, as a linear map. -/
noncomputable def dotPairing (c : G.E → ℤ) : (G.E → ℤ) →ₗ[ℤ] ℤ where
  toFun ω := ω ⬝ᵥ c
  map_add' ω η := add_dotProduct ω η c
  map_smul' a ω := smul_dotProduct a ω c

/-- Gradients pair to zero with any integral cycle — Stokes at the
lattice level. -/
theorem grad_dotProduct_cycle_eq_zero (g : G.V → ℤ) {c : G.E → ℤ}
    (hc : c ∈ G.cycleLattice) : G.grad g ⬝ᵥ c = 0 := by
  rw [G.grad_dotProduct_eq]
  exact Finset.sum_eq_zero fun v _ => by
    rw [(G.mem_cycleLattice.mp hc) v, mul_zero]

/-- **Pairing an `H¹` class with an integral cycle**: well-defined by
Stokes — gradients are invisible to cycles. -/
noncomputable def IncidenceGraph.classPairing (G : IncidenceGraph.{u, v})
    (c : G.E → ℤ) (hc : c ∈ G.cycleLattice) :
    ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) →ₗ[ℤ] ℤ :=
  Submodule.liftQ _ (dotPairing c) (by
    rintro _ ⟨g, rfl⟩
    exact grad_dotProduct_cycle_eq_zero g hc)

theorem IncidenceGraph.classPairing_mk (c : G.E → ℤ) (hc : c ∈ G.cycleLattice)
    (ω : G.E → ℤ) :
    G.classPairing c hc (Submodule.Quotient.mk ω) = ω ⬝ᵥ c := rfl

/-! ## Two-complexes -/

/-- A 2-complex over `G`: faces attached along integral cycles. -/
structure TwoComplex (G : IncidenceGraph.{u, v}) where
  /-- The face index. -/
  Faces : Type w
  /-- The attaching cycle of each face. -/
  face : Faces → G.E → ℤ
  /-- Attaching maps are cycles. -/
  face_mem : ∀ i, face i ∈ G.cycleLattice

namespace TwoComplex

variable (X : TwoComplex.{u, v, w} G)

/-- The cocycles of the complex: integer cochains with vanishing
periods around every attached face. -/
noncomputable def cocycles : Submodule ℤ (G.E → ℤ) where
  carrier := {ω | ∀ i, ω ⬝ᵥ X.face i = 0}
  add_mem' := fun hω hη i => by
    rw [add_dotProduct]
    rw [hω i, hη i, add_zero]
  zero_mem' := fun i => zero_dotProduct _
  smul_mem' := fun a ω hω i => by
    rw [smul_dotProduct]
    rw [hω i, smul_zero]

theorem mem_cocycles {ω : G.E → ℤ} :
    ω ∈ X.cocycles ↔ ∀ i, ω ⬝ᵥ X.face i = 0 := Iff.rfl

/-- `H¹` of the complex: face-annihilating cochains modulo
gradients. -/
noncomputable def h1 : Type v :=
  ↥X.cocycles ⧸
    (LinearMap.range (G.gradLin ℤ)).comap X.cocycles.subtype

noncomputable instance : AddCommGroup X.h1 :=
  inferInstanceAs (AddCommGroup (↥X.cocycles ⧸
    (LinearMap.range (G.gradLin ℤ)).comap X.cocycles.subtype))

noncomputable instance : Module ℤ X.h1 :=
  inferInstanceAs (Module ℤ (↥X.cocycles ⧸
    (LinearMap.range (G.gradLin ℤ)).comap X.cocycles.subtype))

/-- The comap'd gradients are exactly the kernel of
"include, then take the `G`-class". -/
theorem comap_eq_ker :
    (LinearMap.range (G.gradLin ℤ)).comap X.cocycles.subtype
      = LinearMap.ker ((LinearMap.range (G.gradLin ℤ)).mkQ.comp
          X.cocycles.subtype) := by
  rw [LinearMap.ker_comp, Submodule.ker_mkQ]

/-- **The induced map on `H¹`**: a class of the complex restricts to a
class of the graph. -/
noncomputable def restrict :
    X.h1 →ₗ[ℤ] ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :=
  Submodule.liftQ _
    ((LinearMap.range (G.gradLin ℤ)).mkQ.comp X.cocycles.subtype)
    (X.comap_eq_ker).le

/-- **Injectivity of the restriction** (half of `attach_dual_image`):
`H¹(X)` embeds in `H¹(G)` — filling faces destroys classes, it never
creates or conflates them. -/
theorem restrict_injective : Function.Injective X.restrict :=
  LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot' _ _ X.comap_eq_ker)

/-- The surviving classes: those annihilating every attached cycle. -/
noncomputable def survivors :
    Submodule ℤ ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :=
  ⨅ i, LinearMap.ker (G.classPairing (X.face i) (X.face_mem i))

theorem mem_survivors
    {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)} :
    κ ∈ X.survivors
      ↔ ∀ i, G.classPairing (X.face i) (X.face_mem i) κ = 0 := by
  unfold survivors
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]

/-- **The image of the restriction** (the other half of
`attach_dual_image`): exactly the classes that annihilate the
attached cycles. `H¹(X) ↪ H¹(G)` with image `{φ | φ(c) = 0}`. -/
theorem range_restrict : LinearMap.range X.restrict = X.survivors := by
  have h1 : LinearMap.range X.restrict
      = X.cocycles.map (LinearMap.range (G.gradLin ℤ)).mkQ := by
    rw [restrict, Submodule.range_liftQ, LinearMap.range_comp,
      Submodule.range_subtype]
  rw [h1]
  ext κ
  constructor
  · rintro ⟨ω, hω, rfl⟩
    rw [X.mem_survivors]
    intro i
    show ω ⬝ᵥ X.face i = 0
    exact (X.mem_cocycles.mp hω) i
  · intro hκ
    obtain ⟨τ, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
    refine ⟨τ, ?_, rfl⟩
    intro i
    have := (X.mem_survivors.mp hκ) i
    rwa [G.classPairing_mk] at this
  -- `Submodule.Quotient.mk` and `mkQ` agree definitionally.

/-- **BINDING KILLS MATTER** (C7's heart, the original Goal 7): a
matter sector with nonzero period around an attached face does not
extend to the filled space — there is no class of the complex
restricting to it. The paradox the sector stores is resolved by the
face, and the sector ceases to exist. -/
theorem binding_kills_matter (m : MatterSector G) (i : X.Faces)
    (hm : G.classPairing (X.face i) (X.face_mem i) m.val ≠ 0) :
    ¬ ∃ κ' : X.h1, X.restrict κ' = m.val := by
  rintro ⟨κ', hκ'⟩
  apply hm
  have hmem : m.val ∈ LinearMap.range X.restrict := ⟨κ', hκ'⟩
  rw [X.range_restrict, X.mem_survivors] at hmem
  exact hmem i

end TwoComplex

/-! ## Attaching a single face -/

/-- The complex obtained by attaching one face along the cycle `c`. -/
noncomputable def IncidenceGraph.attach (G : IncidenceGraph.{u, v})
    (c : G.E → ℤ) (hc : c ∈ G.cycleLattice) : TwoComplex.{u, v, w} G :=
  ⟨PUnit, fun _ => c, fun _ => hc⟩

/-! ## Homology: `H₁(X) = H₁(G) ⧸ ⟨c⟩`, free of rank `b₁ − 1` -/

/-- `H₁` of the complex: the cycle lattice modulo the attached
faces. -/
noncomputable def TwoComplex.h1Homology (X : TwoComplex.{u, v, w} G) :
    Type v :=
  ↥G.cycleLattice ⧸ Submodule.span ℤ
    (Set.range fun i => (⟨X.face i, X.face_mem i⟩ : G.cycleLattice))

noncomputable instance (X : TwoComplex.{u, v, w} G) :
    AddCommGroup X.h1Homology :=
  inferInstanceAs (AddCommGroup (↥G.cycleLattice ⧸ Submodule.span ℤ
    (Set.range fun i => (⟨X.face i, X.face_mem i⟩ : G.cycleLattice))))

noncomputable instance (X : TwoComplex.{u, v, w} G) :
    Module ℤ X.h1Homology :=
  inferInstanceAs (Module ℤ (↥G.cycleLattice ⧸ Submodule.span ℤ
    (Set.range fun i => (⟨X.face i, X.face_mem i⟩ : G.cycleLattice))))

section Splitting

variable (c : G.E → ℤ) (hc : c ∈ G.cycleLattice)

/-- **`attach_h1`** (acceptance): attaching one face along `c`
presents the quotient `H₁(G;ℤ) ⧸ ⟨c⟩`. -/
noncomputable def attach_h1 :
    (G.attach c hc : TwoComplex.{u, v, w} G).h1Homology ≃ₗ[ℤ]
      (↥G.cycleLattice ⧸ (ℤ ∙ (⟨c, hc⟩ : G.cycleLattice))) :=
  Submodule.quotEquivOfEq _ _ (by
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      rfl
    · rintro rfl
      exact ⟨PUnit.unit, rfl⟩)

variable (τ : G.E → ℤ)

/-- Pairing the cycle lattice against a fixed cochain. -/
noncomputable def latticePairing : ↥G.cycleLattice →ₗ[ℤ] ℤ where
  toFun x := (x : G.E → ℤ) ⬝ᵥ τ
  map_add' x y := by
    show ((x : G.E → ℤ) + (y : G.E → ℤ)) ⬝ᵥ τ = _
    rw [add_dotProduct]
  map_smul' a x := by
    show ((a • (x : G.E → ℤ)) ⬝ᵥ τ) = _
    rw [smul_dotProduct]
    rfl

/-- **The primitive splitting**: if some cochain pairs with `c` to
`1`, the cycle lattice splits as `ℤ·c ⊕ ker φ`. -/
theorem isCompl_span_ker (hτ : c ⬝ᵥ τ = 1) :
    IsCompl (ℤ ∙ (⟨c, hc⟩ : G.cycleLattice))
      (LinearMap.ker (latticePairing (G := G) τ)) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hk
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have h0 : latticePairing (G := G) τ (a • ⟨c, hc⟩) = 0 :=
      LinearMap.mem_ker.mp hk
    rw [map_smul] at h0
    have hpc : latticePairing (G := G) τ ⟨c, hc⟩ = 1 := hτ
    rw [hpc, smul_eq_mul, mul_one] at h0
    rw [h0, zero_smul]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hdecomp : x = latticePairing (G := G) τ x • (⟨c, hc⟩ : G.cycleLattice)
        + (x - latticePairing (G := G) τ x • ⟨c, hc⟩) := by
      abel
    rw [hdecomp]
    refine Submodule.add_mem_sup
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) ?_
    rw [LinearMap.mem_ker, map_sub, map_smul]
    have hpc : latticePairing (G := G) τ ⟨c, hc⟩ = 1 := hτ
    rw [hpc, smul_eq_mul, mul_one, sub_self]

/-- `H₁` of the attached complex, split off: the kernel of the
primitive functional. -/
noncomputable def attachH1EquivKer (hτ : c ⬝ᵥ τ = 1) :
    (G.attach c hc : TwoComplex.{u, v, w} G).h1Homology ≃ₗ[ℤ]
      LinearMap.ker (latticePairing (G := G) τ) :=
  (attach_h1 c hc).trans
    (Submodule.quotientEquivOfIsCompl _ _ (isCompl_span_ker c hc τ hτ))

/-- The span of a primitive cycle is a line: `ℤ ≃ₗ ℤ·c`. -/
noncomputable def spanLineEquiv (hτ : c ⬝ᵥ τ = 1) :
    ℤ ≃ₗ[ℤ] ↥(ℤ ∙ (⟨c, hc⟩ : G.cycleLattice)) where
  toFun a := ⟨a • (⟨c, hc⟩ : G.cycleLattice),
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)⟩
  invFun y := latticePairing (G := G) τ (y : G.cycleLattice)
  left_inv a := by
    show latticePairing (G := G) τ (a • ⟨c, hc⟩) = a
    rw [map_smul]
    have hpc : latticePairing (G := G) τ ⟨c, hc⟩ = 1 := hτ
    rw [hpc, smul_eq_mul, mul_one]
  right_inv y := by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp y.2
    apply Subtype.ext
    show latticePairing (G := G) τ (y : G.cycleLattice) • (⟨c, hc⟩ : G.cycleLattice)
      = (y : G.cycleLattice)
    rw [← ha, map_smul]
    have hpc : latticePairing (G := G) τ ⟨c, hc⟩ = 1 := hτ
    rw [hpc, smul_eq_mul, mul_one]
  map_add' a b := by
    apply Subtype.ext
    show (a + b) • (⟨c, hc⟩ : G.cycleLattice)
      = a • (⟨c, hc⟩ : G.cycleLattice) + b • ⟨c, hc⟩
    rw [add_smul]
  map_smul' a b := by
    apply Subtype.ext
    show (a * b) • (⟨c, hc⟩ : G.cycleLattice)
      = a • (b • (⟨c, hc⟩ : G.cycleLattice))
    exact (smul_smul a b _).symm

/-- **`H₁` of the filled complex is free** (acceptance): the quotient
by a primitive cycle carries a basis. -/
noncomputable def attachH1Basis :
    Σ n : ℕ, Module.Basis (Fin n) ℤ
      (LinearMap.ker (latticePairing (G := G) τ)) :=
  Submodule.basisOfPid G.cycleBasis _

/-- **The rank drops by exactly one** (acceptance): `H₁` of the
complex obtained by filling a primitive cycle has rank `b₁ − 1`. One
face, one sector — the count is exact. -/
theorem finrank_attach_h1Homology (hτ : c ⬝ᵥ τ = 1) :
    Module.finrank ℤ
        (G.attach c hc : TwoComplex.{u, v, w} G).h1Homology
      = G.b1 - 1 := by
  haveI hkfree : Module.Free ℤ
      ↥(LinearMap.ker (latticePairing (G := G) τ)) :=
    Module.Free.of_basis (attachH1Basis (G := G) τ).2
  haveI hkfin : Module.Finite ℤ
      ↥(LinearMap.ker (latticePairing (G := G) τ)) :=
    Module.Finite.of_basis (attachH1Basis (G := G) τ).2
  haveI hsfree : Module.Free ℤ ↥(ℤ ∙ (⟨c, hc⟩ : G.cycleLattice)) :=
    Module.Free.of_equiv (spanLineEquiv c hc τ hτ)
  haveI hsfin : Module.Finite ℤ ↥(ℤ ∙ (⟨c, hc⟩ : G.cycleLattice)) :=
    Module.Finite.equiv (spanLineEquiv c hc τ hτ)
  -- span ⊕ ker fills the lattice: ranks add to b₁
  have hprod :=
    (Submodule.prodEquivOfIsCompl _ _ (isCompl_span_ker c hc τ hτ)).finrank_eq
  rw [Module.finrank_prod, G.finrank_cycleLattice] at hprod
  -- the span is a line
  have hspan : Module.finrank ℤ ↥(ℤ ∙ (⟨c, hc⟩ : G.cycleLattice)) = 1 := by
    rw [← (spanLineEquiv c hc τ hτ).finrank_eq, Module.finrank_self]
  rw [hspan] at hprod
  -- transport along the splitting equivalence
  rw [(attachH1EquivKer c hc τ hτ).finrank_eq]
  omega

end Splitting

/-! ## The spectrum: survivors keep their mass, the killed weight is removed -/

/-- The partition function read directly over `H¹(G;ℤ)`. -/
noncomputable def IncidenceGraph.classPartFn (G : IncidenceGraph.{u, v}) : ℝ :=
  ∑' κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ),
    Real.exp (-G.harmonicEnergy κ)

/-- The class-level partition function *is* the intrinsic carrier's
(`classSectorAction`, `Meno/BasisIndependence.lean`) — definitionally. -/
theorem IncidenceGraph.classPartFn_eq_classSectorAction
    (G : IncidenceGraph.{u, v}) :
    G.classPartFn = (G.classSectorAction).partFn := rfl

/-- The class-level partition function is the graph's partition
function — the fundamental instance of
`basisGramData_partFn_eq_tsum_classes` (C3). -/
theorem IncidenceGraph.classPartFn_eq_partFn (G : IncidenceGraph.{u, v}) :
    G.classPartFn = G.partFn :=
  (G.basisGramData_partFn_eq_tsum_classes G.cycleBasis).symm

namespace TwoComplex

variable (X : TwoComplex.{u, v, w} G)

/-- The partition function of the complex: Boltzmann sum over its own
`H¹`, with each class weighed by the harmonic energy of its
restriction — justified as `X`'s intrinsic variational minimum by
`energy_isLeast` below. -/
noncomputable def partFn : ℝ :=
  ∑' κ' : X.h1, Real.exp (-G.harmonicEnergy (X.restrict κ'))

/-- **Survivors keep their exact mass** (the `X`-side variational
identity): the harmonic energy of a surviving class is the least
cochain energy among realizers *satisfying the face constraints* —
and it coincides with the unconstrained `G`-minimum, because every
realizer of a surviving class satisfies the face constraints for
free. -/
theorem energy_isLeast (κ' : X.h1) :
    IsLeast {E : ℝ | ∃ ω : G.E → ℝ,
        ((∀ j, ω ⬝ᵥ G.fundCyclesR j
            = ((G.h1QuotEquiv (X.restrict κ')) j : ℝ))
          ∧ ∀ i, ω ⬝ᵥ (fun e => ((X.face i e : ℤ) : ℝ)) = 0)
        ∧ E = ω ⬝ᵥ ω}
      (G.harmonicEnergy (X.restrict κ')) := by
  have hsurv : X.restrict κ' ∈ X.survivors := by
    rw [← X.range_restrict]
    exact ⟨κ', rfl⟩
  have hface : ∀ (ω : G.E → ℝ),
      (∀ j, ω ⬝ᵥ G.fundCyclesR j
        = ((G.h1QuotEquiv (X.restrict κ')) j : ℝ)) →
      ∀ i, ω ⬝ᵥ (fun e => ((X.face i e : ℤ) : ℝ)) = 0 := by
    intro ω hper i
    obtain ⟨τ, hτ⟩ := Submodule.Quotient.mk_surjective _ (X.restrict κ')
    -- ω = τ̂ + grad f, by the basis-free realizer characterization
    have hiff := G.periods_eq_cast_iff G.cycleBasis τ ω
    have hper' : ∀ j, ω ⬝ᵥ G.cyclesR G.cycleBasis j
        = ((τ ⬝ᵥ G.cyclesZ G.cycleBasis j : ℤ) : ℝ) := by
      intro j
      have := hper j
      rw [← hτ, G.h1QuotEquiv_mk τ] at this
      exact this
    obtain ⟨f, rfl⟩ := hiff.mp hper'
    rw [add_dotProduct]
    -- the gradient part: real Stokes against a closed cochain
    have hgrad : G.grad f ⬝ᵥ (fun e => ((X.face i e : ℤ) : ℝ)) = 0 := by
      rw [G.grad_dotProduct_eq]
      refine Finset.sum_eq_zero fun v _ => ?_
      rw [G.boundary_castR, (G.mem_cycleLattice.mp (X.face_mem i)) v,
        Int.cast_zero, mul_zero]
    -- the integral part: the surviving class annihilates the face
    have hint : (fun e => ((τ e : ℤ) : ℝ))
        ⬝ᵥ (fun e => ((X.face i e : ℤ) : ℝ))
        = ((τ ⬝ᵥ X.face i : ℤ) : ℝ) := by
      show ∑ e, ((τ e : ℤ) : ℝ) * ((X.face i e : ℤ) : ℝ)
        = ((∑ e, τ e * X.face i e : ℤ) : ℝ)
      push_cast
      rfl
    have hzero : τ ⬝ᵥ X.face i = 0 := by
      have := (X.mem_survivors.mp hsurv) i
      rw [← hτ, G.classPairing_mk] at this
      exact this
    rw [hint, hgrad, hzero, Int.cast_zero, add_zero]
  have hbase := G.harmonicEnergy_isLeast (X.restrict κ')
  constructor
  · obtain ⟨ω, hω, hE⟩ := hbase.1
    exact ⟨ω, ⟨hω, hface ω hω⟩, hE⟩
  · rintro E ⟨ω, ⟨hω, _⟩, hE⟩
    exact hbase.2 ⟨ω, hω, hE⟩

/-- The classes of the complex are exactly the surviving classes of
the graph. -/
noncomputable def survivorEquiv : X.h1 ≃ ↥X.survivors :=
  Equiv.ofBijective
    (fun κ' => ⟨X.restrict κ', by
      rw [← X.range_restrict]
      exact ⟨κ', rfl⟩⟩)
    ⟨fun a b hab => X.restrict_injective (congrArg Subtype.val hab),
     fun st => by
      have hst : (st : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))
          ∈ LinearMap.range X.restrict := by
        rw [X.range_restrict]
        exact st.2
      obtain ⟨κ', hκ'⟩ := hst
      exact ⟨κ', Subtype.ext hκ'⟩⟩

/-- The complex's partition function is the survivor sum. -/
theorem partFn_eq_survivors :
    X.partFn = ∑' s : ↥X.survivors, Real.exp (-G.harmonicEnergy s.val) := by
  unfold partFn
  rw [← Equiv.tsum_eq X.survivorEquiv
    (fun s : ↥X.survivors => Real.exp (-G.harmonicEnergy s.val))]
  exact tsum_congr fun κ' => rfl

/-- **THE EXACT SPECTRAL DECOMPOSITION** (C7): the graph's partition
function is the complex's partition function *plus* the killed
classes' Boltzmann sum — an equality, not a bound. Filling faces
partitions the spectrum into survivors and casualties. -/
theorem partFn_add_killed :
    X.partFn + (∑' κ : ↥((X.survivors :
        Set ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))))ᶜ,
      Real.exp (-G.harmonicEnergy κ.val)) = G.classPartFn := by
  have hSum := G.summable_classWeight
  have hsplit := hSum.tsum_subtype_add_tsum_subtype_compl
    (X.survivors : Set ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)))
  have hX : X.partFn = ∑' s : ↥X.survivors,
      Real.exp (-G.harmonicEnergy s.val) := X.partFn_eq_survivors
  have hG : G.classPartFn
      = ∑' κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ),
        Real.exp (-G.harmonicEnergy κ) := rfl
  rw [hX, hG, ← hsplit]
  rfl

/-- **The removed-weight bound** (corollary of the exact
decomposition): filling a face that a matter sector wraps removes at
least the sector's entire Boltzmann weight from the spectrum —
`exp(−mass)` leaves because the sector leaves. A statement about
weight, not a moved energy: the killed sector has no image to carry
one. -/
theorem attach_partFn_add_le (m : MatterSector G) (i : X.Faces)
    (hm : G.classPairing (X.face i) (X.face_mem i) m.val ≠ 0) :
    X.partFn + Real.exp (-m.mass) ≤ G.classPartFn := by
  have hSum := G.summable_classWeight
  have hmem : m.val ∈ ((X.survivors :
      Set ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))))ᶜ := by
    intro hmem
    exact hm ((X.mem_survivors.mp hmem) i)
  have hcompl : Real.exp (-m.mass)
      ≤ ∑' κ : ↥((X.survivors :
          Set ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))))ᶜ,
        Real.exp (-G.harmonicEnergy κ.val) := by
    have hsub : Summable (fun κ : ↥((X.survivors :
        Set ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))))ᶜ =>
          Real.exp (-G.harmonicEnergy κ.val)) :=
      hSum.subtype _
    have hterm := hsub.sum_le_tsum ({⟨m.val, hmem⟩} :
        Finset ↥((X.survivors :
          Set ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))))ᶜ)
      (fun κ _ => (Real.exp_pos _).le)
    rwa [Finset.sum_singleton] at hterm
  rw [← X.partFn_add_killed]
  exact add_le_add_right hcompl _

/-- **The partition function strictly decreases** (acceptance,
corollary of the decomposition): the filled space weighs strictly
less — the killed sector's weight is gone. -/
theorem attach_partFn_lt (m : MatterSector G) (i : X.Faces)
    (hm : G.classPairing (X.face i) (X.face_mem i) m.val ≠ 0) :
    X.partFn < G.classPartFn := by
  have h := X.attach_partFn_add_le m i hm
  have hpos := Real.exp_pos (-m.mass)
  linarith

end TwoComplex

end Meno
