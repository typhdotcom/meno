import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Unique
import Mathlib.Data.Set.Image
import Mathlib.Tactic

/-! # SGD — Abstract Framework -/

namespace SGD

universe u

/-! ## Pullback Infrastructure -/

/-- The fiber of a function over a point. -/
abbrev Fiber {A D : Type u} (f : A → D) (d : D) : Type u :=
  { a : A // f a = d }

/-- The product of fibers over a common base point. -/
abbrev FiberProd {A B D : Type u} (f : A → D) (g : B → D) (d : D) : Type u :=
  Fiber f d × Fiber g d

/-- The pullback (fiber product) of two types over a shared base. -/
def Pullback {A B D : Type u} (f : A → D) (g : B → D) : Type u :=
  { p : A × B // f p.1 = g p.2 }

/-- The shared base value of a pullback element. -/
def Pullback.base {A B D : Type u} {f : A → D} {g : B → D} (p : Pullback f g) : D :=
  f p.val.1

/-- The fundamental equivalence: pullback factors through sigma of fiber products. -/
def Pullback.equivSigmaFiber {A B D : Type u} (f : A → D) (g : B → D) :
    Pullback f g ≃ Σ d : D, FiberProd f g d where
  toFun p := ⟨p.base, ⟨p.val.1, rfl⟩, ⟨p.val.2, p.property.symm ▸ rfl⟩⟩
  invFun x := ⟨(x.2.1.val, x.2.2.val), x.2.1.property.trans x.2.2.property.symm⟩
  left_inv _ := Subtype.ext rfl
  right_inv := fun ⟨_, ⟨_, ha⟩, ⟨_, hb⟩⟩ => by subst ha; rfl

/-- The fiber of the pullback's base map over `d` is the product of
the two fibers over `d` (review #10 — the counting engine of the
shared-base coupling). -/
def Pullback.baseFiberEquiv {A B D : Type u} (f : A → D) (g : B → D)
    (d : D) :
    {p : Pullback f g // p.base = d} ≃ Fiber f d × Fiber g d where
  toFun p := (⟨p.val.val.1, p.prop⟩,
    ⟨p.val.val.2, p.val.prop.symm.trans p.prop⟩)
  invFun x := ⟨⟨(x.1.val, x.2.val), x.1.prop.trans x.2.prop.symm⟩, x.1.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The fiber of the pullback's first projection over `x` is the
`g`-fiber over `f x` (review #10 — the first marginal's counting
engine). -/
def Pullback.fstFiberEquiv {A B D : Type u} (f : A → D) (g : B → D)
    (x : A) :
    {p : Pullback f g // p.val.1 = x} ≃ Fiber g (f x) where
  toFun p := ⟨p.val.val.2, p.val.prop.symm.trans (congrArg f p.prop)⟩
  invFun y := ⟨⟨(x, y.val), y.prop.symm⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext p.prop.symm rfl
  right_inv y := rfl

/-- The fiber of the pullback's second projection over `y` is the
`f`-fiber over `g y` (review #10 — the second marginal's counting
engine). -/
def Pullback.sndFiberEquiv {A B D : Type u} (f : A → D) (g : B → D)
    (y : B) :
    {p : Pullback f g // p.val.2 = y} ≃ Fiber f (g y) where
  toFun p := ⟨p.val.val.1, p.val.prop.trans (congrArg g p.prop)⟩
  invFun x := ⟨⟨(x.val, y), x.prop⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl p.prop.symm
  right_inv x := rfl

/-! ## Axiom 1: The Weighted Universe — Complexity Hierarchy -/

/-- Level 1: Base complexity measure (subadditive).
    Codomain M is typically ℝ≥0∞ or similar ordered additive monoid. -/
class ComplexityMeasure (M : Type*) [AddCommMonoid M] [PartialOrder M] where
  C : Type u → M
  unique_zero : ∀ (A : Type u) [Unique A], C A = 0
  congr : ∀ {A B : Type u}, A ≃ B → C A = C B
  prod_le : ∀ (A B : Type u), C (A × B) ≤ C A + C B

/-- Level 2: Sigma subadditivity.
    C(Σ d, P d) ≤ C(D) + sup_d C(P d). This is a capacity bound. -/
class SigmaComplexity (M : Type*) [AddCommMonoid M] [PartialOrder M] [SupSet M]
    extends ComplexityMeasure (M := M) where
  sigma_le : ∀ (D : Type u) (P : D → Type u),
    C (Σ d, P d) ≤ C D + ⨆ (d : D), C (P d)

/-- Level 3: Additive complexity (scarcity).
    Products cost exactly the sum. Structural economy only emerges here. -/
class AdditiveComplexity (M : Type*) [AddCommMonoid M] [PartialOrder M] [SupSet M]
    extends SigmaComplexity (M := M) where
  prod_eq : ∀ (A B : Type u), C (A × B) = C A + C B

/-! ## The Refactoring Bound (THEOREM, not axiom) -/

section RefactoringBound

variable {M : Type*} [ConditionallyCompleteLattice M] [AddCommMonoid M] [IsOrderedAddMonoid M]
variable [inst : SigmaComplexity M]
variable {A B D : Type u} (f : A → D) (g : B → D)

omit [IsOrderedAddMonoid M] in
/-- Pullback complexity via sigma-fiber equivalence. -/
lemma pullback_complexity_eq :
    inst.C (Pullback f g) = inst.C (Σ d : D, FiberProd f g d) :=
  inst.congr (Pullback.equivSigmaFiber f g)

omit [IsOrderedAddMonoid M] in
/-- Fiber products bounded by sum of fiber complexities. -/
lemma fiberProd_le (d : D) :
    inst.C (FiberProd f g d) ≤ inst.C (Fiber f d) + inst.C (Fiber g d) :=
  inst.prod_le _ _

/-- **Sharp refactoring bound**: pullback ≤ base + supremum of paired fiber costs.
    C(A ×_D B) ≤ C(D) + sup_d (C(Fiber f d) + C(Fiber g d)). -/
theorem refactoring_bound_fiberwise
    (hfg : BddAbove (Set.range fun d => inst.C (Fiber f d) + inst.C (Fiber g d)))
    (hne : Nonempty D) :
    inst.C (Pullback f g) ≤
      inst.C D + (⨆ d, (inst.C (Fiber f d) + inst.C (Fiber g d))) := by
  rw [pullback_complexity_eq]
  have key : ⨆ d, inst.C (FiberProd f g d) ≤ ⨆ d, (inst.C (Fiber f d) + inst.C (Fiber g d)) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨d, rfl⟩
    exact (fiberProd_le f g d).trans (le_csSup hfg (Set.mem_range_self d))
  calc inst.C (Σ d, FiberProd f g d)
      ≤ inst.C D + ⨆ d, inst.C (FiberProd f g d) := inst.sigma_le D _
    _ ≤ inst.C D + (⨆ d, (inst.C (Fiber f d) + inst.C (Fiber g d))) :=
        add_le_add_right key _

/-- Coarse refactoring bound obtained by decoupling the two fiber suprema. -/
theorem refactoring_bound
    (hf : BddAbove (Set.range fun d => inst.C (Fiber f d)))
    (hg : BddAbove (Set.range fun d => inst.C (Fiber g d)))
    (hne : Nonempty D) :
    inst.C (Pullback f g) ≤
      inst.C D + (⨆ d, inst.C (Fiber f d)) + (⨆ d, inst.C (Fiber g d)) := by
  have hfg : BddAbove (Set.range fun d => inst.C (Fiber f d) + inst.C (Fiber g d)) := by
    refine ⟨(⨆ d, inst.C (Fiber f d)) + (⨆ d, inst.C (Fiber g d)), ?_⟩
    rintro _ ⟨d, rfl⟩
    exact add_le_add (le_csSup hf (Set.mem_range_self d))
      (le_csSup hg (Set.mem_range_self d))
  have hsharp := refactoring_bound_fiberwise (f := f) (g := g) hfg hne
  have hsplit : (⨆ d, (inst.C (Fiber f d) + inst.C (Fiber g d))) ≤
      (⨆ d, inst.C (Fiber f d)) + (⨆ d, inst.C (Fiber g d)) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨d, rfl⟩
    exact add_le_add (le_csSup hf (Set.mem_range_self d))
      (le_csSup hg (Set.mem_range_self d))
  have hsplit' :
      inst.C D + (⨆ d, (inst.C (Fiber f d) + inst.C (Fiber g d))) ≤
      inst.C D + ((⨆ d, inst.C (Fiber f d)) + (⨆ d, inst.C (Fiber g d))) := by
    simpa [add_assoc, add_comm, add_left_comm] using add_le_add_right hsplit (inst.C D)
  calc inst.C (Pullback f g)
      ≤ inst.C D + (⨆ d, (inst.C (Fiber f d) + inst.C (Fiber g d))) := hsharp
    _ ≤ inst.C D + ((⨆ d, inst.C (Fiber f d)) + (⨆ d, inst.C (Fiber g d))) :=
        hsplit'
    _ = inst.C D + (⨆ d, inst.C (Fiber f d)) + (⨆ d, inst.C (Fiber g d)) := by
        rw [add_assoc]

end RefactoringBound

/-! ## Domain-Generic Additive Complexity — THE ONE GRAVITY ENGINE

The algebraic core shared by all additive complexity measures: a
unit, equivalence, product, and the laws that make C a monoid
homomorphism into (M, +). **`algebraic_gravity` below is the one
gravity theorem of the program** (review #21): the type-level
`gravity` is its corollary at the counting instance
(`instAdditiveComplexityOnType`), the priced
`SectorAction.complexity_gravity` (`Meno/InfoRatchet.lean`) is its
corollary at the pricing instance
(`instAdditiveComplexityOnSectorAction`,
`Meno/UniformAction.lean`), and the groupoid shared-component
identity (`Meno/Groupoid.lean`) is its corollary at the groupoid
instance. -/

/-- Additive complexity on a domain D, valued in M.
    Captures the algebraic fragment common to the type-level hierarchy
    (AdditiveComplexity, which adds sigma bounds), the priced sector
    calculus, and groupoid complexity. -/
class AdditiveComplexityOn (D : Type*) (M : Type*) [AddCommMonoid M] where
  C : D → M
  unit : D
  equiv : D → D → Prop
  prod : D → D → D
  unit_zero : C unit = 0
  congr : {a b : D} → equiv a b → C a = C b
  prod_add : (a b : D) → C (prod a b) = C a + C b

/-- Any type-level `AdditiveComplexity` instance yields an `AdditiveComplexityOn` instance.
    This extraction witnesses that the domain-generic axioms were always implicit
    in the type-level hierarchy. -/
noncomputable instance instAdditiveComplexityOnType
    (M : Type*) [AddCommMonoid M] [PartialOrder M] [SupSet M]
    [inst : AdditiveComplexity M] : AdditiveComplexityOn (Type u) M where
  C := inst.C
  unit := PUnit
  equiv A B := Nonempty (A ≃ B)
  prod A B := A × B
  unit_zero := inst.unique_zero PUnit
  congr h := inst.congr h.some
  prod_add := inst.prod_eq

/-- **ALGEBRAIC GRAVITY — the one gravity engine** (review #21):
merging two structures sharing a component d saves exactly C(d).
Every gravity identity of the program is this theorem at an
instance: counting (`gravity`, at `instAdditiveComplexityOnType`),
pricing (`SectorAction.complexity_gravity`), groupoid
(`GroupoidObj.shared_component_identity`). -/
theorem AdditiveComplexityOn.algebraic_gravity {D M : Type*}
    [AddCommMonoid M] [inst : AdditiveComplexityOn D M] (d f g : D) :
    inst.C (inst.prod d (inst.prod f g)) + inst.C d =
    inst.C (inst.prod d f) + inst.C (inst.prod d g) := by
  simp only [inst.prod_add]; abel

/-! ## Gravity (Uniform Fiber Case) -/

section Gravity

variable {M : Type*} [AddCommMonoid M] [PartialOrder M]
variable [SupSet M] [inst : AdditiveComplexity M]

/-- **Gravity at the counting instance** (review #21): for any maps
f : A → D, g : B → D with uniform fibers (all fibers of f isomorphic
to F, all fibers of g isomorphic to G), the pullback saves exactly
C(D). The sigma-fiber decompositions supply
`Pullback f g ≃ D × (F × G)`, `A ≃ D × F`, `B ≃ D × G`; the identity
itself is `algebraic_gravity` at `instAdditiveComplexityOnType` —
**invoked, not reproved**. -/
theorem gravity {A B D F G : Type u} (f : A → D) (g : B → D)
    (ef : ∀ d, Fiber f d ≃ F) (eg : ∀ d, Fiber g d ≃ G) :
    inst.C (Pullback f g) + inst.C D = inst.C A + inst.C B := by
  have hA : inst.C A = inst.C (D × F) :=
    inst.congr ((Equiv.sigmaFiberEquiv f).symm.trans
      ((Equiv.sigmaCongrRight ef).trans (Equiv.sigmaEquivProd D F)))
  have hB : inst.C B = inst.C (D × G) :=
    inst.congr ((Equiv.sigmaFiberEquiv g).symm.trans
      ((Equiv.sigmaCongrRight eg).trans (Equiv.sigmaEquivProd D G)))
  have hP : inst.C (Pullback f g) = inst.C (D × (F × G)) :=
    inst.congr ((Pullback.equivSigmaFiber f g).trans
      ((Equiv.sigmaCongrRight (fun d => Equiv.prodCongr (ef d) (eg d))).trans
        (Equiv.sigmaEquivProd D (F × G))))
  rw [hA, hB, hP]
  exact AdditiveComplexityOn.algebraic_gravity
    (inst := instAdditiveComplexityOnType M) D F G

end Gravity

/-! ## The arrow of time — moved

Phase 10's abstract transition-cost class and its Landauer 2/1
instance are deleted (Completion Path
C9). The ratchet is now *derived*, not axiomatized:
`Meno/InfoRatchet.lean` counts the reverse descriptions
(`log_card_sections` — the coding theorem) and proves the
cardinality-free form (`section_not_surjective_of_not_injective`);
`Meno/Simplicial.lean`'s `simplicial_ratchet` consumes the latter. -/

end SGD
