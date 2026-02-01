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

/-- When D is a subsingleton, pullback ≃ product. -/
def Pullback.equivProdOfSubsingleton {A B D : Type u} [Subsingleton D]
    (f : A → D) (g : B → D) : Pullback f g ≃ A × B where
  toFun p := p.val
  invFun p := ⟨p, Subsingleton.elim _ _⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

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

/-- **The Refactoring Bound**: pullback ≤ base + sup fibers.
    C(A ×_D B) ≤ C(D) + sup_d C(Fiber f d) + sup_d C(Fiber g d) -/
theorem refactoring_bound
    (hf : BddAbove (Set.range fun d => inst.C (Fiber f d)))
    (hg : BddAbove (Set.range fun d => inst.C (Fiber g d)))
    (hne : Nonempty D) :
    inst.C (Pullback f g) ≤
      inst.C D + (⨆ d, inst.C (Fiber f d)) + (⨆ d, inst.C (Fiber g d)) := by
  rw [pullback_complexity_eq]
  have key : ⨆ d, inst.C (FiberProd f g d) ≤
             (⨆ d, inst.C (Fiber f d)) + (⨆ d, inst.C (Fiber g d)) := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨d, rfl⟩
    calc inst.C (FiberProd f g d)
        ≤ inst.C (Fiber f d) + inst.C (Fiber g d) := fiberProd_le f g d
      _ ≤ (⨆ d, inst.C (Fiber f d)) + (⨆ d, inst.C (Fiber g d)) :=
          add_le_add (le_csSup hf (Set.mem_range_self d))
                     (le_csSup hg (Set.mem_range_self d))
  calc inst.C (Σ d, FiberProd f g d)
      ≤ inst.C D + ⨆ d, inst.C (FiberProd f g d) := inst.sigma_le D _
    _ ≤ inst.C D + ((⨆ d, inst.C (Fiber f d)) + (⨆ d, inst.C (Fiber g d))) :=
        add_le_add_right key _
    _ = inst.C D + (⨆ d, inst.C (Fiber f d)) + (⨆ d, inst.C (Fiber g d)) := by
        rw [add_assoc]

end RefactoringBound

/-! ## Gravity (Uniform Fiber Case) -/

section Gravity

variable {M : Type*} [AddCommMonoid M] [PartialOrder M]
variable [SupSet M] [inst : AdditiveComplexity M]

/-- **Gravity**: for any maps f : A → D, g : B → D with uniform fibers
    (all fibers of f isomorphic to F, all fibers of g isomorphic to G),
    the pullback saves exactly C(D).

    Proof: A ≃ D × F and B ≃ D × G via sigma-fiber decomposition,
    Pullback f g ≃ D × F × G via the same on fiber products.
    Then C(D×F×G) + C(D) = C(D×F) + C(D×G) by additivity. -/
theorem gravity {A B D F G : Type u} (f : A → D) (g : B → D)
    (ef : ∀ d, Fiber f d ≃ F) (eg : ∀ d, Fiber g d ≃ G) :
    inst.C (Pullback f g) + inst.C D = inst.C A + inst.C B := by
  have hA : inst.C A = inst.C D + inst.C F :=
    (inst.congr ((Equiv.sigmaFiberEquiv f).symm.trans
        ((Equiv.sigmaCongrRight ef).trans (Equiv.sigmaEquivProd D F)))).trans (inst.prod_eq D F)
  have hB : inst.C B = inst.C D + inst.C G :=
    (inst.congr ((Equiv.sigmaFiberEquiv g).symm.trans
        ((Equiv.sigmaCongrRight eg).trans (Equiv.sigmaEquivProd D G)))).trans (inst.prod_eq D G)
  have hP : inst.C (Pullback f g) = inst.C D + (inst.C F + inst.C G) := by
    rw [inst.congr ((Pullback.equivSigmaFiber f g).trans
        ((Equiv.sigmaCongrRight (fun d => Equiv.prodCongr (ef d) (eg d))).trans
         (Equiv.sigmaEquivProd D (F × G)))),
        inst.prod_eq D (F × G), inst.prod_eq F G]
  rw [hA, hB, hP]; abel

/-- Fiber of first projection π₁ : D × F → D over d is isomorphic to F. -/
def fstFiberEquiv (D F : Type u) (d : D) : Fiber (fun p : D × F => p.1) d ≃ F where
  toFun x := x.val.2
  invFun f := ⟨(d, f), rfl⟩
  left_inv x := by ext; exact x.property.symm; rfl
  right_inv _ := rfl

/-- Corollary: the original product-projection case. -/
theorem gravity_uniform (D F G : Type u) :
    inst.C (Pullback (fun p : D × F => p.1) (fun p : D × G => p.1)) + inst.C D =
    inst.C (D × F) + inst.C (D × G) :=
  gravity _ _ (fstFiberEquiv D F) (fstFiberEquiv D G)

end Gravity

/-! ## Structured Complexity

The type-level hierarchy above measures bare types. For structured objects
(simplicial complexes, graphs), complexity depends on structure, not cardinality.
StructuredComplexity captures the same algebraic law — merge/overlap gravity —
for any object type with merge and overlap operations. -/

/-- Complexity on structured objects with merge and overlap.
    The merge_overlap law is Mayer-Vietoris: total complexity is preserved. -/
class StructuredComplexity (Obj : Type*) (M : Type*) [AddCommMonoid M] where
  K : Obj → M
  merge : Obj → Obj → Obj
  overlap : Obj → Obj → Obj
  merge_overlap : ∀ (A B : Obj), K (merge A B) + K (overlap A B) = K A + K B

/-! ## Contractibility -/

def Contractible (A : Type u) : Prop := Nonempty (A ≃ PUnit.{u+1})

/-! ## The Directed Loop: Time

The thermodynamic laws of computation. Any concrete model claiming to be physical
must instantiate this class, proving that non-injective maps are irreversible
and injective maps are free. -/

class TransitionComplexity where
  /-- Transition cost for a map. Concrete meaning is model-dependent. -/
  transitionCost : {A B : Type u} → (A → B) → ℕ
  /-- Every transition costs at least 1. -/
  transitionCost_pos : ∀ {A B : Type u} (f : A → B), transitionCost f > 0
  /-- **The Entropic Ratchet.** Non-injective maps collapse fibers; recovering
      which preimage was used costs strictly more than the forward map. -/
  ratchet : ∀ {A B : Type u} (f : A → B) (r : B → A),
    (∀ b, f (r b) = b) → ¬Function.Injective f →
    transitionCost r > transitionCost f
  /-- Injective maps are losslessly reversible: forward and backward cost the same.
      Injective computation is timeless. -/
  injective_reversible : ∀ {A B : Type u} (f : A → B) (r : B → A),
    (∀ b, f (r b) = b) → Function.Injective f →
    transitionCost r = transitionCost f

/-! ## Landauer Instance: The Minimal Ratchet -/

open Classical in
/-- The Landauer cost model: injective maps cost 2, non-injective cost 1.
    Any right-inverse of a non-injective map is injective (f ∘ r = id → r injective),
    so the ratchet and reversibility axioms are satisfied. -/
noncomputable instance : TransitionComplexity where
  transitionCost f := if Function.Injective f then 2 else 1
  transitionCost_pos f := by split <;> omega
  ratchet f r hfr hni := by
    have hr_inj : Function.Injective r := fun _ _ h => by
      have := congr_arg f h; rwa [hfr, hfr] at this
    show (if Function.Injective r then 2 else 1) > (if Function.Injective f then 2 else 1)
    rw [if_pos hr_inj, if_neg hni]; norm_num
  injective_reversible f r hfr hfi := by
    have hr_inj : Function.Injective r := fun _ _ h => by
      have := congr_arg f h; rwa [hfr, hfr] at this
    show (if Function.Injective r then 2 else 1) = (if Function.Injective f then 2 else 1)
    rw [if_pos hr_inj, if_pos hfi]

end SGD
