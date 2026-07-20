import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Unique
import Mathlib.Data.Set.Image
import Mathlib.Tactic

/-! # SGD — The Pullback Substrate

The shared-base structure the priced gravity calculus consumes:
fibers, fiber products, the pullback with its base map, and the
equivalences that decompose it — the sigma-fiber factorization and
the base/marginal fiber identifications. The consumers are the
priced coupling machinery (`Meno/InfoRatchet.lean`) and the carrier
layers (`Meno/ResolutionCount.lean`, `Meno/ThetaHarmonic.lean`).

The former abstract complexity hierarchy — the measure classes,
their log-cardinality realization, the type-level gravity and
refactoring bounds, and the additivity engine — is **deleted**
(review #25; the name-by-name record is `scripts/deleted.txt`):
consumer analysis found it certificate-only — a
parallel construction, not a load-bearing layer. The one gravity
theorem of the program is `SectorAction.complexity_gravity`
(`Meno/InfoRatchet.lean`); counting gravity is its zero-energy
corollary (`counting_gravity`, same file). -/

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

/-! ## The arrow of time — moved

Phase 10's abstract transition-cost class and its Landauer 2/1
instance are deleted (Completion Path
C9). The ratchet is now *derived*, not axiomatized:
`Meno/InfoRatchet.lean` counts the reverse descriptions
(`log_card_sections` — the coding theorem) and proves the
cardinality-free form (`section_not_surjective_of_not_injective`);
`Meno/Simplicial.lean`'s `simplicial_ratchet` consumes the latter. -/

end SGD
