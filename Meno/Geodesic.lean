import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Geodesic: Lawvere-subadditive length on a category

A `Geodesic` instance equips a category with a non-negative real-valued
length on morphisms that is **subadditive** under composition and zero on
identities. This is the categorical version of a Lawvere metric: a
combinatorial / topological scale on morphisms without analytic content.

**Critical separation from analytic energy.** `Geodesic.length` is *not*
the source of a `SectorAction` energy. For the cycle graph `C_n`, the
canonical winding-1 cycle has `length = n` (combinatorial walk length)
while the harmonic energy of the same sector is `1/n`. The two are
independent invariants connected by the geodesic/harmonic duality
`n · (1/n) = 1`. -/

namespace Meno

open CategoryTheory

universe u v

/-- A category equipped with a Lawvere-subadditive non-negative length. -/
class Geodesic (C : Type u) [Category.{v} C] where
  /-- Length of a morphism. -/
  length : ∀ {X Y : C}, (X ⟶ Y) → ℝ
  /-- Length is non-negative. -/
  length_nonneg : ∀ {X Y : C} (f : X ⟶ Y), 0 ≤ length f
  /-- Length of identity is zero. -/
  length_id : ∀ (X : C), length (𝟙 X) = 0
  /-- Length is subadditive under composition. -/
  length_comp_le : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    length (f ≫ g) ≤ length f + length g

namespace Geodesic


end Geodesic

end Meno
