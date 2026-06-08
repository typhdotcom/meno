import Meno.LoopKernel

/-! # Hom Kernel: per-cell sector actions on a category

A `HomKernelCat` equips a category with an energy on every Hom-cell.
Each `(X, Y)` hom-set carries its own Boltzmann weight; together with
the identity/non-negativity/summability conditions, this is the global
data needed for Leinster magnitude `1ᵀ Z⁻¹ 1` on a finite category.

`LoopKernelObj` is recovered as the single-base-slice: `K.atBase X`
projects the X-loop sector action out of the global hom kernel. Most of
Meno's existing analytic content (`Duality.lean`, `Hodge.lean`, `Zeta.lean`)
needs only the base slice; the hom-kernel layer is here to support the
global magnitude readout and forward compatibility with multi-base
invariants.

A `HomKernelCat` is **not** the foundation of the project — `SectorAction`
is. `HomKernelCat` generalises `LoopKernelObj` upward by tracking all
hom-cells; `LoopKernelObj` was already enough for single-basepoint
analytic content. -/

namespace Meno

open CategoryTheory

universe u v

/-- A category with a sector action on every hom-cell. -/
structure HomKernelCat where
  C : Type u
  [cat : Category.{v} C]
  /-- Energy on each morphism. -/
  energy : ∀ {X Y : C}, (X ⟶ Y) → ℝ
  /-- Identity has zero energy. -/
  energy_id : ∀ X : C, energy (𝟙 X) = 0
  /-- All energies are non-negative. -/
  energy_nonneg : ∀ {X Y : C} (f : X ⟶ Y), 0 ≤ energy f
  /-- The hom-cell Boltzmann weight is summable. -/
  summable : ∀ X Y : C, Summable (fun f : X ⟶ Y => Real.exp (-energy f))

attribute [instance] HomKernelCat.cat

namespace HomKernelCat

variable (K : HomKernelCat.{u, v})

/-- Per-cell partition function: `Z(X, Y) = ∑' f : X ⟶ Y, exp(-E f)`. -/
noncomputable def homPartFn (X Y : K.C) : ℝ :=
  ∑' f : X ⟶ Y, Real.exp (-K.energy f)

/-- Loop kernel at base `X`: the X-endomorphism slice. -/
noncomputable def atBase (X : K.C) : LoopKernelObj.{u, v} where
  C := K.C
  base := X
  energy := K.energy
  energy_id := K.energy_id X
  energy_nonneg := K.energy_nonneg
  summable := K.summable X X

theorem atBase_partFn (X : K.C) : (K.atBase X).partFn = K.homPartFn X X := rfl

theorem homPartFn_pos (X : K.C) : 0 < K.homPartFn X X := by
  rw [← K.atBase_partFn]; exact (K.atBase X).partFn_pos

theorem homPartFn_ge_one (X : K.C) : 1 ≤ K.homPartFn X X := by
  rw [← K.atBase_partFn]; exact (K.atBase X).partFn_ge_one

end HomKernelCat

end Meno
