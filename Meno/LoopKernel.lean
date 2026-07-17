import Meno.SectorAction
import Mathlib.CategoryTheory.Endomorphism

/-! # Loop Kernel: categorical presentation of a sector action

A `LoopKernelObj` is a basepointed category equipped with an energy on
`End base` whose Boltzmann weight is summable, plus the two ground conditions
`energy_id = 0` and `energy_nonneg`. It is the categorical interface to
`SectorAction`: every loop kernel projects to a sector action by forgetting
the categorical structure and keeping only `(End base, energy)`.

This is the upstream primitive that `GroupoidObj` (a groupoid plus energy)
specialises. The bridge `GroupoidObj.toLoopKernelObj` takes the two ground
conditions as explicit arguments — `GroupoidObj` does not carry them as
fields, and each construction site discharges them where it builds the
bridge (`Meno/Hodge.lean`, `Meno/Duality.lean`). -/

namespace Meno

open CategoryTheory

universe u v w

/-- A loop kernel: a (small) category, a basepoint, and a sector action on
the endomorphism monoid of the basepoint. -/
structure LoopKernelObj where
  C : Type u
  [cat : Category.{v} C]
  base : C
  energy : End base → ℝ
  energy_id : energy (𝟙 base) = 0
  energy_nonneg : ∀ g, 0 ≤ energy g
  summable : Summable (fun g => Real.exp (-energy g))

attribute [instance] LoopKernelObj.cat

namespace LoopKernelObj

variable (L : LoopKernelObj.{u, v})

/-- Forgetful projection to a `SectorAction`: discard the categorical
structure, keep only the analytic content `(End base, energy)`. -/
noncomputable def toSectorAction : SectorAction.{v} where
  Λ := End L.base
  E := L.energy
  E_zero := ⟨𝟙 L.base, L.energy_id⟩
  E_nonneg := L.energy_nonneg
  summable := L.summable

/-- Partition function of a loop kernel. -/
noncomputable def partFn : ℝ := L.toSectorAction.partFn

/-- Complexity of a loop kernel. -/
noncomputable def complexity : ℝ := L.toSectorAction.complexity

/-- Gibbs density on endomorphisms. -/
noncomputable def gibbsMass (g : End L.base) : ℝ := L.toSectorAction.gibbsMass g

/-- Gibbs expectation of an observable. -/
noncomputable def gibbsExpect (f : End L.base → ℝ) : ℝ :=
  L.toSectorAction.gibbsExpect f

/-- Gibbs variance of an observable. -/
noncomputable def gibbsVariance (f : End L.base → ℝ) : ℝ :=
  L.toSectorAction.gibbsVariance f

/-! ## Forwarded analytic lemmas (all `rfl` or one-line forwarding). -/

theorem partFn_pos : 0 < L.partFn := L.toSectorAction.partFn_pos

theorem partFn_ge_one : 1 ≤ L.partFn := L.toSectorAction.partFn_ge_one

theorem complexity_nonneg : 0 ≤ L.complexity := L.toSectorAction.complexity_nonneg

theorem gibbsMass_nonneg (g : End L.base) : 0 ≤ L.gibbsMass g :=
  L.toSectorAction.gibbsMass_nonneg g

theorem summable_gibbsMass : Summable L.gibbsMass :=
  L.toSectorAction.summable_gibbsMass

theorem tsum_gibbsMass_eq_one : ∑' g, L.gibbsMass g = 1 :=
  L.toSectorAction.tsum_gibbsMass_eq_one

theorem gibbsExpect_one : L.gibbsExpect (fun _ => 1) = 1 :=
  L.toSectorAction.gibbsExpect_one

theorem gibbsVariance_nonneg (f : End L.base → ℝ)
    (hsq : Summable (fun g => f g ^ 2 * L.gibbsMass g))
    (hf : Summable (fun g => f g * L.gibbsMass g)) :
    0 ≤ L.gibbsVariance f :=
  L.toSectorAction.gibbsVariance_nonneg f hsq hf

end LoopKernelObj

end Meno
