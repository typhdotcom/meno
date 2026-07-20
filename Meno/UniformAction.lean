import Meno.SectorAction
import Meno.Basic

/-! # The Uniform Sector Action — Counting as Zero-Energy Pricing

A finite nonempty type is a sector lattice
with **zero energy everywhere** — every state equally costly to
name — so its partition function *is* its cardinality and its
complexity *is* `log |A|` (`uniformAction_partFn`,
`uniformAction_complexity`).

Counting is not a parallel theory: the log-cardinality
gravity identity is the **zero-energy corollary** of the one gravity
theorem — `counting_gravity` (`Meno/InfoRatchet.lean`) instantiates
`SectorAction.complexity_gravity` at `uniformAction D` and evaluates
the four complexities through `uniformAction_complexity`. This file
supplies the zero-energy actions and the pullback finiteness that
corollary consumes. -/

namespace Meno

open scoped BigOperators

universe u

/-- **The uniform sector action** of a finite nonempty type: every
element a sector, every sector free. The Boltzmann sum then simply
counts. -/
noncomputable def uniformAction (A : Type u) [Fintype A] [Nonempty A] :
    SectorAction where
  Λ := A
  E := fun _ => 0
  E_zero := ⟨Classical.arbitrary A, rfl⟩
  E_nonneg := fun _ => le_refl 0
  summable := (hasSum_fintype _).summable

/-- The uniform partition function is the cardinality. -/
theorem uniformAction_partFn (A : Type u) [Fintype A] [Nonempty A] :
    (uniformAction A).partFn = Fintype.card A := by
  show ∑' _ : A, Real.exp (-(0 : ℝ)) = (Fintype.card A : ℝ)
  rw [tsum_fintype]
  simp

/-- The uniform complexity is the log-cardinality — counting,
realized as a zero-energy sector action. -/
theorem uniformAction_complexity (A : Type u) [Fintype A] [Nonempty A] :
    (uniformAction A).complexity = Real.log (Fintype.card A) := by
  show Real.log (uniformAction A).partFn = _
  rw [uniformAction_partFn]

/-- The pullback of finite types is finite (seen through the
definition, which instance search cannot unfold on its own). -/
instance pullbackFintype {A B D : Type u} [Fintype A] [Fintype B]
    [DecidableEq D] {f : A → D} {g : B → D} :
    Fintype (SGD.Pullback f g) :=
  inferInstanceAs (Fintype {p : A × B // f p.1 = g p.2})

end Meno
