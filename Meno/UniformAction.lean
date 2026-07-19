import Meno.SectorAction
import Meno.Basic
import Meno.Instances

/-! # The Uniform Sector Action and the Two Gravity Instances (C9)

The valid replacement for the falsified endofunction-kernel design
(Part II, Phase 17 record: `E(id) = log|A|` contradicted `energy_id`;
endofunction sums broke summability). The correct realization is
simpler: a finite nonempty type is a sector lattice
with **zero energy everywhere** — every state equally costly to
name — so its partition function *is* its cardinality and its
complexity *is* `log |A|` (`uniformAction_partFn`,
`uniformAction_complexity`). The log-cardinality complexity of
`Basic.lean` was a sector action all along
(`logCard_eq_uniformComplexity`).

**The two instances of the one gravity engine** (review #21):
`SGD.AdditiveComplexityOn.algebraic_gravity` (`Meno/Basic.lean`) is
the program's one gravity theorem, and this file holds both of its
physical instances:

* **counting** — the log-cardinality `AdditiveComplexity ℝ≥0∞`
  instance of `Meno/Instances.lean`, through which `SGD.gravity` is
  derived; `gravity_logCard` and `refactoring_bound_logCard`
  **invoke** the abstract theorems at that instance;
* **pricing** — `instAdditiveComplexityOnSectorAction`, below:
  complexity `log Z` on sector actions, congruent under
  energy-preserving equivalence (`SectorAction.complexity_congr`),
  additive over independent products
  (`SectorAction.complexity_prod`). The priced gravity identity
  `SectorAction.complexity_gravity` (`Meno/InfoRatchet.lean`) is
  `algebraic_gravity` at this instance. -/

namespace Meno

open scoped BigOperators ENNReal

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

/-- The uniform complexity is the log-cardinality — `Basic.lean`'s
complexity measure, realized as a sector action. -/
theorem uniformAction_complexity (A : Type u) [Fintype A] [Nonempty A] :
    (uniformAction A).complexity = Real.log (Fintype.card A) := by
  show Real.log (uniformAction A).partFn = _
  rw [uniformAction_partFn]

/-! ## The pricing instance -/

/-- **THE PRICING INSTANCE** (review #21): sector actions carry the
domain-generic additive complexity — `C = log Z`, the unit the free
one-sector action, equivalence the energy-preserving relabeling,
product the independent product. `algebraic_gravity` at this
instance is the priced gravity identity
(`SectorAction.complexity_gravity`, `Meno/InfoRatchet.lean`). -/
noncomputable instance instAdditiveComplexityOnSectorAction :
    SGD.AdditiveComplexityOn SectorAction.{u} ℝ where
  C := SectorAction.complexity
  unit := uniformAction PUnit
  equiv := SectorAction.EnergyEquiv
  prod := SectorAction.prod
  unit_zero := by rw [uniformAction_complexity]; simp
  congr := SectorAction.complexity_congr
  prod_add := SectorAction.complexity_prod

/-! ## Gravity at the counting instance -/

/-- The pullback of finite types is finite (seen through the
definition, which instance search cannot unfold on its own). -/
instance pullbackFintype {A B D : Type u} [Fintype A] [Fintype B]
    [DecidableEq D] {f : A → D} {g : B → D} :
    Fintype (SGD.Pullback f g) :=
  inferInstanceAs (Fintype {p : A × B // f p.1 = g p.2})

/-- **The bridge to the abstract hierarchy** (review #2): for finite
nonempty types, `SGD.logCard` — the `ℝ≥0∞`-valued complexity of
`Meno/Instances.lean`'s `AdditiveComplexity` instance — *is* the
uniform action's complexity, lifted along `ENNReal.ofReal`. The two
theories compute one number. -/
theorem logCard_eq_uniformComplexity (A : Type u) [Fintype A] [Nonempty A] :
    SGD.logCard A = ENNReal.ofReal (uniformAction A).complexity := by
  have hpos : Nat.card A ≠ 0 := by
    have h := Nat.card_pos (α := A)
    omega
  rw [uniformAction_complexity, SGD.logCard, if_neg hpos,
    Nat.card_eq_fintype_card]

/-- Gravity at the counting instance: `SGD.gravity` — itself
`algebraic_gravity` at `instAdditiveComplexityOnType` (review #21) —
**invoked** at the log-cardinality `AdditiveComplexity ℝ≥0∞`
instance, not reproved. -/
theorem gravity_logCard {A B D F G : Type u} (f : A → D) (g : B → D)
    (ef : ∀ d, SGD.Fiber f d ≃ F) (eg : ∀ d, SGD.Fiber g d ≃ G) :
    SGD.logCard (SGD.Pullback f g) + SGD.logCard D
      = SGD.logCard A + SGD.logCard B :=
  SGD.gravity (M := ℝ≥0∞) f g ef eg

/-- The abstract refactoring bound at the log-cardinality instance
(review #2): `SGD.refactoring_bound`, **invoked**. -/
theorem refactoring_bound_logCard {A B D : Type u} (f : A → D) (g : B → D)
    (hne : Nonempty D) :
    SGD.logCard (SGD.Pullback f g)
      ≤ SGD.logCard D + (⨆ d, SGD.logCard (SGD.Fiber f d))
        + ⨆ d, SGD.logCard (SGD.Fiber g d) :=
  SGD.refactoring_bound (M := ℝ≥0∞) f g
    (OrderTop.bddAbove _) (OrderTop.bddAbove _) hne

end Meno
