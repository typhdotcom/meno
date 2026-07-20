import Meno.Binding
import Meno.BasisIndependence
import Meno.ResolutionCount

/-! # The Completion Object: the Dichotomy (G7)

One biconditional at the top of the tree. The first program's
statement-coverage bundle and its nine law packages — an
acceptance-signature checklist, one field per claim — lived in this
file; the Obstruction Program (PLAN, G7) deletes them (recorded in
`scripts/deleted.txt`) and installs their successor: one statement
whose forward direction requires every face's strictness.

`meno_dichotomy`: a finite multigraph has cycles **iff** the five
strict phenomena all occur —

* **matter** (`exists_matter`): a nonzero `H¹` class exists;
* **spectrum** (`one_lt_classPartFn`, `Meno/Binding.lean`): the
  class partition function strictly exceeds the vacuum's unit
  weight;
* **fluctuation** (`classSectorAction_gibbsVariance_energy_pos`):
  the harmonic energy genuinely fluctuates under the intrinsic
  Gibbs law;
* **deficit** (`residueDefect_pos`): at every resolution `1 < q`
  the Gibbs residue law sits strictly below maximal ignorance;
* **arrow** (`sectionCost_h1TowerMap`, the ratchet along the
  tower): reversing any genuine refinement step `q → c·q`, `1 < c`,
  has strictly positive section cost.

The reverse direction consumes only the matter conjunct: a matter
sector already forces cycles (`MatterSector.b1_pos`, the converse
of `exists_matter`).

**The universe of the model is interesting exactly when it is
globally unsatisfiable.** A hollow face cannot deliver its strict
conjunct, and deleting any face's strictness theorem breaks this
file. -/

namespace Meno

universe u v

/-- **THE DICHOTOMY** (G7, the completion object): a finite
multigraph has cycles **iff** matter exists, the spectrum strictly
exceeds the vacuum, the energy fluctuates, every resolution carries
a strict information deficit, and every genuine refinement of the
tower is strictly priced. Forward: the faces' strictness theorems,
consumed by name. Reverse: a matter sector forces cycles
(`MatterSector.b1_pos`). -/
theorem meno_dichotomy (G : IncidenceGraph.{u, v}) :
    0 < G.b1 ↔
      Nonempty (MatterSector G)
      ∧ 1 < G.classPartFn
      ∧ 0 < (G.classSectorAction).gibbsVariance G.harmonicEnergy
      ∧ (∀ (q : ℕ) [NeZero q], 1 < q → 0 < G.residueDefect q)
      ∧ (∀ (q c : ℕ) [NeZero q] [NeZero c], 1 < c →
          0 < sectionCost (⇑(G.h1TowerMap q (c * q) (dvd_mul_left q c)))) := by
  constructor
  · intro hb
    refine ⟨exists_matter G hb, G.one_lt_classPartFn hb,
      G.classSectorAction_gibbsVariance_energy_pos hb, ?_, ?_⟩
    · intro q _ hq
      exact G.residueDefect_pos q hb hq
    · intro q c _ _ hc
      have hcard : (0 : ℝ)
          < Nat.card (IncidenceGraph.H1Reduction G q) := by
        exact_mod_cast Nat.card_pos
      have hlaw := G.sectionCost_h1TowerMap q (c * q) c
        (dvd_mul_left q c) rfl
      rw [div_eq_iff hcard.ne'] at hlaw
      rw [hlaw]
      exact mul_pos (mul_pos (by exact_mod_cast hb)
        (Real.log_pos (by exact_mod_cast hc))) hcard
  · rintro ⟨⟨m⟩, -, -, -, -⟩
    exact m.b1_pos

end Meno
