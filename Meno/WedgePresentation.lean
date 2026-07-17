import Meno.GraphInstances
import Meno.Matter

/-! # The Concrete Bases' Acceptance Witnesses (C5)

The concrete graphs' lattice bases live with their topology in
`Meno/GraphInstances.lean` (review #5: `cycleLatticeBasis`,
`wedgeLatticeBasis`, `thetaLatticeBasis` — genuine
`Module.Basis _ ℤ G.cycleLattice` objects, everything derived). What
remains here are the C5 acceptance witnesses that consume the priced
stack:

* the genuine wedge has **matter** (`wedgeGraph_exists_matter`) —
  nontrivial topology forces it;
* each hand-built basis is a **unimodular recombination** of its
  graph's fundamental basis — instances of C3's
  `exists_unimodular_relating`. (The theta instance lives with its
  pricing in `Meno/ThetaHarmonic.lean`.)

The old hand-built presentation structures, the routed prefix-sum
potentials, and the per-instance integral fields are gone: integral
potentials, period surjectivity, spanning, and Gram positivity are
theorems of every lattice basis (`Meno/GraphHomology.lean`). -/

namespace Meno

open scoped BigOperators
open Matrix

/-- The genuine wedge has matter: nontrivial topology (`b₁ = 2`)
forces it. -/
theorem wedgeGraph_exists_matter (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    Nonempty (MatterSector (wedgeGraph n₁ n₂ h₁ h₂)) :=
  exists_matter _ (by rw [wedgeGraph_b1 n₁ n₂ h₁ h₂]; norm_num)

/-! ## C5's acceptance witnesses -/

/-- The cycle graph's hand-built basis is a unimodular recombination
of the fundamental one (C3's `exists_unimodular_relating`). -/
theorem cycleLatticeBasis_unimodular_related (n : ℕ) (hn : 0 < n) :
    ∃ U : Matrix (Fin (cycleGraph n hn).b1) (Fin (cycleGraph n hn).b1) ℤ,
      IsUnit U.det ∧
      ∀ j, (cycleGraph n hn).cyclesZ
          ((cycleLatticeBasis n hn).reindex
            (finCongr ((cycleGraph n hn).card_eq_b1 (cycleLatticeBasis n hn)))) j
        = fun e => ∑ i, U i j
            * (cycleGraph n hn).cyclesZ (cycleGraph n hn).cycleBasis i e :=
  (cycleGraph n hn).exists_unimodular_relating (cycleGraph n hn).cycleBasis
    ((cycleLatticeBasis n hn).reindex
      (finCongr ((cycleGraph n hn).card_eq_b1 (cycleLatticeBasis n hn))))

/-- The wedge's hand-built basis is a unimodular recombination of the
fundamental one (C3's `exists_unimodular_relating`). -/
theorem wedgeLatticeBasis_unimodular_related
    (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    ∃ U : Matrix (Fin (wedgeGraph n₁ n₂ h₁ h₂).b1)
        (Fin (wedgeGraph n₁ n₂ h₁ h₂).b1) ℤ,
      IsUnit U.det ∧
      ∀ j, (wedgeGraph n₁ n₂ h₁ h₂).cyclesZ
          ((wedgeLatticeBasis n₁ n₂ h₁ h₂).reindex
            (finCongr ((wedgeGraph n₁ n₂ h₁ h₂).card_eq_b1
              (wedgeLatticeBasis n₁ n₂ h₁ h₂)))) j
        = fun e => ∑ i, U i j
            * (wedgeGraph n₁ n₂ h₁ h₂).cyclesZ
                (wedgeGraph n₁ n₂ h₁ h₂).cycleBasis i e :=
  (wedgeGraph n₁ n₂ h₁ h₂).exists_unimodular_relating
    (wedgeGraph n₁ n₂ h₁ h₂).cycleBasis
    ((wedgeLatticeBasis n₁ n₂ h₁ h₂).reindex
      (finCongr ((wedgeGraph n₁ n₂ h₁ h₂).card_eq_b1
        (wedgeLatticeBasis n₁ n₂ h₁ h₂))))

end Meno
