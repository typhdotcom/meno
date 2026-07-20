import Meno.InfoRatchet
import Mathlib.Data.ZMod.Basic

/-! # Self-Reference: the Diagonal Corner

The diagonal kernel, exactly this and no
more: **no description system enumerates its own binary predicates,
and the shortfall is priced.** Scope stated plainly: this is the
Lawvere/Cantor core in Meno's vocabulary — the fixed-point-free
diagonal on `ZMod 2`-valued predicates — not a formalization of the
incompleteness theorems.

* **The impossibility** (`no_self_enumeration`): for every type `A`,
  in every universe, with no finiteness hypothesis, there is no
  surjection `A → (A → ZMod 2)`. The direct diagonal: a preimage of
  `fun b => e b b + 1` yields `0 = 1` in `ZMod 2`.
* **The exact law** (`descriptionCost_split`): on a nonempty finite
  carrier the forward description cost of a binary predicate splits
  as the enumerable budget plus its own correction term —
  `descriptionCost f = log |A| + log (|A → ZMod 2| / |A|)` — the
  correction is the log-ratio of the predicate space to the carrier.
* **The strictness** (`log_card_lt_descriptionCost`): the correction
  term is strictly positive at **every**
  nonempty finite carrier — `log |A| < descriptionCost f`. The route
  is the diagonal itself, not an independent numeric bound: were the
  predicate space no larger than the carrier, a finite retraction
  would produce the forbidden surjection (`card_lt_card_predicates`,
  private).
* **The boundary** (`log_card_eq_descriptionCost_iff`): equality
  holds **iff** the carrier is empty — the price collapses to the
  budget exactly where there is nothing to describe. -/

namespace Meno

universe u

/-- **The impossibility**: no type surjects onto its own
`ZMod 2`-valued predicates — every type, every universe, no
finiteness hypothesis. The direct diagonal: a preimage of
`fun b => e b b + 1` evaluated at itself forces `0 = 1` in
`ZMod 2`. -/
theorem no_self_enumeration (A : Type u) :
    ¬ ∃ e : A → (A → ZMod 2), Function.Surjective e := by
  rintro ⟨e, he⟩
  obtain ⟨a, ha⟩ := he (fun b => e b b + 1)
  have h : e a a + 0 = e a a + 1 := by
    rw [add_zero]; exact congrFun ha a
  exact absurd (add_left_cancel h) (by decide)

/-- The counting shadow of the diagonal: on a finite carrier the
predicate space is strictly larger. Proved through
`no_self_enumeration` — were it no larger, an embedding of the
predicate space into the carrier would retract to the forbidden
surjection — so the priced corollaries below inherit the diagonal's
provenance rather than an independent numeric bound. -/
private theorem card_lt_card_predicates (A : Type u) [Finite A] :
    Nat.card A < Nat.card (A → ZMod 2) := by
  classical
  cases nonempty_fintype A
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  by_contra hle
  push_neg at hle
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hle
  obtain ⟨r, hr⟩ := emb.injective.hasLeftInverse
  exact no_self_enumeration A ⟨r, hr.surjective⟩

variable {A : Type} [Fintype A]

/-- **The exact law**: on a nonempty finite carrier the forward
description cost of a binary predicate is the enumerable budget plus
its own correction term — the log-ratio of the predicate space to
the carrier. -/
theorem descriptionCost_split [Nonempty A] (f : A → ZMod 2) :
    descriptionCost f
      = Real.log (Nat.card A)
        + Real.log ((Nat.card (A → ZMod 2) : ℝ) / (Nat.card A : ℝ)) := by
  have hA : ((Nat.card A : ℝ)) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hF : ((Nat.card (A → ZMod 2) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := A → ZMod 2)).ne'
  rw [descriptionCost_eq, Real.log_div hF hA]
  ring

/-- **The strictness — the cost corollary**: the law's
correction term is strictly positive at every nonempty finite
carrier, so the enumerable budget never pays for the predicate
space. Derived through the counting shadow of the diagonal
(`card_lt_card_predicates`), i.e. from `no_self_enumeration`
itself. -/
theorem log_card_lt_descriptionCost [Nonempty A] (f : A → ZMod 2) :
    Real.log (Nat.card A) < descriptionCost f := by
  rw [descriptionCost_split f, lt_add_iff_pos_right]
  refine Real.log_pos ?_
  rw [one_lt_div (by exact_mod_cast Nat.card_pos)]
  exact_mod_cast card_lt_card_predicates A

/-- **The boundary**: the budget equals the price **iff** the
carrier is empty — the shortfall vanishes exactly where there is
nothing to describe. -/
theorem log_card_eq_descriptionCost_iff (f : A → ZMod 2) :
    Real.log (Nat.card A) = descriptionCost f ↔ IsEmpty A := by
  constructor
  · intro h
    by_contra hne
    haveI : Nonempty A := not_isEmpty_iff.mp hne
    exact absurd h (ne_of_lt (log_card_lt_descriptionCost f))
  · intro h
    simp [descriptionCost, Nat.card_eq_fintype_card, Fintype.card_eq_zero]

end Meno
