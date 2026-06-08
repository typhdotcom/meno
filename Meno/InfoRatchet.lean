import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Card

/-! # Fiber Information Cost and the Entropic Ratchet

For a finite function `f : A → B`, the **fiber information cost** is

    fiberInfoCost f = ∑_{b : B} log |f ⁻¹ {b}|

— the description length needed to specify *which preimage* in each fiber
a point comes from. For injective `f` every fiber has size 1, so
`fiberInfoCost = 0`; for non-injective `f` some fiber has size ≥ 2, so
`fiberInfoCost > 0`.

The **ratchet** is then the inequality `sectionCost ≥ descriptionCost +
fiberInfoCost`: specifying any section `s : B → A` of `f` costs at least
the description of `f` plus the fiber-choice information.

This file isolates the fiber-information layer. It is independent of the
specific cost convention used by Basic.lean's `TransitionComplexity`
class. The reconciliation — showing the Landauer 2/1 convention is one
admissible cost model — is left to Phase 10. -/

namespace Meno

open scoped BigOperators

universe u

variable {A B : Type u}

/-- Fiber information cost of a function: `∑ b, log |f ⁻¹ {b}|`. Empty
fibers (`b ∉ image f`) contribute `log 0 = 0` by Mathlib convention. -/
noncomputable def fiberInfoCost [Fintype B] [DecidableEq B] (f : A → B) : ℝ :=
  ∑ b : B, Real.log (Nat.card (f ⁻¹' {b}) : ℝ)

theorem fiberInfoCost_nonneg [Fintype B] [DecidableEq B] (f : A → B) :
    0 ≤ fiberInfoCost f := by
  unfold fiberInfoCost
  refine Finset.sum_nonneg (fun b _ => ?_)
  rcases (Nat.card (f ⁻¹' {b})).eq_zero_or_pos with hzero | hpos
  · simp [hzero]
  · exact Real.log_nonneg (by exact_mod_cast hpos)

/-- Injective functions have zero fiber-info cost: every fiber is a
singleton (or empty), and `log 1 = log 0 = 0`. -/
theorem fiberInfoCost_of_injective [Fintype B] [DecidableEq B]
    {f : A → B} (hf : Function.Injective f) :
    fiberInfoCost f = 0 := by
  unfold fiberInfoCost
  refine Finset.sum_eq_zero (fun b _ => ?_)
  have hsub : Subsingleton (f ⁻¹' {b}) := by
    refine ⟨fun ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ => ?_⟩
    have h₁ : f a₁ = b := ha₁
    have h₂ : f a₂ = b := ha₂
    exact Subtype.ext (hf (h₁.trans h₂.symm))
  by_cases hne : Nonempty (f ⁻¹' {b})
  · have h1 : Nat.card (f ⁻¹' {b}) = 1 := Nat.card_unique
    rw [h1]; simp
  · rw [not_nonempty_iff] at hne
    have h0 : Nat.card (f ⁻¹' {b}) = 0 := Nat.card_eq_zero.mpr (Or.inl hne)
    rw [h0]; simp

/-- Description cost of a function: `|A| · log |B|`. The number of bits
to specify which of `|B|^|A|` total functions `f` is. -/
noncomputable def descriptionCost [Fintype A] [Fintype B] (_f : A → B) : ℝ :=
  (Fintype.card A : ℝ) * Real.log (Fintype.card B : ℝ)

/-- Section cost: the description cost of `f` plus the fiber-information
overhead. A section `s : B → A` of `f` must specify, for each `b`, which
preimage to use — that's `fiberInfoCost f` bits of additional information. -/
noncomputable def sectionCost [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) (_s : B → A) (_hs : ∀ b, f (_s b) = b) : ℝ :=
  descriptionCost f + fiberInfoCost f

/-- The **ratchet identity**: section cost minus description cost equals
the fiber information cost. The asymmetry between forward and reverse
description is exactly the fiber-choice information. -/
theorem sectionCost_sub_descriptionCost [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) (s : B → A) (hs : ∀ b, f (s b) = b) :
    sectionCost f s hs - descriptionCost f = fiberInfoCost f := by
  unfold sectionCost; ring

/-- For an **injective** `f`, section cost equals description cost: no
fiber information needed. -/
theorem sectionCost_eq_of_injective [Fintype A] [Fintype B] [DecidableEq B]
    {f : A → B} (s : B → A) (hs : ∀ b, f (s b) = b) (hf : Function.Injective f) :
    sectionCost f s hs = descriptionCost f := by
  unfold sectionCost
  rw [fiberInfoCost_of_injective hf]; ring

end Meno
