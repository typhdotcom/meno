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

The **ratchet** (completion path, C8 — now *derived*): reversing `f`,
i.e. choosing a section `s : B → A`, is not free. The sections of `f`
are counted exactly — there are `∏_b |f⁻¹{b}|` of them
(`card_sections`) — so the information in a reverse description,
`sectionCost f := log (#sections)`, is *proved* to equal `fiberInfoCost f`
(`log_card_sections`), rather than defined as `descriptionCost +
fiberInfoCost`. An injective `f` has at most one section
(`sectionCost = 0`); a non-injective surjection has many
(`sectionCost_pos_of_not_injective`). The forward cost is likewise a
genuine count: `descriptionCost f = log (#{functions A → B})`
(`descriptionCost_eq`).

This file isolates the fiber-information layer. It is independent of the
specific cost convention used by Basic.lean's `TransitionComplexity`
class; the Phase-10 program that was to reconcile them was falsified
(PLAN, Phase 17) and is superseded by the completion path's C9. The
compression-map specialization — `#sections = |G_q|^{q^{b₁}}`, tying the
count to the keystone K1–K3 — lives in `Meno/ResolutionCount.lean`. -/

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

/-- **Strict ratchet**: a non-injective function has strictly positive
fiber information cost. The pair `a₁ ≠ a₂` with `f a₁ = f a₂` forces
`|f ⁻¹ {f a₁}| ≥ 2`, contributing `log 2 > 0`; all other fibers
contribute `≥ 0`. -/
theorem fiberInfoCost_pos_of_not_injective [Fintype A] [Fintype B] [DecidableEq B]
    {f : A → B} (hf : ¬ Function.Injective f) :
    0 < fiberInfoCost f := by
  obtain ⟨a₁, a₂, hfa, hne⟩ := Function.not_injective_iff.mp hf
  have hcard : 2 ≤ Nat.card (f ⁻¹' {f a₁}) := by
    have hsub : ({a₁, a₂} : Set A) ⊆ f ⁻¹' {f a₁} := by
      rintro x (rfl | rfl)
      · rfl
      · exact hfa.symm
    have hpair : ({a₁, a₂} : Set A).ncard = 2 := Set.ncard_pair hne
    have hfin : (f ⁻¹' {f a₁}).Finite := Set.toFinite _
    have h2 : 2 ≤ (f ⁻¹' {f a₁}).ncard := by
      rw [← hpair]; exact Set.ncard_le_ncard hsub hfin
    rwa [← Nat.card_coe_set_eq] at h2
  have hlogpos : 0 < Real.log (Nat.card (f ⁻¹' {f a₁}) : ℝ) := by
    apply Real.log_pos
    have h2 : (2 : ℝ) ≤ (Nat.card (f ⁻¹' {f a₁}) : ℝ) := by exact_mod_cast hcard
    linarith
  unfold fiberInfoCost
  refine Finset.sum_pos' (fun c _ => ?_) ⟨f a₁, Finset.mem_univ _, hlogpos⟩
  rcases (Nat.card (f ⁻¹' {c})).eq_zero_or_pos with hzero | hpos
  · simp [hzero]
  · exact Real.log_nonneg (by exact_mod_cast hpos)

/-! ## Counting sections: the coding theorem (C8)

`sectionCost` is no longer *defined* as `descriptionCost + fiberInfoCost`.
The sections of `f` are counted (`card_sections`), and the log-count is
*proved* equal to `fiberInfoCost` (`log_card_sections`). The
fiber-information cost is thereby derived from a description model — the
reverse descriptions of `f` are exactly its sections — not asserted. -/

/-- Sections of `f` correspond to a choice, at each point of `B`, of a
preimage: `{s : B → A // section of f} ≃ ((b : B) → f ⁻¹' {b})`. -/
def sectionsEquivPiFiber (f : A → B) :
    {s : B → A // ∀ b, f (s b) = b} ≃ ((b : B) → (f ⁻¹' {b} : Set A)) where
  toFun s := fun b => ⟨s.1 b, s.2 b⟩
  invFun g := ⟨fun b => (g b).1, fun b => (g b).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The number of sections of `f`** is the product of the fiber sizes:
each reverse description is a per-point choice of preimage. No
surjectivity needed — an empty fiber contributes a `0` factor and there
are then no sections. -/
theorem card_sections [Fintype B] (f : A → B) :
    Nat.card {s : B → A // ∀ b, f (s b) = b} = ∏ b : B, Nat.card (f ⁻¹' {b}) := by
  rw [Nat.card_congr (sectionsEquivPiFiber f), Nat.card_pi]

/-- **The reverse-description cost**: the log-count of `f`'s sections. -/
noncomputable def sectionCost (f : A → B) : ℝ :=
  Real.log (Nat.card {s : B → A // ∀ b, f (s b) = b})

/-- **The coding theorem** (C8): for a surjection the reverse-description
cost — genuinely counted — equals the fiber information cost. This is
`card_sections` composed with `Real.log_prod`; the Phase-22 note is
discharged, the identity `sectionCost = fiberInfoCost` is a counting
theorem, not a definition. -/
theorem log_card_sections [Fintype A] [Fintype B] [DecidableEq B]
    {f : A → B} (hf : Function.Surjective f) :
    sectionCost f = fiberInfoCost f := by
  have hne : ∀ b : B, ((Nat.card (f ⁻¹' {b}) : ℕ) : ℝ) ≠ 0 := by
    intro b
    obtain ⟨a, ha⟩ := hf b
    haveI : Nonempty ↥(f ⁻¹' {b}) := ⟨⟨a, ha⟩⟩
    exact_mod_cast (Finite.card_pos).ne'
  unfold sectionCost fiberInfoCost
  rw [card_sections f, Nat.cast_prod, Real.log_prod (fun b _ => hne b)]

/-- Reading `log_card_sections` as an equation of costs. -/
theorem sectionCost_eq_fiberInfoCost [Fintype A] [Fintype B] [DecidableEq B]
    {f : A → B} (hf : Function.Surjective f) :
    sectionCost f = fiberInfoCost f :=
  log_card_sections hf

/-- An **injective** function has at most one section, so its reverse
description is free. -/
theorem sectionCost_eq_zero_of_injective
    {f : A → B} (hf : Function.Injective f) :
    sectionCost f = 0 := by
  haveI : Subsingleton {s : B → A // ∀ b, f (s b) = b} :=
    ⟨fun s t => Subtype.ext (funext fun b => hf ((s.2 b).trans (t.2 b).symm))⟩
  haveI : Finite {s : B → A // ∀ b, f (s b) = b} := Finite.of_subsingleton
  unfold sectionCost
  have hle : Nat.card {s : B → A // ∀ b, f (s b) = b} ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.mpr inferInstance
  rcases (by omega : Nat.card {s : B → A // ∀ b, f (s b) = b} = 0
      ∨ Nat.card {s : B → A // ∀ b, f (s b) = b} = 1) with h | h <;>
    rw [h] <;> simp

/-- **The ratchet** (C8): a non-injective surjection has strictly
positive reverse-description cost — recovering the input is genuinely
costly. -/
theorem sectionCost_pos_of_not_injective [Fintype A] [Fintype B] [DecidableEq B]
    {f : A → B} (hsurj : Function.Surjective f) (hf : ¬ Function.Injective f) :
    0 < sectionCost f := by
  rw [sectionCost_eq_fiberInfoCost hsurj]
  exact fiberInfoCost_pos_of_not_injective hf

/-- **Forward description cost**: `|A| · log |B|` — the bits to specify
which of `|B|^|A|` functions `f` is. -/
noncomputable def descriptionCost [Fintype A] [Fintype B] (_f : A → B) : ℝ :=
  (Fintype.card A : ℝ) * Real.log (Fintype.card B : ℝ)

/-- Forward cost, justified as a genuine count: `descriptionCost f` is
the log-number of all functions `A → B`. -/
theorem descriptionCost_eq [Fintype A] [Fintype B] (f : A → B) :
    descriptionCost f = Real.log (Nat.card (A → B)) := by
  unfold descriptionCost
  rw [Nat.card_fun, Nat.cast_pow, Real.log_pow, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]

end Meno
