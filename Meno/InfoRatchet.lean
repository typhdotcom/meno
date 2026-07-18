import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Card
import Mathlib.Data.ENNReal.Real

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

The numerical (`ℝ`-valued) cost API is **restricted to finite types**
(review #3, finding 1): `Nat.card` of an infinite type is `0`, so an
unrestricted `log (Nat.card ·)` silently prices infinite ambiguity at
zero (`ℕ → Unit` would have had cost `0`). Finiteness is demanded by
the definitions themselves; the extended (`ℝ≥0∞`-valued) costs
`sectionCostE` and `recoveryCostE` price the impossible cases at `⊤`;
and the only cost statement about infinite types is the
cardinality-free ratchet `section_not_surjective_of_not_injective`.

This file isolates the fiber-information layer. Basic.lean's old
axiomatized transition-cost class (its reconciliation program was
falsified in Phase 17) is deleted as of C9 —
the ratchet below is derived, and `simplicial_ratchet` consumes it. The
compression-map specialization — `#sections = |G_q|^{q^{b₁}}`, tying the
count to the keystone K1–K3 — lives in `Meno/ResolutionCount.lean`. -/

namespace Meno

open scoped BigOperators ENNReal

universe u

variable {A B : Type u}

/-- Fiber information cost of a function on a **finite** domain:
`∑ b, log |f ⁻¹ {b}|`. Empty fibers (`b ∉ image f`) contribute
`log 0 = 0` by Mathlib convention — the extended per-output cost
`recoveryCostE` prices them honestly at `⊤`. -/
noncomputable def fiberInfoCost [Finite A] [Fintype B] [DecidableEq B]
    (f : A → B) : ℝ :=
  ∑ b : B, Real.log (Nat.card (f ⁻¹' {b}) : ℝ)

/-- **Per-output recovery cost** on a **finite** domain: the
information needed to pick the preimage of *one* output —
`log |f⁻¹{b}|`. Beware the boundary: on an *empty* fiber this is
`log 0 = 0` by Mathlib convention — an impossible recovery is not
free, it is impossible; `recoveryCostE` prices it at `⊤`. -/
noncomputable def recoveryCost [Finite A] (f : A → B) (b : B) : ℝ :=
  Real.log (Nat.card (f ⁻¹' {b}) : ℝ)

/-- The fiber information cost is the aggregate of the per-output
recovery costs. -/
theorem fiberInfoCost_eq_sum_recoveryCost [Finite A] [Fintype B]
    [DecidableEq B] (f : A → B) :
    fiberInfoCost f = ∑ b : B, recoveryCost f b := rfl

/-- Recovery costs are nonnegative (fibers of a finite domain have
natural cardinalities). -/
theorem recoveryCost_nonneg [Finite A] (f : A → B) (b : B) :
    0 ≤ recoveryCost f b := by
  unfold recoveryCost
  rcases (Nat.card (f ⁻¹' {b})).eq_zero_or_pos with hzero | hpos
  · simp [hzero]
  · exact Real.log_nonneg (by exact_mod_cast hpos)

theorem fiberInfoCost_nonneg [Finite A] [Fintype B] [DecidableEq B] (f : A → B) :
    0 ≤ fiberInfoCost f := by
  unfold fiberInfoCost
  refine Finset.sum_nonneg (fun b _ => ?_)
  rcases (Nat.card (f ⁻¹' {b})).eq_zero_or_pos with hzero | hpos
  · simp [hzero]
  · exact Real.log_nonneg (by exact_mod_cast hpos)

/-- Injective functions have zero fiber-info cost: every fiber is a
singleton (or empty), and `log 1 = log 0 = 0`. -/
theorem fiberInfoCost_of_injective [Finite A] [Fintype B] [DecidableEq B]
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
are then no sections. Finiteness of the domain is demanded (review #4):
on an infinite domain `Nat.card` collapses to `0` and the equation,
while true, would not be the advertised exact count. The general-
cardinality content is `sectionsEquivPiFiber` alone. -/
theorem card_sections [Finite A] [Fintype B] (f : A → B) :
    Nat.card {s : B → A // ∀ b, f (s b) = b} = ∏ b : B, Nat.card (f ⁻¹' {b}) := by
  rw [Nat.card_congr (sectionsEquivPiFiber f), Nat.card_pi]

/-- **The reverse-description count-cost**: the log-count of `f`'s
sections. Beware the boundary: when *no* section exists this is
`log 0 = 0` by Mathlib's junk convention — an impossible inverse is
not free, it is impossible. `sectionCostE` below is the honest
extended cost (`⊤` when no section exists); use it for cost
readings. Finiteness of both types is demanded (review #3): on
infinite types `Nat.card` of the section type is `0` and this would
price infinite ambiguity at zero. -/
noncomputable def sectionCost [Finite A] [Finite B] (f : A → B) : ℝ :=
  Real.log (Nat.card {s : B → A // ∀ b, f (s b) = b})

/-- Sections are invariant under postcomposition by a codomain
equivalence: relabeling outputs neither creates nor destroys reverse
descriptions (review #8 — proved once; consumers transport). -/
def sectionsEquivCompEquiv {C : Type u} (f : A → B) (e : B ≃ C) :
    {s : C → A // ∀ c, e (f (s c)) = c} ≃ {s : B → A // ∀ b, f (s b) = b} where
  toFun s := ⟨fun b => s.val (e b), fun b => e.injective (s.prop (e b))⟩
  invFun s := ⟨fun c => s.val (e.symm c), fun c => by
    rw [s.prop (e.symm c), Equiv.apply_symm_apply]⟩
  left_inv s := by
    apply Subtype.ext
    funext c
    show s.val (e (e.symm c)) = s.val c
    rw [Equiv.apply_symm_apply]
  right_inv s := by
    apply Subtype.ext
    funext b
    show s.val (e.symm (e b)) = s.val b
    rw [Equiv.symm_apply_apply]

/-- **Section cost is invariant under codomain relabeling** — the
transport lemma (review #8): postcomposing with an equivalence changes
neither the sections nor their count. -/
theorem sectionCost_comp_equiv {C : Type u} [Finite A] [Finite B] [Finite C]
    (f : A → B) (e : B ≃ C) :
    sectionCost (fun a : A => e (f a)) = sectionCost f := by
  unfold sectionCost
  exact congrArg Real.log
    (congrArg Nat.cast (Nat.card_congr (sectionsEquivCompEquiv f e)))

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

/-- An injective function has *at most one* section, so its log-count
is zero. This does **not** say reversal is free: an injective
non-surjective `f` has *no* section, and its honest extended cost is
`⊤` (`sectionCostE_eq_top_iff`). Zero honest cost characterizes
bijections (`sectionCostE_eq_zero_iff`). -/
theorem sectionCost_eq_zero_of_injective [Finite A] [Finite B]
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

/-- **The cardinality-free ratchet**: a section of a non-injective map
is never surjective — every reverse description misses states,
finite or not. (Where cardinalities exist, `log_card_sections`
quantifies the miss; this is the form that survives infinite
fibers.) -/
theorem section_not_surjective_of_not_injective {f : A → B}
    (hf : ¬ Function.Injective f) (r : B → A) (hr : ∀ b, f (r b) = b) :
    ¬ Function.Surjective r := by
  intro hsurj
  apply hf
  intro a₁ a₂ ha
  obtain ⟨b₁, rfl⟩ := hsurj a₁
  obtain ⟨b₂, rfl⟩ := hsurj a₂
  have hb : b₁ = b₂ := by rw [← hr b₁, ← hr b₂, ha]
  rw [hb]

/-- Sections exist exactly for surjections. -/
theorem sections_nonempty_iff_surjective (f : A → B) :
    Nonempty {s : B → A // ∀ b, f (s b) = b} ↔ Function.Surjective f := by
  constructor
  · rintro ⟨s⟩ b
    exact ⟨s.1 b, s.2 b⟩
  · intro hf
    choose s hs using hf
    exact ⟨⟨s, hs⟩⟩

open Classical in
/-- **The extended reverse-description cost**: `⊤` when no section
exists. An impossible inverse is not free — it is impossible. -/
noncomputable def sectionCostE [Finite A] [Finite B] (f : A → B) : ℝ≥0∞ :=
  if Function.Surjective f then ENNReal.ofReal (sectionCost f) else ⊤

/-- Infinite reverse cost characterizes non-surjectivity. -/
theorem sectionCostE_eq_top_iff [Finite A] [Finite B] (f : A → B) :
    sectionCostE f = ⊤ ↔ ¬ Function.Surjective f := by
  classical
  unfold sectionCostE
  split_ifs with h
  · simp [h, ENNReal.ofReal_ne_top]
  · simp [h]

/-- For surjections, the extended cost is the fiber information. -/
theorem sectionCostE_eq_fiberInfoCost [Fintype A] [Fintype B] [DecidableEq B]
    {f : A → B} (hf : Function.Surjective f) :
    sectionCostE f = ENNReal.ofReal (fiberInfoCost f) := by
  classical
  unfold sectionCostE
  rw [if_pos hf, log_card_sections hf]

/-- **Zero reverse cost characterizes bijections** — not arbitrary
injections. The only maps that are free to reverse are the ones that
lose nothing and miss nothing. -/
theorem sectionCostE_eq_zero_iff [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) : sectionCostE f = 0 ↔ Function.Bijective f := by
  constructor
  · intro h0
    have hsurj : Function.Surjective f := by
      by_contra hns
      have htop := (sectionCostE_eq_top_iff f).mpr hns
      rw [h0] at htop
      exact (by simp : (0 : ℝ≥0∞) ≠ ⊤) htop
    refine ⟨?_, hsurj⟩
    by_contra hni
    have hpos := fiberInfoCost_pos_of_not_injective hni
    have heq := sectionCostE_eq_fiberInfoCost hsurj
    rw [h0] at heq
    have hle := ENNReal.ofReal_eq_zero.mp heq.symm
    linarith
  · intro hbij
    classical
    unfold sectionCostE
    rw [if_pos hbij.surjective, log_card_sections hbij.surjective,
      fiberInfoCost_of_injective hbij.injective]
    simp

open Classical in
/-- **The extended per-output recovery cost**: `⊤` on an empty fiber.
An output that cannot be produced cannot be recovered from — that
recovery is not free, it is impossible. -/
noncomputable def recoveryCostE [Finite A] (f : A → B) (b : B) : ℝ≥0∞ :=
  if b ∈ Set.range f then ENNReal.ofReal (recoveryCost f b) else ⊤

/-- Infinite recovery cost characterizes the outputs `f` misses. -/
theorem recoveryCostE_eq_top_iff [Finite A] (f : A → B) (b : B) :
    recoveryCostE f b = ⊤ ↔ b ∉ Set.range f := by
  classical
  unfold recoveryCostE
  split_ifs with h
  · simp [h, ENNReal.ofReal_ne_top]
  · simp [h]

/-- **The extended coding identity**: the extended reverse-description
cost is the sum of the extended per-output recovery costs — on both
sides of the boundary. For a surjection both sides are the finite
fiber information; the moment one output is missed, both sides are
`⊤`. -/
theorem sectionCostE_eq_sum_recoveryCostE [Fintype A] [Fintype B]
    [DecidableEq B] (f : A → B) :
    sectionCostE f = ∑ b : B, recoveryCostE f b := by
  classical
  by_cases hf : Function.Surjective f
  · have hall : ∀ b : B, b ∈ Set.range f := fun b => hf b
    have hterm : ∀ b : B, recoveryCostE f b
        = ENNReal.ofReal (recoveryCost f b) := fun b => by
      unfold recoveryCostE
      rw [if_pos (hall b)]
    rw [sectionCostE_eq_fiberInfoCost hf,
      Finset.sum_congr rfl (fun b _ => hterm b),
      ← ENNReal.ofReal_sum_of_nonneg (fun b _ => recoveryCost_nonneg f b),
      fiberInfoCost_eq_sum_recoveryCost]
  · obtain ⟨b, hb⟩ := not_forall.mp fun hc => hf fun b => (hc b)
    have hbtop : recoveryCostE f b = ⊤ :=
      (recoveryCostE_eq_top_iff f b).mpr (by
        intro hmem
        exact hb (by obtain ⟨a, ha⟩ := hmem; exact ⟨a, ha⟩))
    have htop : (∑ b : B, recoveryCostE f b) = ⊤ :=
      eq_top_iff.mpr (le_trans (le_of_eq hbtop.symm)
        (Finset.single_le_sum (fun c _ => zero_le _) (Finset.mem_univ b)))
    rw [(sectionCostE_eq_top_iff f).mpr hf, htop]

/-- **Forward description cost**: `|A| · log |B|` — the information
(in nats: `Real.log` is the natural logarithm) to specify which of
`|B|^|A|` functions `f` is. -/
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
