import Meno.Basic
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

/-! ## Shannon entropy and the uniform-lift chain rule (review #9)

The gravity face of the carrier is priced by genuine distribution
entropies, not only log-cardinalities: `shannonEntropy` is the Shannon
entropy (nats) of a mass function on a finite type;
`shannonEntropy_comp_div` is the chain rule for a uniform lift along a
constant-fiber map — the lifted entropy exceeds the base entropy by
exactly the log of the fiber size; `shannonEntropy_uniform` identifies
the uniform case with the log-cardinality complexity. The carrier
instantiation — the intrinsic Gibbs distribution pushed through
`H¹(G;ℤ) → H1Reduction G q` — lives in `Meno/ResolutionCount.lean`. -/

/-- **Shannon entropy** (nats) of a mass function on a finite type. -/
noncomputable def shannonEntropy {X : Type u} [Fintype X] (p : X → ℝ) : ℝ :=
  -∑ x, p x * Real.log (p x)

/-- Summing a composite through a map with constant fiber count `m`
multiplies the base sum by `m`. -/
theorem sum_comp_card_fiber {X D : Type u} [Fintype X] [Fintype D]
    [DecidableEq D] (f : X → D) {m : ℕ}
    (hfib : ∀ d, Nat.card {x : X // f x = d} = m) (g : D → ℝ) :
    ∑ x, g (f x) = m * ∑ d, g d := by
  rw [← Finset.sum_fiberwise' Finset.univ f g, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_const]
  have hcard : (Finset.univ.filter fun x : X => f x = d).card = m := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact hfib d
  rw [hcard, nsmul_eq_mul]

/-- **The entropy chain rule for a uniform lift** (review #9): pulling
a distribution back along a constant-fiber map, dividing each mass
evenly across the fiber, adds exactly the log of the fiber size. -/
theorem shannonEntropy_comp_div {X D : Type u} [Fintype X] [Fintype D]
    [DecidableEq D] (f : X → D) (p : D → ℝ) {m : ℕ} (hm : 0 < m)
    (hfib : ∀ d, Nat.card {x : X // f x = d} = m)
    (hp1 : ∑ d, p d = 1) (hp : ∀ d, 0 ≤ p d) :
    shannonEntropy (fun x => p (f x) / m)
      = shannonEntropy p + Real.log m := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold shannonEntropy
  rw [sum_comp_card_fiber f hfib (fun d => p d / m * Real.log (p d / m))]
  have hterm : ∀ d, (m : ℝ) * (p d / m * Real.log (p d / m))
      = p d * Real.log (p d) - p d * Real.log m := by
    intro d
    rcases eq_or_lt_of_le (hp d) with h0 | hpos
    · rw [← h0]
      simp
    · rw [Real.log_div (ne_of_gt hpos) hm']
      field_simp
  rw [Finset.mul_sum, Finset.sum_congr rfl fun d _ => hterm d,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul]
  ring

/-- Entropy of the uniform distribution is the log-cardinality — the
bridge from distribution entropy to `uniformAction` complexity. -/
theorem shannonEntropy_uniform (X : Type u) [Fintype X] [Nonempty X] :
    shannonEntropy (fun _ : X => ((Fintype.card X : ℝ))⁻¹)
      = Real.log (Fintype.card X) := by
  have hpos : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  unfold shannonEntropy
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.log_inv]
  field_simp

/-- A map with constant fiber count `m` multiplies cardinalities. -/
theorem card_eq_card_mul_of_fiber {X D : Type u} [Fintype X] [Fintype D]
    [DecidableEq D] (f : X → D) {m : ℕ}
    (hfib : ∀ d, Nat.card {x : X // f x = d} = m) :
    Fintype.card X = Fintype.card D * m := by
  rw [← Finset.card_univ (α := X),
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (f x))]
  rw [Finset.sum_congr rfl fun d _ =>
    (show (Finset.univ.filter fun x : X => f x = d).card = m by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact hfib d)]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-! ## Finite distributions (review #10)

The distribution semantics of the gravity face, as one abstraction: a
`FinDist` carries nonnegativity and normalization; `map` is the
pushforward, `uniformLift` the uniform fiber lift, `coupling` the
shared-base coupling on the pullback. The lift pushforward law
(`map_uniformLift`), both coupling marginals (`coupling_fst`,
`coupling_snd`), and **the entropy gravity identity**
(`entropy_gravity` — `H(coupling) + H(base) = H(lift) + H(lift)`) are
proved once, here. The graph instantiations — the Gibbs residue
distribution and the uniform distribution — live in
`Meno/ResolutionCount.lean`. -/

/-- A **finite probability distribution**: a nonnegative, normalized
mass function on a finite type. -/
structure FinDist (X : Type u) [Fintype X] where
  /-- The mass function. -/
  mass : X → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  sum_one : ∑ x, mass x = 1

namespace FinDist

variable {X Y D : Type u} [Fintype X] [Fintype Y] [Fintype D]

theorem ext {P P' : FinDist X} (h : P.mass = P'.mass) : P = P' := by
  cases P
  cases P'
  simpa using h

/-- The Shannon entropy of a finite distribution. -/
noncomputable def entropy (P : FinDist X) : ℝ := shannonEntropy P.mass

/-- **Pushforward** along a map: fiber sums. -/
noncomputable def map [DecidableEq D] (f : X → D) (P : FinDist X) :
    FinDist D where
  mass d := ∑ x ∈ Finset.univ.filter (fun x => f x = d), P.mass x
  nonneg d := Finset.sum_nonneg fun x _ => P.nonneg x
  sum_one := by
    rw [Finset.sum_fiberwise Finset.univ f P.mass]
    exact P.sum_one

/-- **The uniform fiber lift**: pull a base distribution back along a
constant-fiber map, dividing each mass evenly across the fiber. -/
noncomputable def uniformLift [DecidableEq D] (f : X → D) {m : ℕ}
    (hm : 0 < m) (hfib : ∀ d, Nat.card {x : X // f x = d} = m)
    (P : FinDist D) : FinDist X where
  mass x := P.mass (f x) / m
  nonneg x := div_nonneg (P.nonneg _) (by positivity)
  sum_one := by
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [sum_comp_card_fiber f hfib (fun d => P.mass d / m),
      ← Finset.sum_div, P.sum_one]
    field_simp

/-- The lift's entropy: base entropy plus the fiber log — the chain
rule, in distribution form. -/
theorem entropy_uniformLift [DecidableEq D] (f : X → D) {m : ℕ}
    (hm : 0 < m) (hfib : ∀ d, Nat.card {x : X // f x = d} = m)
    (P : FinDist D) :
    (P.uniformLift f hm hfib).entropy = P.entropy + Real.log m :=
  shannonEntropy_comp_div f P.mass hm hfib P.sum_one P.nonneg

/-- **The lift pushforward law** (review #10): pushing the uniform
lift forward recovers the base distribution. -/
theorem map_uniformLift [DecidableEq D] (f : X → D) {m : ℕ}
    (hm : 0 < m) (hfib : ∀ d, Nat.card {x : X // f x = d} = m)
    (P : FinDist D) :
    (P.uniformLift f hm hfib).map f = P := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  apply ext
  funext d
  show ∑ x ∈ Finset.univ.filter (fun x => f x = d), P.mass (f x) / m
    = P.mass d
  rw [Finset.sum_congr rfl fun x hx => by
    rw [(Finset.mem_filter.mp hx).2]]
  rw [Finset.sum_const,
    show (Finset.univ.filter fun x : X => f x = d).card = m by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact hfib d,
    nsmul_eq_mul]
  field_simp

/-- The uniform distribution on a finite nonempty type. -/
noncomputable def uniform (X : Type u) [Fintype X] [Nonempty X] :
    FinDist X where
  mass _ := (Fintype.card X : ℝ)⁻¹
  nonneg _ := by positivity
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀
        (Nat.cast_ne_zero.mpr Fintype.card_pos.ne' : (Fintype.card X : ℝ) ≠ 0)]

theorem entropy_uniform (X : Type u) [Fintype X] [Nonempty X] :
    (uniform X).entropy = Real.log (Fintype.card X) :=
  shannonEntropy_uniform X

/-- Lifting the uniform distribution uniformly is uniform. -/
theorem uniformLift_uniform [DecidableEq D] [Nonempty D] [Nonempty X]
    (f : X → D) {m : ℕ} (hm : 0 < m)
    (hfib : ∀ d, Nat.card {x : X // f x = d} = m) :
    (uniform D).uniformLift f hm hfib = uniform X := by
  apply ext
  funext x
  show (Fintype.card D : ℝ)⁻¹ / m = (Fintype.card X : ℝ)⁻¹
  rw [card_eq_card_mul_of_fiber f hfib]
  have hD : (0 : ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  push_cast
  rw [mul_inv]
  field_simp

/-- **The shared-base coupling** of two uniform lifts: on the
pullback, each base mass split evenly across the `m · m'` pairs above
it. -/
noncomputable def coupling [DecidableEq D] (f : X → D) (g : Y → D)
    [Fintype (SGD.Pullback f g)] {m m' : ℕ}
    (hm : 0 < m) (hm' : 0 < m')
    (hf : ∀ d, Nat.card {x : X // f x = d} = m)
    (hg : ∀ d, Nat.card {y : Y // g y = d} = m')
    (P : FinDist D) : FinDist (SGD.Pullback f g) where
  mass p := P.mass (SGD.Pullback.base p) / ((m * m' : ℕ) : ℝ)
  nonneg p := div_nonneg (P.nonneg _) (by positivity)
  sum_one := by
    have hfib : ∀ d,
        Nat.card {p : SGD.Pullback f g // SGD.Pullback.base p = d}
          = m * m' := fun d => by
      rw [Nat.card_congr (SGD.Pullback.baseFiberEquiv f g d),
        Nat.card_prod, hf d, hg d]
    have hmm : ((m * m' : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos hm hm').ne'
    rw [sum_comp_card_fiber
        (fun p : SGD.Pullback f g => SGD.Pullback.base p) hfib
        (fun d => P.mass d / ((m * m' : ℕ) : ℝ)),
      ← Finset.sum_div, P.sum_one]
    field_simp

omit [Fintype X] [Fintype Y] [Fintype D] in
/-- The constant fiber count of the pullback's base map. -/
theorem card_base_fiber (f : X → D) (g : Y → D) {m m' : ℕ}
    (hf : ∀ d, Nat.card {x : X // f x = d} = m)
    (hg : ∀ d, Nat.card {y : Y // g y = d} = m') (d : D) :
    Nat.card {p : SGD.Pullback f g // SGD.Pullback.base p = d}
      = m * m' := by
  rw [Nat.card_congr (SGD.Pullback.baseFiberEquiv f g d),
    Nat.card_prod, hf d, hg d]

omit [Fintype X] [Fintype Y] in
/-- The coupling's entropy: base entropy plus both fiber logs. -/
theorem entropy_coupling [DecidableEq D] (f : X → D) (g : Y → D)
    [Fintype (SGD.Pullback f g)] {m m' : ℕ}
    (hm : 0 < m) (hm' : 0 < m')
    (hf : ∀ d, Nat.card {x : X // f x = d} = m)
    (hg : ∀ d, Nat.card {y : Y // g y = d} = m') (P : FinDist D) :
    (P.coupling f g hm hm' hf hg).entropy
      = P.entropy + Real.log ((m * m' : ℕ) : ℝ) :=
  shannonEntropy_comp_div
    (fun p : SGD.Pullback f g => SGD.Pullback.base p) P.mass
    (Nat.mul_pos hm hm') (card_base_fiber f g hf hg) P.sum_one P.nonneg

omit [Fintype Y] in
/-- **The first coupling marginal is the first uniform lift**
(review #10). -/
theorem coupling_fst [DecidableEq D] [DecidableEq X] (f : X → D)
    (g : Y → D) [Fintype (SGD.Pullback f g)] {m m' : ℕ}
    (hm : 0 < m) (hm' : 0 < m')
    (hf : ∀ d, Nat.card {x : X // f x = d} = m)
    (hg : ∀ d, Nat.card {y : Y // g y = d} = m') (P : FinDist D) :
    (P.coupling f g hm hm' hf hg).map (fun p => p.val.1)
      = P.uniformLift f hm hf := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmR' : (0 : ℝ) < m' := by exact_mod_cast hm'
  apply ext
  funext x
  show ∑ p ∈ Finset.univ.filter
      (fun p : SGD.Pullback f g => p.val.1 = x),
      P.mass (SGD.Pullback.base p) / ((m * m' : ℕ) : ℝ)
    = P.mass (f x) / m
  rw [Finset.sum_congr rfl fun p hp => by
    rw [show SGD.Pullback.base p = f x from
      congrArg f (Finset.mem_filter.mp hp).2]]
  rw [Finset.sum_const,
    show (Finset.univ.filter
        fun p : SGD.Pullback f g => p.val.1 = x).card = m' by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
        Nat.card_congr (SGD.Pullback.fstFiberEquiv f g x)]
      exact hg (f x),
    nsmul_eq_mul]
  push_cast
  field_simp

omit [Fintype X] in
/-- **The second coupling marginal is the second uniform lift**
(review #10). -/
theorem coupling_snd [DecidableEq D] [DecidableEq Y] (f : X → D)
    (g : Y → D) [Fintype (SGD.Pullback f g)] {m m' : ℕ}
    (hm : 0 < m) (hm' : 0 < m')
    (hf : ∀ d, Nat.card {x : X // f x = d} = m)
    (hg : ∀ d, Nat.card {y : Y // g y = d} = m') (P : FinDist D) :
    (P.coupling f g hm hm' hf hg).map (fun p => p.val.2)
      = P.uniformLift g hm' hg := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmR' : (0 : ℝ) < m' := by exact_mod_cast hm'
  apply ext
  funext y
  show ∑ p ∈ Finset.univ.filter
      (fun p : SGD.Pullback f g => p.val.2 = y),
      P.mass (SGD.Pullback.base p) / ((m * m' : ℕ) : ℝ)
    = P.mass (g y) / m'
  rw [Finset.sum_congr rfl fun p hp => by
    rw [show SGD.Pullback.base p = g y from
      p.prop.trans (congrArg g (Finset.mem_filter.mp hp).2)]]
  rw [Finset.sum_const,
    show (Finset.univ.filter
        fun p : SGD.Pullback f g => p.val.2 = y).card = m by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
        Nat.card_congr (SGD.Pullback.sndFiberEquiv f g y)]
      exact hf (g y),
    nsmul_eq_mul]
  push_cast
  field_simp

omit [Fintype X] [Fintype Y] in
/-- Coupling the uniform distribution is uniform on the pullback. -/
theorem coupling_uniform [DecidableEq D] [Nonempty D] (f : X → D)
    (g : Y → D) [Fintype (SGD.Pullback f g)]
    [Nonempty (SGD.Pullback f g)] {m m' : ℕ}
    (hm : 0 < m) (hm' : 0 < m')
    (hf : ∀ d, Nat.card {x : X // f x = d} = m)
    (hg : ∀ d, Nat.card {y : Y // g y = d} = m') :
    (uniform D).coupling f g hm hm' hf hg
      = uniform (SGD.Pullback f g) := by
  apply ext
  funext p
  show (Fintype.card D : ℝ)⁻¹ / ((m * m' : ℕ) : ℝ)
    = (Fintype.card (SGD.Pullback f g) : ℝ)⁻¹
  rw [card_eq_card_mul_of_fiber
    (fun p : SGD.Pullback f g => SGD.Pullback.base p)
    (card_base_fiber f g hf hg)]
  have hD : (0 : ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have hmm : (0 : ℝ) < ((m * m' : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hm hm'
  push_cast
  rw [mul_inv]
  field_simp

/-- **THE ENTROPY GRAVITY IDENTITY, generically** (review #10): for
any base distribution uniformly lifted along two constant-fiber maps,
the shared-base coupling's entropy plus the base's entropy equals the
two lifts' entropies — sharing the base saves exactly one copy of its
entropy. Proved once; every instance is an instantiation. -/
theorem entropy_gravity [DecidableEq D] (f : X → D) (g : Y → D)
    [Fintype (SGD.Pullback f g)] {m m' : ℕ}
    (hm : 0 < m) (hm' : 0 < m')
    (hf : ∀ d, Nat.card {x : X // f x = d} = m)
    (hg : ∀ d, Nat.card {y : Y // g y = d} = m') (P : FinDist D) :
    (P.coupling f g hm hm' hf hg).entropy + P.entropy
      = (P.uniformLift f hm hf).entropy
        + (P.uniformLift g hm' hg).entropy := by
  rw [entropy_coupling f g hm hm' hf hg,
    entropy_uniformLift f hm hf, entropy_uniformLift g hm' hg,
    Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hm.ne') (by exact_mod_cast hm'.ne')]
  ring

end FinDist

end Meno
