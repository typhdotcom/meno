import Meno.Basic
import Meno.SectorAction
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

/-! ## The Gibbs entropy split: pricing meets entropy (review #12)

For a finite sector action the Shannon entropy of its Gibbs
distribution splits as complexity plus expected energy,
`H(μ) = log Z + ⟨E⟩` — the identity that puts *pricing* (the action's
`log Z` and its energy expectation) inside every entropy statement
about a Gibbs law. Pointwise, `-log μ(k) = E k + log Z`; summing
against `μ` gives the split. -/

/-- **The Gibbs entropy split** (review #12): for a finite sector
action, `H(gibbsMass) = K + ⟨E⟩`. -/
theorem SectorAction.entropy_gibbs (A : SectorAction.{u}) [Fintype A.Λ] :
    shannonEntropy A.gibbsMass = A.complexity + A.gibbsExpect A.E := by
  have hlog : ∀ k, Real.log (A.gibbsMass k) = -A.E k - A.complexity := by
    intro k
    show Real.log (A.weight k / A.partFn) = _
    rw [Real.log_div (ne_of_gt (A.weight_pos k)) (ne_of_gt A.partFn_pos)]
    show Real.log (Real.exp (-A.E k)) - Real.log A.partFn = _
    rw [Real.log_exp]
    rfl
  have hexpect : A.gibbsExpect A.E = ∑ k, A.E k * A.gibbsMass k := by
    show (∑' k, A.E k * A.gibbsMass k) = _
    rw [tsum_fintype]
  have hsum : ∑ k, A.gibbsMass k = 1 := by
    have h := A.tsum_gibbsMass_eq_one
    rwa [tsum_fintype] at h
  have hterm : ∀ k, A.gibbsMass k * Real.log (A.gibbsMass k)
      = -(A.E k * A.gibbsMass k) - A.complexity * A.gibbsMass k := by
    intro k
    rw [hlog k]
    ring
  show -∑ k, A.gibbsMass k * Real.log (A.gibbsMass k) = _
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, ← Finset.mul_sum, hsum, hexpect]
  ring

/-- **Strict Gibbs fluctuation, finite form** (review #14): on a
finite sector action, an observable taking two distinct values has
strictly positive variance — both moments are finite sums, and one of
the two witnesses misses the mean. -/
theorem SectorAction.gibbsVariance_pos_of_ne (A : SectorAction.{u})
    [Fintype A.Λ] (f : A.Λ → ℝ) {k l : A.Λ} (h : f k ≠ f l) :
    0 < A.gibbsVariance f := by
  have hsq : Summable (fun k => f k ^ 2 * A.gibbsMass k) :=
    (hasSum_fintype _).summable
  have hf : Summable (fun k => f k * A.gibbsMass k) :=
    (hasSum_fintype _).summable
  by_cases hk : f k = A.gibbsExpect f
  · refine A.gibbsVariance_pos f hsq hf (k₀ := l) ?_
    rw [← hk]
    exact fun heq => h heq.symm
  · exact A.gibbsVariance_pos f hsq hf (k₀ := k) hk

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

/-! ### The uniform entropy defect (review #11)

`Δ(P) = log|X| − H(P)` measures how far a distribution sits below
maximal ignorance. It is nonnegative (`defect_nonneg` — the maximum
entropy theorem), vanishes exactly at the uniform distribution
(`defect_eq_zero_iff`), and is **preserved** by uniform fiber lifting
and shared-base coupling (`defect_uniformLift`, `defect_coupling`) —
the bridge from action-priced entropies to uniform counting. -/

/-- **The uniform entropy defect**: `Δ(P) = log|X| − H(P)`. -/
noncomputable def defect [Nonempty X] (P : FinDist X) : ℝ :=
  Real.log (Fintype.card X) - P.entropy

private lemma defect_term_nonneg {N : ℕ} (hN : 0 < N) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ p * Real.log (p * N) - p + 1 / N := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rcases eq_or_lt_of_le hp with h0 | hpos
  · rw [← h0]
    simp
  · have ht : 0 < p * N := mul_pos hpos hN'
    have hlog : Real.log (1 / (p * N)) ≤ 1 / (p * N) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [one_div, Real.log_inv] at hlog
    have h2 : 1 - (p * N)⁻¹ ≤ Real.log (p * N) := by linarith
    have h3 : p * (1 - (p * N)⁻¹) ≤ p * Real.log (p * N) :=
      mul_le_mul_of_nonneg_left h2 hp
    have h4 : p * (1 - (p * N)⁻¹) = p - 1 / N := by
      field_simp
    linarith

private lemma defect_term_eq_zero {N : ℕ} (hN : 0 < N) {p : ℝ} (hp : 0 ≤ p)
    (h0 : p * Real.log (p * N) - p + 1 / N = 0) : p = (N : ℝ)⁻¹ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rcases eq_or_lt_of_le hp with hz | hpos
  · exfalso
    rw [← hz] at h0
    simp at h0
    exact absurd h0 (by positivity)
  · by_contra hne
    have ht : 0 < p * N := mul_pos hpos hN'
    have htne : p * N ≠ 1 := by
      intro h1
      apply hne
      field_simp at h1 ⊢
      linarith
    have hstrict : Real.log (1 / (p * N)) < 1 / (p * N) - 1 :=
      Real.log_lt_sub_one_of_pos (by positivity)
        (by
          rw [one_div]
          exact fun h => htne (by
            have := congrArg (· * (p * N)) h
            field_simp at this
            linarith))
    rw [one_div, Real.log_inv] at hstrict
    have h2 : 1 - (p * N)⁻¹ < Real.log (p * N) := by linarith
    have h3 : p * (1 - (p * N)⁻¹) < p * Real.log (p * N) :=
      mul_lt_mul_of_pos_left h2 hpos
    have h4 : p * (1 - (p * N)⁻¹) = p - 1 / N := by
      field_simp
    linarith

private lemma defect_eq_sum [Nonempty X] (P : FinDist X) :
    P.defect = ∑ x, (P.mass x * Real.log (P.mass x * Fintype.card X)
      - P.mass x + 1 / Fintype.card X) := by
  have hN : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ x, P.mass x * Real.log (P.mass x * Fintype.card X)
      = P.mass x * Real.log (P.mass x)
        + P.mass x * Real.log (Fintype.card X) := by
    intro x
    rcases eq_or_lt_of_le (P.nonneg x) with h0 | hpos
    · rw [← h0]
      simp
    · rw [Real.log_mul hpos.ne' hN.ne']
      ring
  show Real.log (Fintype.card X) - shannonEntropy P.mass = _
  rw [shannonEntropy,
    Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_add_distrib,
    ← Finset.sum_mul, P.sum_one, one_mul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div,
    div_self hN.ne']
  ring

/-- **The maximum entropy theorem**: the defect is nonnegative —
`H(P) ≤ log|X|`. -/
theorem defect_nonneg [Nonempty X] (P : FinDist X) : 0 ≤ P.defect := by
  rw [P.defect_eq_sum]
  exact Finset.sum_nonneg fun x _ =>
    defect_term_nonneg Fintype.card_pos (P.nonneg x)

/-- **Zero defect characterizes the uniform distribution.** -/
theorem defect_eq_zero_iff [Nonempty X] (P : FinDist X) :
    P.defect = 0 ↔ P = uniform X := by
  constructor
  · intro h0
    apply ext
    funext x
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => defect_term_nonneg Fintype.card_pos (P.nonneg x))).mp
      ((P.defect_eq_sum).symm.trans h0)
    have hx := hterms x (Finset.mem_univ x)
    exact defect_term_eq_zero Fintype.card_pos (P.nonneg x) hx
  · rintro rfl
    rw [defect, entropy_uniform]
    ring

/-- **Uniform fiber lifting preserves the defect** (review #11): the
lift adds `log m` to the entropy and `log m` to the log-cardinality. -/
theorem defect_uniformLift [DecidableEq D] [Nonempty D] [Nonempty X]
    (f : X → D) {m : ℕ} (hm : 0 < m)
    (hfib : ∀ d, Nat.card {x : X // f x = d} = m) (P : FinDist D) :
    (P.uniformLift f hm hfib).defect = P.defect := by
  rw [defect, defect, entropy_uniformLift,
    card_eq_card_mul_of_fiber f hfib, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast Fintype.card_pos.ne' :
        (Fintype.card D : ℝ) ≠ 0)
      (by exact_mod_cast hm.ne' : (m : ℝ) ≠ 0)]
  ring

/-- **Conditional entropy along a map** (review #15): the expected
information remaining in `x` once `f x` is known —
`H(P | f) = −∑ₓ p(x)·log(p(x)/p(f x))`. -/
noncomputable def condEntropy [DecidableEq D] (f : X → D)
    (P : FinDist X) : ℝ :=
  -∑ x, P.mass x * Real.log (P.mass x / (P.map f).mass (f x))

/-- **The entropy chain rule along a map** (review #15): for a fully
supported distribution, `H(P) = H(f_*P) + H(P | f)` — entropy is the
pushforward's entropy plus the conditional entropy of the fibers. -/
theorem entropy_eq_map_add_condEntropy [DecidableEq D] (f : X → D)
    (P : FinDist X) (hpos : ∀ x, 0 < P.mass x) :
    P.entropy = (P.map f).entropy + P.condEntropy f := by
  have hmap_pos : ∀ x, 0 < (P.map f).mass (f x) := by
    intro x
    refine Finset.sum_pos' (fun y _ => P.nonneg y) ⟨x, ?_, hpos x⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩
  have hterm : ∀ x, P.mass x * Real.log (P.mass x / (P.map f).mass (f x))
      = P.mass x * Real.log (P.mass x)
        - P.mass x * Real.log ((P.map f).mass (f x)) := by
    intro x
    rw [Real.log_div (hpos x).ne' (hmap_pos x).ne']
    ring
  have hgroup : ∑ x, P.mass x * Real.log ((P.map f).mass (f x))
      = ∑ d, (P.map f).mass d * Real.log ((P.map f).mass d) := by
    rw [← Finset.sum_fiberwise Finset.univ f
      (fun x => P.mass x * Real.log ((P.map f).mass (f x)))]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_congr rfl (fun x hx => by
        rw [(Finset.mem_filter.mp hx).2]),
      ← Finset.sum_mul]
    rfl
  show -∑ x, P.mass x * Real.log (P.mass x)
    = (-∑ d, (P.map f).mass d * Real.log ((P.map f).mass d))
      + -∑ x, P.mass x * Real.log (P.mass x / (P.map f).mass (f x))
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_sub_distrib,
    ← hgroup]
  ring

private lemma gibbs_term_le (P Q : FinDist X) (hQ : ∀ x, 0 < Q.mass x)
    (x : X) :
    P.mass x - Q.mass x
      ≤ P.mass x * Real.log (P.mass x / Q.mass x) := by
  rcases eq_or_lt_of_le (P.nonneg x) with h0 | hp
  · rw [← h0, zero_mul, zero_sub]
    exact neg_nonpos.mpr (hQ x).le
  · have h := Real.log_le_sub_one_of_pos (div_pos (hQ x) hp)
    have hlog : Real.log (P.mass x / Q.mass x)
        = -Real.log (Q.mass x / P.mass x) := by
      rw [← Real.log_inv]
      congr 1
      rw [inv_div]
    rw [hlog]
    have h2 : 1 - Q.mass x / P.mass x
        ≤ -Real.log (Q.mass x / P.mass x) := by linarith
    calc P.mass x - Q.mass x
        = P.mass x * (1 - Q.mass x / P.mass x) := by field_simp
      _ ≤ P.mass x * -Real.log (Q.mass x / P.mass x) :=
          mul_le_mul_of_nonneg_left h2 hp.le

/-- **The Gibbs inequality** (review #16): the relative entropy of a
distribution against a fully supported reference is nonnegative. -/
theorem sum_mul_log_div_nonneg (P Q : FinDist X)
    (hQ : ∀ x, 0 < Q.mass x) :
    0 ≤ ∑ x, P.mass x * Real.log (P.mass x / Q.mass x) :=
  calc (0 : ℝ) = ∑ x, (P.mass x - Q.mass x) := by
        rw [Finset.sum_sub_distrib, P.sum_one, Q.sum_one]
        ring
    _ ≤ ∑ x, P.mass x * Real.log (P.mass x / Q.mass x) :=
        Finset.sum_le_sum fun x _ => gibbs_term_le P Q hQ x

/-- **The strict Gibbs inequality** (review #16): distinct
distributions have strictly positive relative entropy. -/
theorem sum_mul_log_div_pos (P Q : FinDist X) (hQ : ∀ x, 0 < Q.mass x)
    (hne : P ≠ Q) :
    0 < ∑ x, P.mass x * Real.log (P.mass x / Q.mass x) := by
  have hx : ∃ x, P.mass x ≠ Q.mass x := by
    by_contra hall
    push_neg at hall
    exact hne (FinDist.ext (funext hall))
  obtain ⟨x₀, hx₀⟩ := hx
  have hstrict : P.mass x₀ - Q.mass x₀
      < P.mass x₀ * Real.log (P.mass x₀ / Q.mass x₀) := by
    rcases eq_or_lt_of_le (P.nonneg x₀) with h0 | hp
    · rw [← h0, zero_mul, zero_sub]
      exact neg_lt_zero.mpr (hQ x₀)
    · have hne1 : Q.mass x₀ / P.mass x₀ ≠ 1 := by
        intro h1
        rw [div_eq_one_iff_eq hp.ne'] at h1
        exact hx₀ h1.symm
      have h := Real.log_lt_sub_one_of_pos (div_pos (hQ x₀) hp) hne1
      have hlog : Real.log (P.mass x₀ / Q.mass x₀)
          = -Real.log (Q.mass x₀ / P.mass x₀) := by
        rw [← Real.log_inv]
        congr 1
        rw [inv_div]
      rw [hlog]
      have h2 : 1 - Q.mass x₀ / P.mass x₀
          < -Real.log (Q.mass x₀ / P.mass x₀) := by linarith
      calc P.mass x₀ - Q.mass x₀
          = P.mass x₀ * (1 - Q.mass x₀ / P.mass x₀) := by field_simp
        _ < P.mass x₀ * -Real.log (Q.mass x₀ / P.mass x₀) :=
            mul_lt_mul_of_pos_left h2 hp
  calc (0 : ℝ) = ∑ x, (P.mass x - Q.mass x) := by
        rw [Finset.sum_sub_distrib, P.sum_one, Q.sum_one]
        ring
    _ < ∑ x, P.mass x * Real.log (P.mass x / Q.mass x) :=
        Finset.sum_lt_sum (fun x _ => gibbs_term_le P Q hQ x)
          ⟨x₀, Finset.mem_univ x₀, hstrict⟩

/-- **Conditional entropy is nonnegative** (review #16): each mass is
at most its fiber's total. -/
theorem condEntropy_nonneg [DecidableEq D] (f : X → D) (P : FinDist X) :
    0 ≤ P.condEntropy f := by
  refine neg_nonneg.mpr (Finset.sum_nonpos fun x _ => ?_)
  rcases eq_or_lt_of_le (P.nonneg x) with h0 | hp
  · rw [← h0, zero_mul]
  · have hmap : P.mass x ≤ (P.map f).mass (f x) := by
      refine Finset.single_le_sum (fun y _ => P.nonneg y) ?_
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩
    have hmpos : 0 < (P.map f).mass (f x) := lt_of_lt_of_le hp hmap
    have hratio : P.mass x / (P.map f).mass (f x) ≤ 1 :=
      (div_le_one hmpos).mpr hmap
    have hlog : Real.log (P.mass x / (P.map f).mass (f x)) ≤ 0 :=
      Real.log_nonpos (div_nonneg (P.nonneg x) hmpos.le) hratio
    exact mul_nonpos_iff.mpr (Or.inl ⟨hp.le, hlog⟩)

/-- **Conditional entropy is strictly positive** (review #16) when a
fully supported distribution has two points in one fiber. -/
theorem condEntropy_pos [DecidableEq D] (f : X → D) (P : FinDist X)
    (hpos : ∀ x, 0 < P.mass x) {x y : X} (hxy : x ≠ y) (hf : f x = f y) :
    0 < P.condEntropy f := by
  classical
  have hle : ∀ z ∈ Finset.univ,
      P.mass z * Real.log (P.mass z / (P.map f).mass (f z)) ≤ 0 := by
    intro z _
    have hmap : P.mass z ≤ (P.map f).mass (f z) := by
      refine Finset.single_le_sum (fun w _ => P.nonneg w) ?_
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, rfl⟩
    have hmpos : 0 < (P.map f).mass (f z) := lt_of_lt_of_le (hpos z) hmap
    have hratio : P.mass z / (P.map f).mass (f z) ≤ 1 :=
      (div_le_one hmpos).mpr hmap
    have hlog : Real.log (P.mass z / (P.map f).mass (f z)) ≤ 0 :=
      Real.log_nonpos (div_nonneg (P.nonneg z) hmpos.le) hratio
    exact mul_nonpos_iff.mpr (Or.inl ⟨(hpos z).le, hlog⟩)
  have hstrict : P.mass x * Real.log (P.mass x / (P.map f).mass (f x)) < 0 := by
    have hmap : P.mass x + P.mass y ≤ (P.map f).mass (f x) := by
      have hsub : ({x, y} : Finset X)
          ⊆ Finset.univ.filter (fun z => f z = f x) := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
        · rw [Finset.mem_singleton.mp hz]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf.symm⟩
      have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun z _ _ => P.nonneg z)
      rwa [Finset.sum_pair hxy] at h
    have hlt : P.mass x < (P.map f).mass (f x) := by
      linarith [hpos y]
    have hmpos : 0 < (P.map f).mass (f x) := lt_trans (hpos x) hlt
    have hratio : P.mass x / (P.map f).mass (f x) < 1 :=
      (div_lt_one hmpos).mpr hlt
    exact mul_neg_of_pos_of_neg (hpos x)
      (Real.log_neg (div_pos (hpos x) hmpos) hratio)
  have hsum : ∑ z, P.mass z * Real.log (P.mass z / (P.map f).mass (f z))
      < 0 := by
    have h := Finset.sum_lt_sum hle ⟨x, Finset.mem_univ x, hstrict⟩
    simpa using h
  show (0 : ℝ) < -∑ z, P.mass z * Real.log (P.mass z / (P.map f).mass (f z))
  linarith

private lemma condEntropy_log_split [DecidableEq D] (f : X → D)
    {m : ℕ} (hm : 0 < m)
    (hfib : ∀ d, Nat.card {x : X // f x = d} = m) (P : FinDist X)
    (hpos : ∀ x, 0 < P.mass x) :
    ∑ x, P.mass x
        * Real.log (P.mass x / ((P.map f).uniformLift f hm hfib).mass x)
      = -P.condEntropy f + Real.log m := by
  have hmap_pos : ∀ x, 0 < (P.map f).mass (f x) := by
    intro x
    refine Finset.sum_pos' (fun y _ => P.nonneg y) ⟨x, ?_, hpos x⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hterm : ∀ x,
      P.mass x * Real.log (P.mass x / ((P.map f).mass (f x) / m))
        = P.mass x * Real.log (P.mass x / (P.map f).mass (f x))
          + P.mass x * Real.log m := by
    intro x
    rw [show P.mass x / ((P.map f).mass (f x) / m)
        = P.mass x / (P.map f).mass (f x) * m from by
      field_simp,
      Real.log_mul (div_pos (hpos x) (hmap_pos x)).ne' hm']
    ring
  show ∑ x, P.mass x * Real.log (P.mass x / ((P.map f).mass (f x) / m))
    = -P.condEntropy f + Real.log m
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_add_distrib,
    ← Finset.sum_mul, P.sum_one, one_mul]
  have hce : -P.condEntropy f
      = ∑ x, P.mass x * Real.log (P.mass x / (P.map f).mass (f x)) := by
    show -(-∑ x, P.mass x * Real.log (P.mass x / (P.map f).mass (f x))) = _
    rw [neg_neg]
  rw [hce]

/-- **The constant-fiber upper bound** (review #16): the conditional
entropy of a fully supported distribution along a constant-fiber map
is at most the fiber log — with the gap the relative entropy against
the fiber-uniformized distribution. -/
theorem condEntropy_le_log [DecidableEq D] (f : X → D) {m : ℕ}
    (hm : 0 < m) (hfib : ∀ d, Nat.card {x : X // f x = d} = m)
    (P : FinDist X) (hpos : ∀ x, 0 < P.mass x) :
    P.condEntropy f ≤ Real.log m := by
  have hQpos : ∀ x, 0 < ((P.map f).uniformLift f hm hfib).mass x := by
    intro x
    have hmap_pos : 0 < (P.map f).mass (f x) := by
      refine Finset.sum_pos' (fun y _ => P.nonneg y) ⟨x, ?_, hpos x⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩
    show 0 < (P.map f).mass (f x) / m
    positivity
  have h := sum_mul_log_div_nonneg P
    ((P.map f).uniformLift f hm hfib) hQpos
  rw [condEntropy_log_split f hm hfib P hpos] at h
  linarith

/-- **The strict constant-fiber bound** (review #16): strict unless
the distribution is its own fiber-uniformization. -/
theorem condEntropy_lt_log [DecidableEq D] (f : X → D) {m : ℕ}
    (hm : 0 < m) (hfib : ∀ d, Nat.card {x : X // f x = d} = m)
    (P : FinDist X) (hpos : ∀ x, 0 < P.mass x)
    (hne : P ≠ (P.map f).uniformLift f hm hfib) :
    P.condEntropy f < Real.log m := by
  have hQpos : ∀ x, 0 < ((P.map f).uniformLift f hm hfib).mass x := by
    intro x
    have hmap_pos : 0 < (P.map f).mass (f x) := by
      refine Finset.sum_pos' (fun y _ => P.nonneg y) ⟨x, ?_, hpos x⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩
    show 0 < (P.map f).mass (f x) / m
    positivity
  have h := sum_mul_log_div_pos P
    ((P.map f).uniformLift f hm hfib) hQpos hne
  rw [condEntropy_log_split f hm hfib P hpos] at h
  linarith

omit [Fintype X] [Fintype Y] in
/-- **Shared-base coupling preserves the defect** (review #11): the
coupling adds `log(m·m')` to both sides. -/
theorem defect_coupling [DecidableEq D] [Nonempty D] (f : X → D)
    (g : Y → D) [Fintype (SGD.Pullback f g)]
    [Nonempty (SGD.Pullback f g)] {m m' : ℕ}
    (hm : 0 < m) (hm' : 0 < m')
    (hf : ∀ d, Nat.card {x : X // f x = d} = m)
    (hg : ∀ d, Nat.card {y : Y // g y = d} = m') (P : FinDist D) :
    (P.coupling f g hm hm' hf hg).defect = P.defect := by
  rw [defect, defect, entropy_coupling,
    card_eq_card_mul_of_fiber
      (fun p : SGD.Pullback f g => SGD.Pullback.base p)
      (card_base_fiber f g hf hg), Nat.cast_mul,
    Real.log_mul (by exact_mod_cast Fintype.card_pos.ne' :
        (Fintype.card D : ℝ) ≠ 0)
      (by exact_mod_cast (Nat.mul_pos hm hm').ne' : ((m * m' : ℕ) : ℝ) ≠ 0)]
  ring

end FinDist

/-! ## Generic priced constructions (review #13)

The `FinDist` layer above carries the *distribution* semantics of the
gravity face; here the same three constructions are built at the level
of **sector actions**, so that gravity and time are priced by `log Z`
and expected energy, not only measured by entropy:

* `SectorAction.coarseGrain` — project the sector type along a map,
  summing Boltzmann weights over each fiber (`coarseWeight`); the
  coarse energy is the effective free energy measured from a modal
  sector. The partition function factorizes
  (`partFn_eq_coarseWeight_mul`) and the complexity decomposes
  (`complexity_eq_coarseGrain`).
* `SectorAction.uniformLift` — pull a finite action back along a
  constant-fiber map; the Gibbs law of the lift **is** the
  `FinDist.uniformLift` of the Gibbs law (`uniformLift_gibbsDist`).
* `SectorAction.coupling` — price the shared-base pullback; the Gibbs
  law of the coupling **is** the `FinDist.coupling` of the Gibbs law
  (`coupling_gibbsDist`).

The lift and coupling preserve every pulled-back observable's
expectation and variance (`uniformLift_gibbsExpect`,
`coupling_gibbsVariance`, …), and satisfy the **action-level gravity
identities** `Z_pair · Z_base = Z_lift · Z_lift` (`partFn_gravity`)
and `K(pair) + K(base) = K(lift) + K(lift)` (`complexity_gravity`). -/

namespace SectorAction

/-- The Gibbs distribution of a finite sector action, bundled as a
`FinDist` (review #13). -/
noncomputable def gibbsDist (A : SectorAction.{u}) [Fintype A.Λ] :
    FinDist A.Λ where
  mass := A.gibbsMass
  nonneg := A.gibbsMass_nonneg
  sum_one := by
    have h := A.tsum_gibbsMass_eq_one
    rwa [tsum_fintype] at h

@[simp] theorem gibbsDist_mass (A : SectorAction.{u}) [Fintype A.Λ] :
    A.gibbsDist.mass = A.gibbsMass := rfl

/-! ### Coarse-graining: fiber Boltzmann sums -/

/-- **The unnormalized coarse weight** (review #13): the Boltzmann sum
of a fiber of a projection — the total weight the fine action assigns
to a coarse sector. -/
noncomputable def coarseWeight (A : SectorAction.{u}) {B : Type u}
    (p : A.Λ → B) (b : B) : ℝ :=
  ∑' k : {k : A.Λ // p k = b}, A.weight k.val

/-- Fiber Boltzmann sums converge. -/
theorem summable_coarse (A : SectorAction.{u}) {B : Type u}
    (p : A.Λ → B) (b : B) :
    Summable (fun k : {k : A.Λ // p k = b} => A.weight k.val) :=
  A.summable.subtype _

/-- A coarse sector with a nonempty fiber carries positive weight. -/
theorem coarseWeight_pos (A : SectorAction.{u}) {B : Type u}
    {p : A.Λ → B} {b : B} (h : ∃ k, p k = b) :
    0 < A.coarseWeight p b := by
  obtain ⟨k₀, hk₀⟩ := h
  exact (A.summable_coarse p b).tsum_pos
    (fun k => A.weight_nonneg k.val) ⟨k₀, hk₀⟩ (A.weight_pos k₀)

/-- The coarse weights sum to the partition function — the fibers
partition the sector type. -/
theorem sum_coarseWeight (A : SectorAction.{u}) {B : Type u} [Fintype B]
    (p : A.Λ → B) : ∑ b, A.coarseWeight p b = A.partFn := by
  have hσ := (Equiv.summable_iff (Equiv.sigmaFiberEquiv p)).mpr A.summable
  calc ∑ b, A.coarseWeight p b
      = ∑' b : B, A.coarseWeight p b := (tsum_fintype _).symm
    _ = ∑' σ : Σ b : B, {k : A.Λ // p k = b}, A.weight σ.2.val :=
        hσ.tsum_sigma.symm
    _ = ∑' k : A.Λ, A.weight k := Equiv.tsum_eq (Equiv.sigmaFiberEquiv p) _

/-- **The effective free energy** of a coarse sector (review #13):
`F b = −log W b`. -/
noncomputable def coarseFreeEnergy (A : SectorAction.{u}) {B : Type u}
    (p : A.Λ → B) (b : B) : ℝ :=
  -Real.log (A.coarseWeight p b)

section CoarseGrain

variable (A : SectorAction.{u}) {B : Type u} [Fintype B] (p : A.Λ → B)
  (b₀ : B) (hpos : ∀ b, 0 < A.coarseWeight p b)
  (hmax : ∀ b, A.coarseWeight p b ≤ A.coarseWeight p b₀)

/-- **Coarse-graining a sector action** (review #13): project the
sector type along `p`, pricing each coarse sector by its fiber
Boltzmann sum. The energy is the effective free energy measured from
the modal sector `b₀` — nonnegative exactly because `b₀` is modal,
vanishing at `b₀`. -/
noncomputable def coarseGrain : SectorAction.{u} where
  Λ := B
  E b := Real.log (A.coarseWeight p b₀) - Real.log (A.coarseWeight p b)
  E_zero := ⟨b₀, sub_self _⟩
  E_nonneg b := sub_nonneg.mpr (Real.log_le_log (hpos b) (hmax b))
  summable := (hasSum_fintype _).summable

instance : Fintype (A.coarseGrain p b₀ hpos hmax).Λ :=
  inferInstanceAs (Fintype B)

/-- The coarse energy is the free-energy difference from the modal
sector: `E b = F b − F b₀` (review #13). -/
theorem coarseGrain_E (b : B) :
    (A.coarseGrain p b₀ hpos hmax).E b
      = A.coarseFreeEnergy p b - A.coarseFreeEnergy p b₀ := by
  show Real.log (A.coarseWeight p b₀) - Real.log (A.coarseWeight p b)
    = -Real.log (A.coarseWeight p b) - -Real.log (A.coarseWeight p b₀)
  ring

/-- The coarse Boltzmann weight is the fiber-weight ratio against the
modal fiber. -/
theorem coarseGrain_weight (b : B) :
    (A.coarseGrain p b₀ hpos hmax).weight b
      = A.coarseWeight p b / A.coarseWeight p b₀ := by
  show Real.exp (-(Real.log (A.coarseWeight p b₀)
      - Real.log (A.coarseWeight p b))) = _
  rw [neg_sub, Real.exp_sub, Real.exp_log (hpos b), Real.exp_log (hpos b₀)]

/-- The coarse partition function: `Z_coarse = Z / W b₀`. -/
theorem coarseGrain_partFn :
    (A.coarseGrain p b₀ hpos hmax).partFn
      = A.partFn / A.coarseWeight p b₀ := by
  show (∑' b : B, (A.coarseGrain p b₀ hpos hmax).weight b) = _
  rw [tsum_fintype,
    Finset.sum_congr rfl fun b _ => coarseGrain_weight A p b₀ hpos hmax b,
    ← Finset.sum_div, A.sum_coarseWeight p]

/-- **The partition function factorizes through a coarse-graining**
(review #13): `Z = W b₀ · Z_coarse`. -/
theorem partFn_eq_coarseWeight_mul :
    A.partFn
      = A.coarseWeight p b₀ * (A.coarseGrain p b₀ hpos hmax).partFn := by
  rw [coarseGrain_partFn A p b₀ hpos hmax]
  have h0 : A.coarseWeight p b₀ ≠ 0 := (hpos b₀).ne'
  field_simp

/-- **The complexity decomposition through a coarse-graining**
(review #13): `log Z = log W b₀ + K_coarse`. -/
theorem complexity_eq_coarseGrain :
    A.complexity
      = Real.log (A.coarseWeight p b₀)
        + (A.coarseGrain p b₀ hpos hmax).complexity := by
  show Real.log A.partFn
    = _ + Real.log (A.coarseGrain p b₀ hpos hmax).partFn
  rw [coarseGrain_partFn A p b₀ hpos hmax,
    Real.log_div (ne_of_gt A.partFn_pos) (ne_of_gt (hpos b₀))]
  ring

/-- **The coarse Gibbs mass is the fiber Gibbs mass** (review #13):
`μ_coarse b = W b / Z` — the pushforward of the fine Gibbs law. -/
theorem coarseGrain_gibbsMass (b : B) :
    (A.coarseGrain p b₀ hpos hmax).gibbsMass b
      = A.coarseWeight p b / A.partFn := by
  show (A.coarseGrain p b₀ hpos hmax).weight b
      / (A.coarseGrain p b₀ hpos hmax).partFn = _
  rw [coarseGrain_weight A p b₀ hpos hmax b,
    coarseGrain_partFn A p b₀ hpos hmax]
  have h0 : A.coarseWeight p b₀ ≠ 0 := (hpos b₀).ne'
  have hZ : A.partFn ≠ 0 := ne_of_gt A.partFn_pos
  field_simp

end CoarseGrain

/-! ### Identity and composition of coarse-grainings (review #14)

Coarse-graining is not a family of disconnected snapshots: the
identity projection changes nothing (`coarseWeight_id`,
`coarseGrain_id`), and coarse-graining a coarse-graining is the
coarse-graining along the composite — the modal normalizations
cancel (`coarseWeight_comp`, `coarseGrain_comp`). -/

/-- Coarse weights along the identity are the weights: the fiber is a
single sector. -/
theorem coarseWeight_id (A : SectorAction.{u}) (b : A.Λ) :
    A.coarseWeight (fun k => k) b = A.weight b := by
  have h : ∀ k : {k : A.Λ // k = b},
      k ≠ (⟨b, rfl⟩ : {k : A.Λ // k = b}) → A.weight k.val = 0 :=
    fun k hk => absurd (Subtype.ext k.prop) hk
  calc A.coarseWeight (fun k => k) b
      = ∑' k : {k : A.Λ // k = b}, A.weight k.val := rfl
    _ = A.weight b := tsum_eq_single _ h

private theorem mk_eq_mk {Λ : Type u} {E E' : Λ → ℝ}
    {h₁ : ∃ z, E z = 0} {h₂ : ∀ k, 0 ≤ E k}
    {h₃ : Summable fun k => Real.exp (-E k)}
    {h₁' : ∃ z, E' z = 0} {h₂' : ∀ k, 0 ≤ E' k}
    {h₃' : Summable fun k => Real.exp (-E' k)} (h : E = E') :
    SectorAction.mk Λ E h₁ h₂ h₃ = SectorAction.mk Λ E' h₁' h₂' h₃' := by
  subst h
  rfl

/-- **Coarse-graining along the identity is the identity**
(review #14): at any zero-energy ground sector as the modal choice,
the coarse action is the action itself. -/
theorem coarseGrain_id (A : SectorAction.{u}) [Fintype A.Λ] {z : A.Λ}
    (hz : A.E z = 0)
    (hpos : ∀ b, 0 < A.coarseWeight (fun k => k) b)
    (hmax : ∀ b, A.coarseWeight (fun k => k) b
      ≤ A.coarseWeight (fun k => k) z) :
    A.coarseGrain (fun k => k) z hpos hmax = A := by
  cases A with
  | mk Λ E hE₀ hEnn hsum =>
    refine mk_eq_mk ?_
    funext b
    rw [coarseWeight_id, coarseWeight_id]
    show Real.log (Real.exp (-E z)) - Real.log (Real.exp (-E b)) = E b
    rw [Real.log_exp, Real.log_exp, show E z = 0 from hz]
    ring

/-- The fiber of a composite projection, as a sigma of intermediate
fibers. -/
private def compFiberEquiv {α B C : Type u} (p : α → B) (p' : B → C)
    (c : C) :
    {k : α // p' (p k) = c}
      ≃ Σ b : {b : B // p' b = c}, {k : α // p k = b.val} where
  toFun k := ⟨⟨p k.val, k.prop⟩, ⟨k.val, rfl⟩⟩
  invFun σ := ⟨σ.2.val, by rw [σ.2.prop]; exact σ.1.prop⟩
  left_inv k := rfl
  right_inv σ := by
    obtain ⟨⟨b, hb⟩, k, hk⟩ := σ
    refine Sigma.ext (Subtype.ext hk) ?_
    exact (Subtype.heq_iff_coe_eq (fun k' => by
      show p k' = p k ↔ p k' = b
      rw [hk])).mpr rfl

/-- **Coarse weights compose** (review #14): the fiber of a composite
projection decomposes as the fibers over the intermediate fiber. -/
theorem coarseWeight_comp (A : SectorAction.{u}) {B C : Type u}
    (p : A.Λ → B) (p' : B → C) (c : C) :
    A.coarseWeight (fun k => p' (p k)) c
      = ∑' b : {b : B // p' b = c}, A.coarseWeight p b.val := by
  classical
  have hsum : Summable (fun σ : Σ b : {b : B // p' b = c},
      {k : A.Λ // p k = b.val} => A.weight σ.2.val) :=
    (Equiv.summable_iff (compFiberEquiv p p' c)).mp (A.summable.subtype _)
  calc A.coarseWeight (fun k => p' (p k)) c
      = ∑' k : {k : A.Λ // p' (p k) = c}, A.weight k.val := rfl
    _ = ∑' σ : Σ b : {b : B // p' b = c}, {k : A.Λ // p k = b.val},
          A.weight σ.2.val :=
        Equiv.tsum_eq (compFiberEquiv p p' c) (fun σ => A.weight σ.2.val)
    _ = ∑' b : {b : B // p' b = c},
          ∑' k : {k : A.Λ // p k = b.val}, A.weight k.val := hsum.tsum_sigma
    _ = ∑' b : {b : B // p' b = c}, A.coarseWeight p b.val := rfl

/-- The coarse action's own coarse weight: the composite coarse
weight over the modal fiber weight. -/
theorem coarseGrain_coarseWeight (A : SectorAction.{u}) {B C : Type u}
    [Fintype B] (p : A.Λ → B) (b₀ : B)
    (hpos : ∀ b, 0 < A.coarseWeight p b)
    (hmax : ∀ b, A.coarseWeight p b ≤ A.coarseWeight p b₀)
    (p' : B → C) (c : C) :
    (A.coarseGrain p b₀ hpos hmax).coarseWeight p' c
      = A.coarseWeight (fun k => p' (p k)) c / A.coarseWeight p b₀ := by
  calc (A.coarseGrain p b₀ hpos hmax).coarseWeight p' c
      = ∑' b : {b : B // p' b = c},
          (A.coarseGrain p b₀ hpos hmax).weight b.val := rfl
    _ = ∑' b : {b : B // p' b = c},
          A.coarseWeight p b.val / A.coarseWeight p b₀ :=
        tsum_congr fun b => coarseGrain_weight A p b₀ hpos hmax b.val
    _ = (∑' b : {b : B // p' b = c}, A.coarseWeight p b.val)
          / A.coarseWeight p b₀ := by rw [tsum_div_const]
    _ = A.coarseWeight (fun k => p' (p k)) c / A.coarseWeight p b₀ := by
        rw [coarseWeight_comp A p p' c]

/-- **Coarse-grainings compose** (review #14): coarse-graining a
coarse-graining is the coarse-graining along the composite — the
modal normalizations cancel out of the free-energy differences. -/
theorem coarseGrain_comp (A : SectorAction.{u}) {B C : Type u}
    [Fintype B] [Fintype C] (p : A.Λ → B) (p' : B → C) (b₀ : B) (c₀ : C)
    (hpos : ∀ b, 0 < A.coarseWeight p b)
    (hmax : ∀ b, A.coarseWeight p b ≤ A.coarseWeight p b₀)
    (hpos' : ∀ c, 0 < (A.coarseGrain p b₀ hpos hmax).coarseWeight p' c)
    (hmax' : ∀ c, (A.coarseGrain p b₀ hpos hmax).coarseWeight p' c
      ≤ (A.coarseGrain p b₀ hpos hmax).coarseWeight p' c₀)
    (hpos'' : ∀ c, 0 < A.coarseWeight (fun k => p' (p k)) c)
    (hmax'' : ∀ c, A.coarseWeight (fun k => p' (p k)) c
      ≤ A.coarseWeight (fun k => p' (p k)) c₀) :
    (A.coarseGrain p b₀ hpos hmax).coarseGrain p' c₀ hpos' hmax'
      = A.coarseGrain (fun k => p' (p k)) c₀ hpos'' hmax'' := by
  refine mk_eq_mk ?_
  funext c
  rw [coarseGrain_coarseWeight A p b₀ hpos hmax p' c₀,
    coarseGrain_coarseWeight A p b₀ hpos hmax p' c,
    Real.log_div (hpos'' c₀).ne' (hpos b₀).ne',
    Real.log_div (hpos'' c).ne' (hpos b₀).ne']
  ring

/-! ### The priced uniform lift -/

section UniformLift

variable (A : SectorAction.{u}) [Fintype A.Λ] {X : Type u} [Fintype X]
  (f : X → A.Λ) {m : ℕ} (hm : 0 < m)
  (hfib : ∀ d, Nat.card {x : X // f x = d} = m)

/-- **The priced uniform lift** (review #13): pull a finite sector
action back along a constant-fiber map. Energy is pulled back
unchanged — each fine sector prices exactly as its coarse image, so
each Boltzmann weight is copied `m` times across the fiber. -/
noncomputable def uniformLift : SectorAction.{u} where
  Λ := X
  E x := A.E (f x)
  E_zero := by
    obtain ⟨z, hz⟩ := A.E_zero
    have hcard : 0 < Nat.card {x : X // f x = z} := by
      rw [hfib z]; exact hm
    obtain ⟨⟨x₀, hx₀⟩⟩ := (Nat.card_pos_iff.mp hcard).1
    exact ⟨x₀, by rw [hx₀, hz]⟩
  E_nonneg x := A.E_nonneg (f x)
  summable := (hasSum_fintype _).summable

instance : Fintype (A.uniformLift f hm hfib).Λ :=
  inferInstanceAs (Fintype X)

/-- The lift's partition function: `Z_lift = m · Z`. -/
theorem uniformLift_partFn :
    (A.uniformLift f hm hfib).partFn = m * A.partFn := by
  classical
  show (∑' x : X, Real.exp (-A.E (f x))) = m * A.partFn
  rw [tsum_fintype,
    sum_comp_card_fiber f hfib (fun d => Real.exp (-A.E d))]
  show (m : ℝ) * ∑ d, Real.exp (-A.E d) = (m : ℝ) * A.partFn
  congr 1
  show ∑ d, Real.exp (-A.E d) = ∑' d, A.weight d
  rw [tsum_fintype]
  rfl

/-- The lift's complexity: `K_lift = log m + K`. -/
theorem uniformLift_complexity :
    (A.uniformLift f hm hfib).complexity = Real.log m + A.complexity := by
  show Real.log (A.uniformLift f hm hfib).partFn = _
  rw [uniformLift_partFn A f hm hfib,
    Real.log_mul (by exact_mod_cast hm.ne' : (m : ℝ) ≠ 0)
      (ne_of_gt A.partFn_pos)]
  rfl

/-- The lift's Gibbs mass: the base Gibbs mass split evenly across the
fiber. -/
theorem uniformLift_gibbsMass (x : X) :
    (A.uniformLift f hm hfib).gibbsMass x = A.gibbsMass (f x) / m := by
  show (A.uniformLift f hm hfib).weight x
      / (A.uniformLift f hm hfib).partFn = _
  rw [uniformLift_partFn A f hm hfib]
  show A.weight (f x) / ((m : ℝ) * A.partFn) = _
  rw [mul_comm, ← div_div]
  rfl

/-- **The lift's Gibbs distribution is the `FinDist` uniform lift of
the base's** (review #13). -/
theorem uniformLift_gibbsDist [DecidableEq A.Λ] :
    (A.uniformLift f hm hfib).gibbsDist
      = A.gibbsDist.uniformLift f hm hfib := by
  refine FinDist.ext ?_
  funext x
  show (A.uniformLift f hm hfib).gibbsMass x = A.gibbsMass (f x) / m
  exact uniformLift_gibbsMass A f hm hfib x

/-- **Pulled-back observables keep their expectation through the
lift** (review #13). -/
theorem uniformLift_gibbsExpect (φ : A.Λ → ℝ) :
    (A.uniformLift f hm hfib).gibbsExpect (fun x => φ (f x))
      = A.gibbsExpect φ := by
  classical
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  show (∑' x : X, φ (f x) * (A.uniformLift f hm hfib).gibbsMass x)
    = ∑' d, φ d * A.gibbsMass d
  rw [tsum_fintype, tsum_fintype,
    Finset.sum_congr rfl fun x _ => by
      rw [uniformLift_gibbsMass A f hm hfib x],
    sum_comp_card_fiber f hfib (fun d => φ d * (A.gibbsMass d / m)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  field_simp

/-- **Pulled-back observables keep their variance through the lift**
(review #13). -/
theorem uniformLift_gibbsVariance (φ : A.Λ → ℝ) :
    (A.uniformLift f hm hfib).gibbsVariance (fun x => φ (f x))
      = A.gibbsVariance φ := by
  show (A.uniformLift f hm hfib).gibbsExpect (fun x => φ (f x) ^ 2)
      - (A.uniformLift f hm hfib).gibbsExpect (fun x => φ (f x)) ^ 2
    = A.gibbsExpect (fun d => φ d ^ 2) - A.gibbsExpect φ ^ 2
  rw [uniformLift_gibbsExpect A f hm hfib φ,
    uniformLift_gibbsExpect A f hm hfib (fun d => φ d ^ 2)]

/-- The lift's expected energy is the base's (review #13). -/
theorem uniformLift_gibbsExpect_E :
    (A.uniformLift f hm hfib).gibbsExpect (A.uniformLift f hm hfib).E
      = A.gibbsExpect A.E :=
  uniformLift_gibbsExpect A f hm hfib A.E

/-- The lift's energy variance is the base's (review #13). -/
theorem uniformLift_gibbsVariance_E :
    (A.uniformLift f hm hfib).gibbsVariance (A.uniformLift f hm hfib).E
      = A.gibbsVariance A.E :=
  uniformLift_gibbsVariance A f hm hfib A.E

/-- **TIME, GENERIC AND PRICED** (review #14): for a constant-fiber
map into a finite sector action's sector type, the normalized section
cost is exactly the complexity increment of the priced uniform lift —
`sectionCost f / |Λ| = K(uniformLift) − K(base)`. The section count
is the theorem (`sectionCost_eq_fiberInfoCost`); the increment is
`log m` (`uniformLift_complexity`). -/
theorem sectionCost_uniformLift :
    sectionCost f / Fintype.card A.Λ
      = (A.uniformLift f hm hfib).complexity - A.complexity := by
  classical
  have hsurj : Function.Surjective f := by
    intro d
    have hpos : 0 < Nat.card {x : X // f x = d} := by
      rw [hfib d]; exact hm
    obtain ⟨⟨x, hx⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨x, hx⟩
  have hcost : sectionCost f = Fintype.card A.Λ * Real.log m := by
    rw [sectionCost_eq_fiberInfoCost hsurj]
    unfold fiberInfoCost
    rw [Finset.sum_congr rfl fun b _ => by
      rw [show (Nat.card (f ⁻¹' {b}) : ℕ) = m from hfib b]]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (0 : ℝ) < Fintype.card A.Λ := by
    have : Nonempty A.Λ := ⟨A.E_zero.choose⟩
    exact_mod_cast Fintype.card_pos
  rw [hcost, uniformLift_complexity A f hm hfib,
    mul_div_cancel_left₀ _ hcard.ne']
  ring

end UniformLift

/-! ### The priced shared-base coupling -/

section Coupling

variable (A : SectorAction.{u}) [Fintype A.Λ] {X Y : Type u} [Fintype X]
  [Fintype Y] (f : X → A.Λ) (g : Y → A.Λ) [Fintype (SGD.Pullback f g)]
  {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m')
  (hf : ∀ d, Nat.card {x : X // f x = d} = m)
  (hg : ∀ d, Nat.card {y : Y // g y = d} = m')

/-- **The priced shared-base coupling** (review #13): price the
pullback of two constant-fiber maps by the base energy at the shared
image. -/
noncomputable def coupling : SectorAction.{u} where
  Λ := SGD.Pullback f g
  E p := A.E (SGD.Pullback.base p)
  E_zero := by
    obtain ⟨z, hz⟩ := A.E_zero
    have hcf : 0 < Nat.card {x : X // f x = z} := by rw [hf z]; exact hm
    have hcg : 0 < Nat.card {y : Y // g y = z} := by rw [hg z]; exact hm'
    obtain ⟨⟨x₀, hx₀⟩⟩ := (Nat.card_pos_iff.mp hcf).1
    obtain ⟨⟨y₀, hy₀⟩⟩ := (Nat.card_pos_iff.mp hcg).1
    refine ⟨⟨(x₀, y₀), hx₀.trans hy₀.symm⟩, ?_⟩
    show A.E (f x₀) = 0
    rw [hx₀, hz]
  E_nonneg p := A.E_nonneg _
  summable := (hasSum_fintype _).summable

instance : Fintype (A.coupling f g hm hm' hf hg).Λ :=
  inferInstanceAs (Fintype (SGD.Pullback f g))

omit [Fintype X] [Fintype Y] in
/-- The coupling's partition function: `Z_pair = m·m' · Z`. -/
theorem coupling_partFn :
    (A.coupling f g hm hm' hf hg).partFn
      = ((m * m' : ℕ) : ℝ) * A.partFn := by
  classical
  show (∑' p : SGD.Pullback f g, Real.exp (-A.E (SGD.Pullback.base p))) = _
  rw [tsum_fintype,
    sum_comp_card_fiber (fun p : SGD.Pullback f g => SGD.Pullback.base p)
      (FinDist.card_base_fiber f g hf hg) (fun d => Real.exp (-A.E d))]
  show ((m * m' : ℕ) : ℝ) * ∑ d, Real.exp (-A.E d) = _
  congr 1
  show ∑ d, Real.exp (-A.E d) = ∑' d, A.weight d
  rw [tsum_fintype]
  rfl

omit [Fintype X] [Fintype Y] in
/-- The coupling's complexity: `K_pair = log m + log m' + K`. -/
theorem coupling_complexity :
    (A.coupling f g hm hm' hf hg).complexity
      = Real.log m + Real.log m' + A.complexity := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hm'0 : (m' : ℝ) ≠ 0 := by exact_mod_cast hm'.ne'
  show Real.log (A.coupling f g hm hm' hf hg).partFn = _
  rw [coupling_partFn A f g hm hm' hf hg, Nat.cast_mul,
    Real.log_mul (mul_ne_zero hm0 hm'0) (ne_of_gt A.partFn_pos),
    Real.log_mul hm0 hm'0]
  rfl

omit [Fintype X] [Fintype Y] in
/-- The coupling's Gibbs mass: the base Gibbs mass split evenly across
the `m·m'` pairs above it. -/
theorem coupling_gibbsMass (p : SGD.Pullback f g) :
    (A.coupling f g hm hm' hf hg).gibbsMass p
      = A.gibbsMass (SGD.Pullback.base p) / ((m * m' : ℕ) : ℝ) := by
  show (A.coupling f g hm hm' hf hg).weight p
      / (A.coupling f g hm hm' hf hg).partFn = _
  rw [coupling_partFn A f g hm hm' hf hg]
  show A.weight (SGD.Pullback.base p) / (((m * m' : ℕ) : ℝ) * A.partFn) = _
  rw [mul_comm, ← div_div]
  rfl

omit [Fintype X] [Fintype Y] in
/-- **The coupling's Gibbs distribution is the `FinDist` shared-base
coupling of the base's** (review #13). -/
theorem coupling_gibbsDist [DecidableEq A.Λ] :
    (A.coupling f g hm hm' hf hg).gibbsDist
      = A.gibbsDist.coupling f g hm hm' hf hg := by
  refine FinDist.ext ?_
  funext p
  show (A.coupling f g hm hm' hf hg).gibbsMass p
    = A.gibbsMass (SGD.Pullback.base p) / ((m * m' : ℕ) : ℝ)
  exact coupling_gibbsMass A f g hm hm' hf hg p

omit [Fintype X] [Fintype Y] in
/-- **Pulled-back observables keep their expectation through the
coupling** (review #13). -/
theorem coupling_gibbsExpect (φ : A.Λ → ℝ) :
    (A.coupling f g hm hm' hf hg).gibbsExpect
        (fun p => φ (SGD.Pullback.base p))
      = A.gibbsExpect φ := by
  classical
  have hmm : ((m * m' : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos hm hm').ne'
  show (∑' p : SGD.Pullback f g,
      φ (SGD.Pullback.base p) * (A.coupling f g hm hm' hf hg).gibbsMass p)
    = ∑' d, φ d * A.gibbsMass d
  rw [tsum_fintype, tsum_fintype,
    Finset.sum_congr rfl fun p _ => by
      rw [coupling_gibbsMass A f g hm hm' hf hg p],
    sum_comp_card_fiber (fun p : SGD.Pullback f g => SGD.Pullback.base p)
      (FinDist.card_base_fiber f g hf hg)
      (fun d => φ d * (A.gibbsMass d / ((m * m' : ℕ) : ℝ))),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  field_simp

omit [Fintype X] [Fintype Y] in
/-- **Pulled-back observables keep their variance through the
coupling** (review #13). -/
theorem coupling_gibbsVariance (φ : A.Λ → ℝ) :
    (A.coupling f g hm hm' hf hg).gibbsVariance
        (fun p => φ (SGD.Pullback.base p))
      = A.gibbsVariance φ := by
  show (A.coupling f g hm hm' hf hg).gibbsExpect
        (fun p => φ (SGD.Pullback.base p) ^ 2)
      - (A.coupling f g hm hm' hf hg).gibbsExpect
          (fun p => φ (SGD.Pullback.base p)) ^ 2
    = A.gibbsExpect (fun d => φ d ^ 2) - A.gibbsExpect φ ^ 2
  rw [coupling_gibbsExpect A f g hm hm' hf hg φ,
    coupling_gibbsExpect A f g hm hm' hf hg (fun d => φ d ^ 2)]

omit [Fintype X] [Fintype Y] in
/-- The coupling's expected energy is the base's (review #13). -/
theorem coupling_gibbsExpect_E :
    (A.coupling f g hm hm' hf hg).gibbsExpect
        (A.coupling f g hm hm' hf hg).E
      = A.gibbsExpect A.E :=
  coupling_gibbsExpect A f g hm hm' hf hg A.E

omit [Fintype X] [Fintype Y] in
/-- The coupling's energy variance is the base's (review #13). -/
theorem coupling_gibbsVariance_E :
    (A.coupling f g hm hm' hf hg).gibbsVariance
        (A.coupling f g hm hm' hf hg).E
      = A.gibbsVariance A.E :=
  coupling_gibbsVariance A f g hm hm' hf hg A.E

/-- **The action-level partition-function gravity identity**
(review #13): `Z_pair · Z_base = Z_lift · Z_lift`. -/
theorem partFn_gravity :
    (A.coupling f g hm hm' hf hg).partFn * A.partFn
      = (A.uniformLift f hm hf).partFn
        * (A.uniformLift g hm' hg).partFn := by
  rw [coupling_partFn A f g hm hm' hf hg, uniformLift_partFn A f hm hf,
    uniformLift_partFn A g hm' hg]
  push_cast
  ring

/-- **The action-level complexity gravity identity** (review #13):
`K(coupling) + K(base) = K(lift) + K(lift)` — the entropy gravity
identity's priced sibling, at the level of `log Z`. -/
theorem complexity_gravity :
    (A.coupling f g hm hm' hf hg).complexity + A.complexity
      = (A.uniformLift f hm hf).complexity
        + (A.uniformLift g hm' hg).complexity := by
  rw [coupling_complexity A f g hm hm' hf hg,
    uniformLift_complexity A f hm hf, uniformLift_complexity A g hm' hg]
  ring

/-- **THE PRICED ENTROPY GRAVITY IDENTITY** (review #14): the
four-term entropy identity of the Gibbs laws, derived from the four
Gibbs entropy splits `H = K + ⟨E⟩`, the complexity gravity identity,
and the expectation transports — entropy gravity is a corollary of
the priced calculus, not a parallel theorem. -/
theorem entropy_gravity :
    shannonEntropy (A.coupling f g hm hm' hf hg).gibbsMass
      + shannonEntropy A.gibbsMass
    = shannonEntropy (A.uniformLift f hm hf).gibbsMass
      + shannonEntropy (A.uniformLift g hm' hg).gibbsMass := by
  rw [SectorAction.entropy_gibbs, SectorAction.entropy_gibbs,
    SectorAction.entropy_gibbs, SectorAction.entropy_gibbs,
    coupling_gibbsExpect_E A f g hm hm' hf hg,
    uniformLift_gibbsExpect_E A f hm hf,
    uniformLift_gibbsExpect_E A g hm' hg]
  have h := complexity_gravity A f g hm hm' hf hg
  linarith

end Coupling

end SectorAction

end Meno
