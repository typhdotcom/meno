import Meno.Basic
import Meno.SectorAction
import Meno.UniformAction
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
`recoveryCostE` prices them at `⊤`. -/
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
not free, it is impossible. `sectionCostE` below is the
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
non-surjective `f` has *no* section, and its extended cost is
`⊤` (`sectionCostE_eq_top_iff`). Zero extended cost characterizes
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
exactly the log of the fiber size. The carrier
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

/-! ### The fiber-count observable (G2) -/

/-- **The fiber-count observable** (G2): the number of states a
description map places over each base point, as a real observable —
the redundancy profile of the description. -/
noncomputable def fiberCount {X D : Type u} (f : X → D) : D → ℝ :=
  fun d => (Nat.card {x : X // f x = d} : ℝ)

/-- Surjectivity from a finite type puts at least one state over
every base point. -/
theorem one_le_fiberCount {X D : Type u} [Finite X] {f : X → D}
    (hf : Function.Surjective f) (d : D) : 1 ≤ fiberCount f d := by
  obtain ⟨x, hx⟩ := hf d
  have hpos : 0 < Nat.card {x : X // f x = d} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨x, hx⟩⟩, inferInstance⟩
  show (1 : ℝ) ≤ (Nat.card {x : X // f x = d} : ℝ)
  exact_mod_cast hpos

/-- Summing a composite through a map groups by fibers — the general,
non-uniform form of `sum_comp_card_fiber`. -/
theorem sum_comp_fiberCount {X D : Type u} [Fintype X] [Fintype D]
    [DecidableEq D] (f : X → D) (g : D → ℝ) :
    ∑ x, g (f x) = ∑ d, fiberCount f d * g d := by
  rw [← Finset.sum_fiberwise' Finset.univ f g]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_const]
  have hcard : (Finset.univ.filter fun x : X => f x = d).card
      = Nat.card {x : X // f x = d} := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  rw [hcard, nsmul_eq_mul]
  rfl

/-- **The pullback's base-fiber count is the product of the two fiber
counts** — no constancy hypothesis (the counting engine of the
unconditioned coupling, through `SGD.Pullback.baseFiberEquiv`). -/
theorem fiberCount_pullback_base {X Y D : Type u} (f : X → D) (g : Y → D)
    (d : D) :
    fiberCount (fun p : SGD.Pullback f g => SGD.Pullback.base p) d
      = fiberCount f d * fiberCount g d := by
  show (Nat.card {p : SGD.Pullback f g // SGD.Pullback.base p = d} : ℝ) = _
  rw [Nat.card_congr (SGD.Pullback.baseFiberEquiv f g d), Nat.card_prod]
  push_cast
  rfl

/-- **The counted cost, exact and non-uniform** (G5): a surjection's
reverse-description cost is the sum of the log fiber counts — the
coding theorem (`sectionCost_eq_fiberInfoCost`) read through the
redundancy profile. -/
theorem sectionCost_eq_sum_log_fiberCount {X D : Type u} [Fintype X]
    [Fintype D] [DecidableEq D] {f : X → D}
    (hf : Function.Surjective f) :
    sectionCost f = ∑ d, Real.log (fiberCount f d) := by
  rw [sectionCost_eq_fiberInfoCost hf]
  rfl

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
(`map_uniformLift`) and both coupling marginals (`coupling_fst`,
`coupling_snd`) are proved once, here. The entropy face of gravity
flows through the one engine — `SectorAction.entropy_gravity`, below
(review #22: the parallel distribution-level identity is deleted).
The graph instantiations — the Gibbs residue distribution and the
uniform distribution — live in `Meno/ResolutionCount.lean`. -/

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

/-- Weighted regrouping along a map: summing `mass · φ ∘ f` over the
domain is summing `pushforward-mass · φ` over the codomain. -/
private lemma sum_mass_mul_comp [DecidableEq D] (f : X → D) (P : FinDist X)
    (φ : D → ℝ) :
    ∑ x, P.mass x * φ (f x) = ∑ d, (P.map f).mass d * φ d := by
  rw [← Finset.sum_fiberwise Finset.univ f (fun x => P.mass x * φ (f x))]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_congr rfl (fun x hx => by
      rw [(Finset.mem_filter.mp hx).2]),
    ← Finset.sum_mul]
  rfl

/-- Each mass is at most its fiber's pushforward mass. -/
theorem mass_le_map [DecidableEq D] (f : X → D) (P : FinDist X) (x : X) :
    P.mass x ≤ (P.map f).mass (f x) :=
  Finset.single_le_sum (fun y _ => P.nonneg y)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩)

/-- **Pushforward along the identity is the identity** (review #17). -/
theorem map_id [DecidableEq X] (P : FinDist X) : P.map id = P := by
  apply ext
  funext x
  show ∑ y ∈ Finset.univ.filter (fun y => id y = x), P.mass y = P.mass x
  simp only [id_eq]
  rw [Finset.filter_eq', if_pos (Finset.mem_univ x), Finset.sum_singleton]

/-- **Pushforward composes** (review #17): the two-step pushforward is
the pushforward along the composite. -/
theorem map_comp {E : Type u} [Fintype E] [DecidableEq D] [DecidableEq E]
    (f : X → D) (g : D → E) (P : FinDist X) :
    P.map (g ∘ f) = (P.map f).map g := by
  apply ext
  funext e
  show ∑ x ∈ Finset.univ.filter (fun x => g (f x) = e), P.mass x
    = ∑ d ∈ Finset.univ.filter (fun d => g d = e), (P.map f).mass d
  rw [Finset.sum_filter, Finset.sum_filter]
  calc (∑ x, if g (f x) = e then P.mass x else 0)
      = ∑ x, P.mass x * (if g (f x) = e then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : g (f x) = e
        · rw [if_pos hx, if_pos hx, mul_one]
        · rw [if_neg hx, if_neg hx, mul_zero]
    _ = ∑ d, (P.map f).mass d * (if g d = e then (1 : ℝ) else 0) :=
        sum_mass_mul_comp f P (fun d => if g d = e then (1 : ℝ) else 0)
    _ = ∑ d, if g d = e then (P.map f).mass d else 0 := by
        refine Finset.sum_congr rfl fun d _ => ?_
        by_cases hd : g d = e
        · rw [if_pos hd, if_pos hd, mul_one]
        · rw [if_neg hd, if_neg hd, mul_zero]

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

/-! #### Full support and the relative entropy (reviews #17, #18)

`D(P ‖ Q) = ∑ₓ p(x)·log(p(x)/q(x))` is meaningful only against a
fully supported reference — with a vanishing reference mass, Lean's
totalized division and `Real.log 0 = 0` would silently zero the
divergent term, making mutually singular distributions "agree". So
the definition **requires the support proof**
(`FinDist.FullSupport`): the invalid expression is unstatable
(review #18). The Gibbs inequality (`relativeEntropy_nonneg`, strict
form `relativeEntropy_pos`, characterization
`relativeEntropy_eq_zero_iff`) is proved **once**, here; the uniform
entropy defect is the special case `Q = uniform`
(`defect_eq_relativeEntropy`), the conditional-entropy gap along a
constant-fiber map is the special case `Q = fiber-uniformization`
(`relativeEntropy_uniformLift_map`, below), and pushforward can only
lose relative entropy (`relativeEntropy_map_le` — data processing,
below). -/

/-- **Full support**: every mass is strictly positive. The
admissibility certificate for relative-entropy references
(review #18). -/
def FullSupport (P : FinDist X) : Prop := ∀ x, 0 < P.mass x

/-- The uniform distribution is fully supported. -/
theorem uniform_fullSupport (X : Type u) [Fintype X] [Nonempty X] :
    (uniform X).FullSupport := fun _ =>
  inv_pos.mpr (by exact_mod_cast Fintype.card_pos)

/-- **Pushforward along a surjection preserves full support**: every
fiber is nonempty, so every pushforward mass bounds a positive mass
below. -/
theorem FullSupport.map [DecidableEq D] {P : FinDist X}
    (hP : P.FullSupport) (f : X → D) (hf : Function.Surjective f) :
    (P.map f).FullSupport := by
  intro d
  obtain ⟨x, hx⟩ := hf d
  refine Finset.sum_pos' (fun y _ => P.nonneg y) ⟨x, ?_, hP x⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩

/-- The fiber-uniformization of the pushforward of a fully supported
distribution is fully supported. -/
theorem FullSupport.uniformLiftMap [DecidableEq D] {P : FinDist X}
    (hP : P.FullSupport) (f : X → D) {m : ℕ} (hm : 0 < m)
    (hfib : ∀ d, Nat.card {x : X // f x = d} = m) :
    (((P.map f)).uniformLift f hm hfib).FullSupport := by
  intro x
  have hmap : 0 < (P.map f).mass (f x) :=
    lt_of_lt_of_le (hP x) (mass_le_map f P x)
  show 0 < (P.map f).mass (f x) / m
  positivity

/-- Total mass one forces a positive mass. -/
theorem exists_mass_pos (P : FinDist X) : ∃ x, 0 < P.mass x := by
  by_contra hall
  push_neg at hall
  have hzero : ∀ x, P.mass x = 0 := fun x =>
    le_antisymm (hall x) (P.nonneg x)
  have h1 := P.sum_one
  rw [Finset.sum_congr rfl fun x _ => hzero x,
    Finset.sum_const_zero] at h1
  exact one_ne_zero h1.symm

/-- The tilt normalizer is positive — no support hypothesis:
`exists_mass_pos` supplies a positive term. -/
theorem tilt_norm_pos (P : FinDist X) (φ : X → ℝ) :
    0 < ∑ y, Real.exp (φ y) * P.mass y := by
  obtain ⟨x, hx⟩ := P.exists_mass_pos
  exact Finset.sum_pos'
    (fun y _ => mul_nonneg (Real.exp_pos _).le (P.nonneg y))
    ⟨x, Finset.mem_univ x, mul_pos (Real.exp_pos _) hx⟩

/-- **The tilted distribution** (G9): reweight `P` by `exp (φ x)`
and renormalize. Normalizable with no support hypothesis
(`tilt_norm_pos`). -/
noncomputable def tilt (P : FinDist X) (φ : X → ℝ) : FinDist X where
  mass x := Real.exp (φ x) * P.mass x / ∑ y, Real.exp (φ y) * P.mass y
  nonneg x := div_nonneg
    (mul_nonneg (Real.exp_pos _).le (P.nonneg x))
    (P.tilt_norm_pos φ).le
  sum_one := by
    rw [← Finset.sum_div, div_self (P.tilt_norm_pos φ).ne']

/-- **Tilting preserves full support** (G9). -/
theorem FullSupport.tilt {P : FinDist X} (hP : P.FullSupport)
    (φ : X → ℝ) : (P.tilt φ).FullSupport := fun x =>
  div_pos (mul_pos (Real.exp_pos _) (hP x)) (P.tilt_norm_pos φ)

/-- **The relative entropy** of `P` against a fully supported
reference `Q` — the support proof is part of the definition
(review #18), so the expression cannot be formed against an invalid
reference. -/
noncomputable def relativeEntropy (P Q : FinDist X)
    (_ : Q.FullSupport) : ℝ :=
  ∑ x, P.mass x * Real.log (P.mass x / Q.mass x)

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

/-- **The Gibbs inequality** (reviews #16, #17): the relative entropy
of a distribution against a fully supported reference is
nonnegative. -/
theorem relativeEntropy_nonneg (P Q : FinDist X)
    (hQ : Q.FullSupport) :
    0 ≤ P.relativeEntropy Q hQ := by
  show (0 : ℝ) ≤ ∑ x, P.mass x * Real.log (P.mass x / Q.mass x)
  calc (0 : ℝ) = ∑ x, (P.mass x - Q.mass x) := by
        rw [Finset.sum_sub_distrib, P.sum_one, Q.sum_one]
        ring
    _ ≤ ∑ x, P.mass x * Real.log (P.mass x / Q.mass x) :=
        Finset.sum_le_sum fun x _ => gibbs_term_le P Q hQ x

/-- **The strict Gibbs inequality** (reviews #16, #17): distinct
distributions have strictly positive relative entropy. -/
theorem relativeEntropy_pos (P Q : FinDist X) (hQ : Q.FullSupport)
    (hne : P ≠ Q) :
    0 < P.relativeEntropy Q hQ := by
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
  show (0 : ℝ) < ∑ x, P.mass x * Real.log (P.mass x / Q.mass x)
  calc (0 : ℝ) = ∑ x, (P.mass x - Q.mass x) := by
        rw [Finset.sum_sub_distrib, P.sum_one, Q.sum_one]
        ring
    _ < ∑ x, P.mass x * Real.log (P.mass x / Q.mass x) :=
        Finset.sum_lt_sum (fun x _ => gibbs_term_le P Q hQ x)
          ⟨x₀, Finset.mem_univ x₀, hstrict⟩

/-- **Zero relative entropy characterizes equality** (review #17). -/
theorem relativeEntropy_eq_zero_iff (P Q : FinDist X)
    (hQ : Q.FullSupport) :
    P.relativeEntropy Q hQ = 0 ↔ P = Q := by
  constructor
  · intro h0
    by_contra hne
    exact (relativeEntropy_pos P Q hQ hne).ne' h0
  · rintro rfl
    show ∑ x, P.mass x * Real.log (P.mass x / P.mass x) = 0
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [div_self (hQ x).ne', Real.log_one, mul_zero]

/-- **The defect is a relative entropy** (review #17): the uniform
entropy defect is exactly the relative entropy against the uniform
distribution — `Δ(P) = D(P ‖ uniform)`. -/
theorem defect_eq_relativeEntropy [Nonempty X] (P : FinDist X) :
    P.defect = P.relativeEntropy (uniform X) (uniform_fullSupport X) := by
  have hN : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ x, P.mass x * Real.log (P.mass x / (uniform X).mass x)
      = P.mass x * Real.log (P.mass x)
        + P.mass x * Real.log (Fintype.card X) := by
    intro x
    show P.mass x * Real.log (P.mass x / (Fintype.card X : ℝ)⁻¹) = _
    rw [div_inv_eq_mul]
    rcases eq_or_lt_of_le (P.nonneg x) with h0 | hpos
    · rw [← h0]
      simp
    · rw [Real.log_mul hpos.ne' hN.ne']
      ring
  show Real.log (Fintype.card X) - shannonEntropy P.mass
    = ∑ x, P.mass x * Real.log (P.mass x / (uniform X).mass x)
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_add_distrib,
    ← Finset.sum_mul, P.sum_one, one_mul, shannonEntropy]
  ring

/-- **The maximum entropy theorem**: the defect is nonnegative —
`H(P) ≤ log|X|`. A special case of the Gibbs inequality
(review #17). -/
theorem defect_nonneg [Nonempty X] (P : FinDist X) : 0 ≤ P.defect := by
  rw [P.defect_eq_relativeEntropy]
  exact relativeEntropy_nonneg P (uniform X) (uniform_fullSupport X)

/-- **Zero defect characterizes the uniform distribution.** A special
case of `relativeEntropy_eq_zero_iff` (review #17). -/
theorem defect_eq_zero_iff [Nonempty X] (P : FinDist X) :
    P.defect = 0 ↔ P = uniform X := by
  rw [P.defect_eq_relativeEntropy]
  exact relativeEntropy_eq_zero_iff P (uniform X) (uniform_fullSupport X)

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

/-- **THE ENTROPY CHAIN RULE** (reviews #15, #18):
`H(P) = H(f_*P) + H(P | f)` — **unconditionally**: zero-mass sectors
drop from every term, and a zero-mass fiber has only zero-mass
members. The single chain-rule engine; the conditional identity and
composition laws are corollaries. -/
theorem entropy_eq_map_add_condEntropy [DecidableEq D] (f : X → D)
    (P : FinDist X) :
    P.entropy = (P.map f).entropy + P.condEntropy f := by
  have hterm : ∀ x, P.mass x * Real.log (P.mass x / (P.map f).mass (f x))
      = P.mass x * Real.log (P.mass x)
        - P.mass x * Real.log ((P.map f).mass (f x)) := by
    intro x
    rcases eq_or_lt_of_le (P.nonneg x) with h0 | hp
    · rw [← h0, zero_mul, zero_mul, zero_mul, sub_zero]
    · have hF : 0 < (P.map f).mass (f x) :=
        lt_of_lt_of_le hp (mass_le_map f P x)
      rw [Real.log_div hp.ne' hF.ne']
      ring
  have hgroup : ∑ x, P.mass x * Real.log ((P.map f).mass (f x))
      = ∑ d, (P.map f).mass d * Real.log ((P.map f).mass d) :=
    sum_mass_mul_comp f P (fun d => Real.log ((P.map f).mass d))
  show -∑ x, P.mass x * Real.log (P.mass x)
    = (-∑ d, (P.map f).mass d * Real.log ((P.map f).mass d))
      + -∑ x, P.mass x * Real.log (P.mass x / (P.map f).mass (f x))
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_sub_distrib,
    ← hgroup]
  ring

/-- **Zero conditional entropy at the identity** (review #18): a
corollary of the chain rule and `map_id`. -/
theorem condEntropy_id [DecidableEq X] (P : FinDist X) :
    P.condEntropy id = 0 := by
  have h := entropy_eq_map_add_condEntropy id P
  rw [map_id] at h
  linarith

/-- **The conditional-entropy chain rule along a composition**
(reviews #17, #18): `H(P | g ∘ f) = H(P | f) + H(f_*P | g)` — a
corollary of the unconditional entropy chain rule and `map_comp`,
not a second termwise engine. -/
theorem condEntropy_comp {E : Type u} [Fintype E] [DecidableEq D]
    [DecidableEq E] (f : X → D) (g : D → E) (P : FinDist X) :
    P.condEntropy (g ∘ f)
      = P.condEntropy f + (P.map f).condEntropy g := by
  have h1 := entropy_eq_map_add_condEntropy (g ∘ f) P
  have h2 := entropy_eq_map_add_condEntropy f P
  have h3 := entropy_eq_map_add_condEntropy g (P.map f)
  rw [map_comp f g P] at h1
  linarith

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

/-- **The conditional-entropy gap is a relative entropy**
(review #17): along a constant-fiber map, the gap between the fiber
log and the conditional entropy is the relative entropy against the
fiber-uniformization of the pushforward —
`D(P ‖ (f_*P)↑) = log m − H(P | f)`. -/
theorem relativeEntropy_uniformLift_map [DecidableEq D] (f : X → D)
    {m : ℕ} (hm : 0 < m)
    (hfib : ∀ d, Nat.card {x : X // f x = d} = m) (P : FinDist X)
    (hpos : P.FullSupport) :
    P.relativeEntropy ((P.map f).uniformLift f hm hfib)
        (hpos.uniformLiftMap f hm hfib)
      = Real.log m - P.condEntropy f := by
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
    = Real.log m - P.condEntropy f
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_add_distrib,
    ← Finset.sum_mul, P.sum_one, one_mul,
    show P.condEntropy f
      = -∑ x, P.mass x * Real.log (P.mass x / (P.map f).mass (f x)) from rfl]
  ring

/-- **The constant-fiber upper bound** (review #16): the conditional
entropy of a fully supported distribution along a constant-fiber map
is at most the fiber log — with the gap the relative entropy against
the fiber-uniformized distribution. -/
theorem condEntropy_le_log [DecidableEq D] (f : X → D) {m : ℕ}
    (hm : 0 < m) (hfib : ∀ d, Nat.card {x : X // f x = d} = m)
    (P : FinDist X) (hpos : P.FullSupport) :
    P.condEntropy f ≤ Real.log m := by
  have h := relativeEntropy_nonneg P
    ((P.map f).uniformLift f hm hfib) (hpos.uniformLiftMap f hm hfib)
  rw [relativeEntropy_uniformLift_map f hm hfib P hpos] at h
  linarith

/-- **The strict constant-fiber bound** (review #16): strict unless
the distribution is its own fiber-uniformization. -/
theorem condEntropy_lt_log [DecidableEq D] (f : X → D) {m : ℕ}
    (hm : 0 < m) (hfib : ∀ d, Nat.card {x : X // f x = d} = m)
    (P : FinDist X) (hpos : P.FullSupport)
    (hne : P ≠ (P.map f).uniformLift f hm hfib) :
    P.condEntropy f < Real.log m := by
  have h := relativeEntropy_pos P
    ((P.map f).uniformLift f hm hfib) (hpos.uniformLiftMap f hm hfib) hne
  rw [relativeEntropy_uniformLift_map f hm hfib P hpos] at h
  linarith

/-- **DATA PROCESSING** (review #18): pushforward along a surjection
can only lose relative entropy — `D(f_*P ‖ f_*Q) ≤ D(P ‖ Q)`.
Termwise: for `p(x) > 0`,
`p·log(p/q) − p·log(F∘f/G∘f) ≥ p − q·(F∘f)/(G∘f)` by
`log t ≤ t − 1`, and both correction sums regroup to `1`. -/
theorem relativeEntropy_map_le [DecidableEq D] (f : X → D)
    (hf : Function.Surjective f) (P Q : FinDist X)
    (hQ : Q.FullSupport) :
    (P.map f).relativeEntropy (Q.map f) (hQ.map f hf)
      ≤ P.relativeEntropy Q hQ := by
  have hG : ∀ d, 0 < (Q.map f).mass d := hQ.map f hf
  have hkey : ∀ x,
      P.mass x - Q.mass x * ((P.map f).mass (f x) / (Q.map f).mass (f x))
        ≤ P.mass x * Real.log (P.mass x / Q.mass x)
          - P.mass x * Real.log ((P.map f).mass (f x)
              / (Q.map f).mass (f x)) := by
    intro x
    rcases eq_or_lt_of_le (P.nonneg x) with h0 | hp
    · rw [← h0, zero_mul, zero_mul, zero_sub, sub_zero]
      refine neg_nonpos.mpr (mul_nonneg (Q.nonneg x) ?_)
      exact div_nonneg ((P.map f).nonneg (f x)) (hG (f x)).le
    · have hqx := hQ x
      have hF : 0 < (P.map f).mass (f x) :=
        lt_of_lt_of_le hp (mass_le_map f P x)
      have hGf := hG (f x)
      have hlog := Real.log_le_sub_one_of_pos
        (show 0 < Q.mass x * (P.map f).mass (f x)
            / (P.mass x * (Q.map f).mass (f x)) from by positivity)
      have h2 : P.mass x * Real.log (Q.mass x * (P.map f).mass (f x)
          / (P.mass x * (Q.map f).mass (f x)))
          ≤ P.mass x * (Q.mass x * (P.map f).mass (f x)
              / (P.mass x * (Q.map f).mass (f x)) - 1) :=
        mul_le_mul_of_nonneg_left hlog hp.le
      have h3 : P.mass x * (Q.mass x * (P.map f).mass (f x)
          / (P.mass x * (Q.map f).mass (f x)) - 1)
          = Q.mass x * ((P.map f).mass (f x) / (Q.map f).mass (f x))
            - P.mass x := by
        field_simp
      have h4 : P.mass x * Real.log (P.mass x / Q.mass x)
          - P.mass x * Real.log ((P.map f).mass (f x)
              / (Q.map f).mass (f x))
          = -(P.mass x * Real.log (Q.mass x * (P.map f).mass (f x)
              / (P.mass x * (Q.map f).mass (f x)))) := by
        rw [Real.log_div hp.ne' hqx.ne', Real.log_div hF.ne' hGf.ne',
          Real.log_div (by positivity) (by positivity),
          Real.log_mul hqx.ne' hF.ne', Real.log_mul hp.ne' hGf.ne']
        ring
      linarith
  have hgroup1 : ∑ x, P.mass x
      * Real.log ((P.map f).mass (f x) / (Q.map f).mass (f x))
      = ∑ d, (P.map f).mass d
          * Real.log ((P.map f).mass d / (Q.map f).mass d) :=
    sum_mass_mul_comp f P
      (fun d => Real.log ((P.map f).mass d / (Q.map f).mass d))
  have hgroup2 : ∑ x, Q.mass x
      * ((P.map f).mass (f x) / (Q.map f).mass (f x))
      = ∑ d, (Q.map f).mass d * ((P.map f).mass d / (Q.map f).mass d) :=
    sum_mass_mul_comp f Q
      (fun d => (P.map f).mass d / (Q.map f).mass d)
  have hsum2 : ∑ d, (Q.map f).mass d
      * ((P.map f).mass d / (Q.map f).mass d) = 1 := by
    rw [Finset.sum_congr rfl fun d _ =>
      mul_div_cancel₀ ((P.map f).mass d) (hG d).ne']
    exact (P.map f).sum_one
  have hsum : (∑ x, (P.mass x
        - Q.mass x * ((P.map f).mass (f x) / (Q.map f).mass (f x))))
      ≤ ∑ x, (P.mass x * Real.log (P.mass x / Q.mass x)
          - P.mass x * Real.log ((P.map f).mass (f x)
              / (Q.map f).mass (f x))) :=
    Finset.sum_le_sum fun x _ => hkey x
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, P.sum_one,
    hgroup1, hgroup2, hsum2] at hsum
  show ∑ d, (P.map f).mass d
      * Real.log ((P.map f).mass d / (Q.map f).mass d)
    ≤ ∑ x, P.mass x * Real.log (P.mass x / Q.mass x)
  linarith

/-- **Pushforward can only lose defect** (review #18): data
processing at the uniform reference, given that the uniform
distribution pushes to the uniform distribution. -/
theorem defect_map_le [Nonempty X] [Nonempty D] [DecidableEq D]
    (f : X → D) (hf : Function.Surjective f)
    (huni : (uniform X).map f = uniform D) (P : FinDist X) :
    (P.map f).defect ≤ P.defect := by
  rw [defect_eq_relativeEntropy, defect_eq_relativeEntropy]
  have h := relativeEntropy_map_le f hf P (uniform X)
    (uniform_fullSupport X)
  calc (P.map f).relativeEntropy (uniform D) (uniform_fullSupport D)
      = (P.map f).relativeEntropy ((uniform X).map f)
          ((uniform_fullSupport X).map f hf) := by
        show (∑ d, (P.map f).mass d
            * Real.log ((P.map f).mass d / (uniform D).mass d))
          = ∑ d, (P.map f).mass d
              * Real.log ((P.map f).mass d / ((uniform X).map f).mass d)
        rw [huni]
    _ ≤ P.relativeEntropy (uniform X) (uniform_fullSupport X) := h

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

/-- The Gibbs distribution is fully supported (`gibbsMass_pos`). -/
theorem gibbsDist_fullSupport (A : SectorAction.{u}) [Fintype A.Λ] :
    A.gibbsDist.FullSupport := fun k => A.gibbsMass_pos k

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

/-! ### Covariance gravity: the priced lift and coupling, unconditioned (G2)

The gravity face without fiber hypotheses. `lift` pulls the energy of
a finite-sector action back along a surjective map from a finite type
— surjectivity is exactly what carries the zero-energy sector
upstairs; no constant-fiber assumption. `couple` prices the pullback
by the base. The complexity increments are log Gibbs-mean
redundancies (`lift_complexity`, `couple_complexity`), the four-term
gravity defect is the log-correlation of the two redundancy profiles
(`gravity_defect`), it vanishes exactly at zero covariance
(`gravity_defect_eq_zero_iff`) — the constant-fiber
`complexity_gravity` below is the zero-covariance chart — and
comonotone redundancy binds (`gravityDefect_nonneg_of_comonotone`),
through the double-sum covariance identity (`gibbsCov_double_sum`).
The strictness witness and the face's negative
(`twoSector_gravityDefect_pos`, `exists_gravity_defect_ne_zero`)
close the file. -/

section CovarianceGravity

variable (A : SectorAction.{u}) {X Y : Type u} [Fintype X] [Fintype Y]
  (f : X → A.Λ) (g : Y → A.Λ)

/-- **The Gibbs covariance** of two observables (G2): the correlation
of their profiles under the Gibbs law. Its diagonal is the standing
`gibbsVariance` (`gibbsCov_self`). -/
noncomputable def gibbsCov (φ ψ : A.Λ → ℝ) : ℝ :=
  A.gibbsExpect (φ * ψ) - A.gibbsExpect φ * A.gibbsExpect ψ

/-- The covariance diagonal is the variance. -/
theorem gibbsCov_self (φ : A.Λ → ℝ) :
    A.gibbsCov φ φ = A.gibbsVariance φ := by
  show A.gibbsExpect (φ * φ) - A.gibbsExpect φ * A.gibbsExpect φ
    = A.gibbsExpect (fun k => φ k ^ 2) - A.gibbsExpect φ ^ 2
  rw [show φ * φ = fun k => φ k ^ 2 from
      funext fun k => (pow_two (φ k)).symm,
    ← pow_two (A.gibbsExpect φ)]

/-- **The priced lift, unconditioned** (G2): pull the energy of a
sector action back along a surjective map from a finite type —
surjectivity carries the zero-energy sector upstairs; no
constant-fiber assumption. -/
noncomputable def lift (hf : Function.Surjective f) : SectorAction.{u} where
  Λ := X
  E x := A.E (f x)
  E_zero := by
    obtain ⟨z, hz⟩ := A.E_zero
    obtain ⟨x, hx⟩ := hf z
    exact ⟨x, by rw [hx, hz]⟩
  E_nonneg x := A.E_nonneg (f x)
  summable := (hasSum_fintype _).summable

instance (hf : Function.Surjective f) : Fintype (A.lift f hf).Λ :=
  inferInstanceAs (Fintype X)

/-- **The priced coupling, unconditioned** (G2): the pullback
`SGD.Pullback f g` priced by the base energy at the shared image. -/
noncomputable def couple [Fintype (SGD.Pullback f g)]
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    SectorAction.{u} where
  Λ := SGD.Pullback f g
  E p := A.E (SGD.Pullback.base p)
  E_zero := by
    obtain ⟨z, hz⟩ := A.E_zero
    obtain ⟨x, hx⟩ := hf z
    obtain ⟨y, hy⟩ := hg z
    refine ⟨⟨(x, y), hx.trans hy.symm⟩, ?_⟩
    show A.E (f x) = 0
    rw [hx, hz]
  E_nonneg p := A.E_nonneg _
  summable := (hasSum_fintype _).summable

/-- **The gravity defect** (G2): what coupling-then-base costs beyond
the two lifts — the four-term combination whose vanishing is the
constant-fiber gravity identity. -/
noncomputable def gravityDefect [Fintype (SGD.Pullback f g)]
    (hf : Function.Surjective f) (hg : Function.Surjective g) : ℝ :=
  ((A.couple f g hf hg).complexity + A.complexity)
    - ((A.lift f hf).complexity + (A.lift g hg).complexity)

/-! #### The finite-base expectation toolkit -/

variable [Fintype A.Λ]

/-- The Gibbs expectation over a finite sector type, as a finite
sum. -/
theorem gibbsExpect_eq_sum (φ : A.Λ → ℝ) :
    A.gibbsExpect φ = ∑ d, φ d * A.gibbsMass d := by
  show (∑' d, φ d * A.gibbsMass d) = ∑ d, φ d * A.gibbsMass d
  rw [tsum_fintype]

/-- The Gibbs masses over a finite sector type sum to one. -/
theorem sum_gibbsMass_eq_one : ∑ d, A.gibbsMass d = 1 := by
  have h := A.tsum_gibbsMass_eq_one
  rw [tsum_fintype] at h
  exact h

/-- Expectation of a constant is the constant — the Gibbs law is a
probability. -/
theorem gibbsExpect_const (c : ℝ) : A.gibbsExpect (fun _ => c) = c := by
  rw [gibbsExpect_eq_sum]
  show ∑ d, c * A.gibbsMass d = c
  rw [← Finset.mul_sum, A.sum_gibbsMass_eq_one, mul_one]

/-- An observable pointwise at least one has Gibbs expectation at
least one — the Gibbs law is a probability. -/
theorem one_le_gibbsExpect (φ : A.Λ → ℝ) (hφ : ∀ d, 1 ≤ φ d) :
    1 ≤ A.gibbsExpect φ := by
  rw [gibbsExpect_eq_sum]
  calc (1 : ℝ) = ∑ d, A.gibbsMass d := A.sum_gibbsMass_eq_one.symm
    _ ≤ ∑ d, φ d * A.gibbsMass d :=
      Finset.sum_le_sum fun d _ =>
        le_mul_of_one_le_left (A.gibbsMass_nonneg d) (hφ d)

/-- The Gibbs-mean redundancy of a surjection is positive. -/
theorem gibbsExpect_fiberCount_pos (hf : Function.Surjective f) :
    0 < A.gibbsExpect (fiberCount f) :=
  lt_of_lt_of_le one_pos
    (A.one_le_gibbsExpect (fiberCount f) (one_le_fiberCount hf))

/-- The Gibbs-mean product redundancy of two surjections is
positive. -/
theorem gibbsExpect_fiberCount_mul_pos (hf : Function.Surjective f)
    (hg : Function.Surjective g) :
    0 < A.gibbsExpect (fiberCount f * fiberCount g) :=
  lt_of_lt_of_le one_pos (A.one_le_gibbsExpect _ fun d => by
    rw [Pi.mul_apply]
    nlinarith [one_le_fiberCount hf d, one_le_fiberCount hg d])

/-- **The double-sum covariance identity** (G2): the Gibbs covariance
is half the doubly-indexed mean of coordinate products —
`Cov(φ,ψ) = ½ Σ_{d,d'} μ_d μ_{d'} (φ_d − φ_{d'})(ψ_d − ψ_{d'})`. -/
theorem gibbsCov_double_sum (φ ψ : A.Λ → ℝ) :
    A.gibbsCov φ ψ
      = (1 / 2) * ∑ d, ∑ d', A.gibbsMass d * A.gibbsMass d'
          * ((φ d - φ d') * (ψ d - ψ d')) := by
  have hkey : ∑ d, ∑ d', A.gibbsMass d * A.gibbsMass d'
      * ((φ d - φ d') * (ψ d - ψ d'))
      = ((∑ d, φ d * ψ d * A.gibbsMass d) * ∑ d, A.gibbsMass d)
        + ((∑ d, A.gibbsMass d) * ∑ d, φ d * ψ d * A.gibbsMass d)
        - ((∑ d, φ d * A.gibbsMass d) * ∑ d, ψ d * A.gibbsMass d)
        - ((∑ d, ψ d * A.gibbsMass d) * ∑ d, φ d * A.gibbsMass d) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum,
      Finset.sum_mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d' _ => ?_
    ring
  have h1 := A.sum_gibbsMass_eq_one
  show A.gibbsExpect (φ * ψ) - A.gibbsExpect φ * A.gibbsExpect ψ = _
  rw [hkey, h1, gibbsExpect_eq_sum, gibbsExpect_eq_sum, gibbsExpect_eq_sum]
  simp only [Pi.mul_apply]
  ring

/-! #### The currency (G9): the cumulant functional's KL identity

The exact law of the currency face: the gap between the cumulant
functional and the Gibbs mean **is** a relative entropy — against
the Gibbs law's own tilt — so every Jensen-type bound in the tree
flows through the house engine (`relativeEntropy_nonneg`,
`relativeEntropy_eq_zero_iff`), not through an external convexity
lemma. -/

/-- A pointwise-positive observable has positive Gibbs expectation
on a finite sector type — every sector carries positive Gibbs
mass. -/
theorem gibbsExpect_pos_of_pos (φ : A.Λ → ℝ) (hφ : ∀ k, 0 < φ k) :
    0 < A.gibbsExpect φ := by
  rw [A.gibbsExpect_eq_sum]
  obtain ⟨z, _⟩ := A.E_zero
  exact Finset.sum_pos
    (fun d _ => mul_pos (hφ d) (A.gibbsMass_pos d))
    ⟨z, Finset.mem_univ z⟩

/-- **THE KL IDENTITY** (G9, the exact law): the gap between the
cumulant functional and the Gibbs mean is the relative entropy of
the Gibbs law against its own tilt by the observable —
`cgf φ − ⟨φ⟩ = D(gibbs ‖ tilt φ gibbs)`. -/
theorem cgf_sub_gibbsExpect_eq_relativeEntropy (φ : A.Λ → ℝ) :
    A.cgf φ - A.gibbsExpect φ
      = A.gibbsDist.relativeEntropy (A.gibbsDist.tilt φ)
          (A.gibbsDist_fullSupport.tilt φ) := by
  have h1 : A.gibbsExpect (fun k => Real.exp (φ k))
      = ∑ y, Real.exp (φ y) * A.gibbsMass y := by
    rw [A.gibbsExpect_eq_sum]
  have hZ : 0 < ∑ y, Real.exp (φ y) * A.gibbsMass y := by
    rw [← h1]
    exact A.gibbsExpect_pos_of_pos _ fun k => Real.exp_pos _
  have hterm : ∀ x, A.gibbsMass x
      * Real.log (A.gibbsMass x / (A.gibbsDist.tilt φ).mass x)
      = A.gibbsMass x
        * (Real.log (∑ y, Real.exp (φ y) * A.gibbsMass y) - φ x) := by
    intro x
    congr 1
    show Real.log (A.gibbsMass x
        / (Real.exp (φ x) * A.gibbsMass x
            / ∑ y, Real.exp (φ y) * A.gibbsMass y)) = _
    rw [div_div_eq_mul_div, mul_comm (A.gibbsMass x),
      mul_div_mul_right _ _ (A.gibbsMass_pos x).ne',
      Real.log_div hZ.ne' (Real.exp_pos _).ne', Real.log_exp]
  show A.cgf φ - A.gibbsExpect φ
    = ∑ x, A.gibbsMass x
        * Real.log (A.gibbsMass x / (A.gibbsDist.tilt φ).mass x)
  rw [Finset.sum_congr rfl fun x _ => hterm x,
    Finset.sum_congr rfl fun x _ =>
      mul_sub (A.gibbsMass x) _ (φ x),
    Finset.sum_sub_distrib, ← Finset.sum_mul, A.sum_gibbsMass_eq_one,
    one_mul]
  show Real.log (A.gibbsExpect fun k => Real.exp (φ k))
      - A.gibbsExpect φ = _
  rw [h1, A.gibbsExpect_eq_sum φ,
    Finset.sum_congr rfl fun x _ => mul_comm (A.gibbsMass x) (φ x)]

/-- **The Gibbs–Jensen bound through the house engine** (G9): the
mean never exceeds the cumulant functional — the KL identity plus
the Gibbs inequality. -/
theorem gibbsExpect_le_cgf (φ : A.Λ → ℝ) :
    A.gibbsExpect φ ≤ A.cgf φ := by
  have h := A.cgf_sub_gibbsExpect_eq_relativeEntropy φ
  have hnn := FinDist.relativeEntropy_nonneg A.gibbsDist
    (A.gibbsDist.tilt φ) (A.gibbsDist_fullSupport.tilt φ)
  linarith

/-- **The gap's boundary** (G9): the cumulant functional meets the
mean exactly at constant observables — zero relative entropy
characterizes the Gibbs law as its own tilt. -/
theorem cgf_sub_gibbsExpect_eq_zero_iff (φ : A.Λ → ℝ) :
    A.cgf φ - A.gibbsExpect φ = 0 ↔ ∀ k k', φ k = φ k' := by
  rw [A.cgf_sub_gibbsExpect_eq_relativeEntropy φ,
    FinDist.relativeEntropy_eq_zero_iff]
  have hZ : 0 < ∑ y, Real.exp (φ y) * A.gibbsMass y :=
    A.gibbsDist.tilt_norm_pos φ
  constructor
  · intro heq k k'
    have hexp : ∀ j, Real.exp (φ j)
        = ∑ y, Real.exp (φ y) * A.gibbsMass y := by
      intro j
      have h : A.gibbsMass j
          = Real.exp (φ j) * A.gibbsMass j
            / ∑ y, Real.exp (φ y) * A.gibbsMass y :=
        congrFun (congrArg FinDist.mass heq) j
      rw [eq_div_iff hZ.ne'] at h
      have h2 : (∑ y, Real.exp (φ y) * A.gibbsMass y) * A.gibbsMass j
          = Real.exp (φ j) * A.gibbsMass j := by
        rw [← h]; ring
      exact (mul_right_cancel₀ (A.gibbsMass_pos j).ne' h2).symm
    exact Real.exp_injective ((hexp k).trans (hexp k').symm)
  · intro hconst
    refine (FinDist.ext ?_).symm
    funext x
    show Real.exp (φ x) * A.gibbsMass x
        / ∑ y, Real.exp (φ y) * A.gibbsMass y = A.gibbsMass x
    rw [show (∑ y, Real.exp (φ y) * A.gibbsMass y)
        = Real.exp (φ x) from by
      rw [Finset.sum_congr rfl fun y _ => by rw [hconst y x],
        ← Finset.mul_sum, A.sum_gibbsMass_eq_one, mul_one],
      mul_comm (Real.exp (φ x)), mul_div_assoc,
      div_self (Real.exp_pos (φ x)).ne', mul_one]

/-- **The bilinear boundary** (G9): the cumulant functional's
additivity defect on a pair vanishes exactly at zero Gibbs
covariance of the exponentiated observables — the gravity boundary's
proof, generalized. -/
theorem cgf_bilinear_eq_zero_iff (φ ψ : A.Λ → ℝ) :
    A.cgf (φ + ψ) - A.cgf φ - A.cgf ψ = 0
      ↔ A.gibbsCov (Real.exp ∘ φ) (Real.exp ∘ ψ) = 0 := by
  have hm : 0 < A.gibbsExpect (fun k => Real.exp (φ k)) :=
    A.gibbsExpect_pos_of_pos _ fun k => Real.exp_pos _
  have hm' : 0 < A.gibbsExpect (fun k => Real.exp (ψ k)) :=
    A.gibbsExpect_pos_of_pos _ fun k => Real.exp_pos _
  have hmm : 0 < A.gibbsExpect
      ((fun k => Real.exp (φ k)) * fun k => Real.exp (ψ k)) :=
    A.gibbsExpect_pos_of_pos _ fun k =>
      mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hsum : A.cgf (φ + ψ)
      = Real.log (A.gibbsExpect
          ((fun k => Real.exp (φ k)) * fun k => Real.exp (ψ k))) := by
    show Real.log (A.gibbsExpect fun k => Real.exp (φ k + ψ k)) = _
    rw [show (fun k => Real.exp (φ k + ψ k))
        = ((fun k => Real.exp (φ k)) * fun k => Real.exp (ψ k)) from
      funext fun k => Real.exp_add (φ k) (ψ k)]
  show A.cgf (φ + ψ) - A.cgf φ - A.cgf ψ = 0
    ↔ A.gibbsExpect
        ((fun k => Real.exp (φ k)) * fun k => Real.exp (ψ k))
      - A.gibbsExpect (fun k => Real.exp (φ k))
        * A.gibbsExpect (fun k => Real.exp (ψ k)) = 0
  rw [hsum]
  show Real.log (A.gibbsExpect _)
      - Real.log (A.gibbsExpect fun k => Real.exp (φ k))
      - Real.log (A.gibbsExpect fun k => Real.exp (ψ k)) = 0 ↔ _
  constructor
  · intro h0
    have hlogeq : Real.log (A.gibbsExpect
        ((fun k => Real.exp (φ k)) * fun k => Real.exp (ψ k)))
        = Real.log (A.gibbsExpect (fun k => Real.exp (φ k))
            * A.gibbsExpect fun k => Real.exp (ψ k)) := by
      rw [Real.log_mul hm.ne' hm'.ne']
      linarith
    have heq := Real.log_injOn_pos (Set.mem_Ioi.mpr hmm)
      (Set.mem_Ioi.mpr (mul_pos hm hm')) hlogeq
    rw [heq]
    ring
  · intro hcov
    rw [show A.gibbsExpect
        ((fun k => Real.exp (φ k)) * fun k => Real.exp (ψ k))
        = A.gibbsExpect (fun k => Real.exp (φ k))
          * A.gibbsExpect fun k => Real.exp (ψ k) from
      by linarith, Real.log_mul hm.ne' hm'.ne']
    ring

/-! #### The evaluations and the law -/

/-- **The lift's partition function**: the base partition function
times the Gibbs-mean redundancy. -/
theorem lift_partFn (hf : Function.Surjective f) :
    (A.lift f hf).partFn = A.partFn * A.gibbsExpect (fiberCount f) := by
  classical
  show (∑' x : X, Real.exp (-A.E (f x))) = _
  rw [tsum_fintype, sum_comp_fiberCount f (fun d => Real.exp (-A.E d)),
    gibbsExpect_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  show fiberCount f d * Real.exp (-A.E d)
    = A.partFn * (fiberCount f d * (Real.exp (-A.E d) / A.partFn))
  field_simp [A.partFn_pos.ne']

/-- **The lift's complexity — the priced increment is the log
Gibbs-mean redundancy** (G2; consumed by G5):
`K(lift f) = K + log ⟨fiberCount f⟩`. -/
theorem lift_complexity (hf : Function.Surjective f) :
    (A.lift f hf).complexity
      = A.complexity + Real.log (A.gibbsExpect (fiberCount f)) := by
  show Real.log (A.lift f hf).partFn = _
  rw [lift_partFn A f hf,
    Real.log_mul A.partFn_pos.ne'
      (A.gibbsExpect_fiberCount_pos f hf).ne']
  rfl

omit [Fintype X] [Fintype Y] in
/-- **The coupling's partition function**: the base times the
Gibbs-mean of the product redundancy — pullback fibers are fiber
products. -/
theorem couple_partFn [Fintype (SGD.Pullback f g)]
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    (A.couple f g hf hg).partFn
      = A.partFn * A.gibbsExpect (fiberCount f * fiberCount g) := by
  classical
  show (∑' p : SGD.Pullback f g, Real.exp (-A.E (SGD.Pullback.base p))) = _
  rw [tsum_fintype,
    sum_comp_fiberCount (fun p : SGD.Pullback f g => SGD.Pullback.base p)
      (fun d => Real.exp (-A.E d)),
    Finset.sum_congr rfl fun d _ => by rw [fiberCount_pullback_base f g d],
    gibbsExpect_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  show fiberCount f d * fiberCount g d * Real.exp (-A.E d)
    = A.partFn * ((fiberCount f * fiberCount g) d
        * (Real.exp (-A.E d) / A.partFn))
  rw [Pi.mul_apply]
  field_simp [A.partFn_pos.ne']

/-- **The coupling's complexity**: `K(couple) = K + log ⟨m·m'⟩`. -/
theorem couple_complexity [Fintype (SGD.Pullback f g)]
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    (A.couple f g hf hg).complexity
      = A.complexity
        + Real.log (A.gibbsExpect (fiberCount f * fiberCount g)) := by
  show Real.log (A.couple f g hf hg).partFn = _
  rw [couple_partFn A f g hf hg,
    Real.log_mul A.partFn_pos.ne'
      (A.gibbsExpect_fiberCount_mul_pos f g hf hg).ne']
  rfl

/-- **THE COVARIANCE GRAVITY LAW** (G2, the exact law): sharing two
descriptions over one base saves exactly the base — corrected by the
log-correlation of their redundancy profiles. The correction term is
a fluctuation quantity: gravity's exactness is measured by the
uncertainty face. -/
theorem gravity_defect [Fintype (SGD.Pullback f g)]
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    A.gravityDefect f g hf hg
      = Real.log (A.gibbsExpect (fiberCount f * fiberCount g))
        - Real.log (A.gibbsExpect (fiberCount f))
        - Real.log (A.gibbsExpect (fiberCount g)) := by
  show ((A.couple f g hf hg).complexity + A.complexity)
      - ((A.lift f hf).complexity + (A.lift g hg).complexity) = _
  rw [couple_complexity A f g hf hg, lift_complexity A f hf,
    lift_complexity A g hg]
  ring

/-- **The gravity recognition** (G9): the defect is the cumulant
functional's additivity defect at the two log-redundancies — a
rewrite of `gravity_defect`, since `Real.exp` inverts `Real.log` on
the positive redundancy profiles. -/
theorem gravityDefect_eq_cgf [Fintype (SGD.Pullback f g)]
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    A.gravityDefect f g hf hg
      = A.cgf ((fun d => Real.log (fiberCount f d))
            + fun d => Real.log (fiberCount g d))
        - A.cgf (fun d => Real.log (fiberCount f d))
        - A.cgf (fun d => Real.log (fiberCount g d)) := by
  have hposf : ∀ d, 0 < fiberCount f d := fun d =>
    lt_of_lt_of_le one_pos (one_le_fiberCount hf d)
  have hposg : ∀ d, 0 < fiberCount g d := fun d =>
    lt_of_lt_of_le one_pos (one_le_fiberCount hg d)
  have h1 : A.cgf ((fun d => Real.log (fiberCount f d))
        + fun d => Real.log (fiberCount g d))
      = Real.log (A.gibbsExpect (fiberCount f * fiberCount g)) := by
    show Real.log (A.gibbsExpect fun k =>
      Real.exp (Real.log (fiberCount f k) + Real.log (fiberCount g k))) = _
    rw [show (fun k =>
        Real.exp (Real.log (fiberCount f k) + Real.log (fiberCount g k)))
        = fiberCount f * fiberCount g from funext fun k => by
      rw [Real.exp_add, Real.exp_log (hposf k), Real.exp_log (hposg k)]
      rfl]
  have h2 : A.cgf (fun d => Real.log (fiberCount f d))
      = Real.log (A.gibbsExpect (fiberCount f)) := by
    show Real.log (A.gibbsExpect fun k =>
      Real.exp (Real.log (fiberCount f k))) = _
    rw [show (fun k => Real.exp (Real.log (fiberCount f k)))
        = fiberCount f from funext fun k => Real.exp_log (hposf k)]
  have h3 : A.cgf (fun d => Real.log (fiberCount g d))
      = Real.log (A.gibbsExpect (fiberCount g)) := by
    show Real.log (A.gibbsExpect fun k =>
      Real.exp (Real.log (fiberCount g k))) = _
    rw [show (fun k => Real.exp (Real.log (fiberCount g k)))
        = fiberCount g from funext fun k => Real.exp_log (hposg k)]
  rw [A.gravity_defect f g hf hg, h1, h2, h3]

/-- **The boundary** (G2): the defect vanishes exactly at zero
covariance of the redundancy profiles — the constant-fiber gravity
identity (`complexity_gravity`) is the zero-covariance chart, not a
law of coupling. Demoted at G9 (rule 3): re-derived from the generic
`cgf_bilinear_eq_zero_iff` through the gravity recognition
(`gravityDefect_eq_cgf`); the direct log-injectivity route is
retired. -/
theorem gravity_defect_eq_zero_iff [Fintype (SGD.Pullback f g)]
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    A.gravityDefect f g hf hg = 0
      ↔ A.gibbsCov (fiberCount f) (fiberCount g) = 0 := by
  have hposf : ∀ d, 0 < fiberCount f d := fun d =>
    lt_of_lt_of_le one_pos (one_le_fiberCount hf d)
  have hposg : ∀ d, 0 < fiberCount g d := fun d =>
    lt_of_lt_of_le one_pos (one_le_fiberCount hg d)
  rw [A.gravityDefect_eq_cgf f g hf hg, A.cgf_bilinear_eq_zero_iff,
    show Real.exp ∘ (fun d => Real.log (fiberCount f d)) = fiberCount f
      from funext fun d => Real.exp_log (hposf d),
    show Real.exp ∘ (fun d => Real.log (fiberCount g d)) = fiberCount g
      from funext fun d => Real.exp_log (hposg d)]

/-- **The direction theorem** (G2): comonotone redundancy binds — if
the two fiber-count profiles move together across every sector pair,
the defect is nonnegative, by the double-sum covariance identity. -/
theorem gravityDefect_nonneg_of_comonotone [Fintype (SGD.Pullback f g)]
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hmono : ∀ d d', 0 ≤ (fiberCount f d - fiberCount f d')
        * (fiberCount g d - fiberCount g d')) :
    0 ≤ A.gravityDefect f g hf hg := by
  have hm := A.gibbsExpect_fiberCount_pos f hf
  have hm' := A.gibbsExpect_fiberCount_pos g hg
  have hcov : 0 ≤ A.gibbsCov (fiberCount f) (fiberCount g) := by
    rw [A.gibbsCov_double_sum]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun d _ =>
      Finset.sum_nonneg fun d' _ => mul_nonneg
        (mul_nonneg (A.gibbsMass_nonneg d) (A.gibbsMass_nonneg d'))
        (hmono d d'))
  have hcov' : A.gibbsExpect (fiberCount f * fiberCount g)
      - A.gibbsExpect (fiberCount f) * A.gibbsExpect (fiberCount g)
      = A.gibbsCov (fiberCount f) (fiberCount g) := rfl
  have hlog : Real.log (A.gibbsExpect (fiberCount f)
        * A.gibbsExpect (fiberCount g))
      ≤ Real.log (A.gibbsExpect (fiberCount f * fiberCount g)) :=
    Real.log_le_log (mul_pos hm hm') (by linarith)
  rw [Real.log_mul hm.ne' hm'.ne'] at hlog
  rw [A.gravity_defect f g hf hg]
  linarith

end CovarianceGravity

/-! ### Time, non-uniform (G5)

The ratchet, unconditioned. The priced increment of the lift is the
log Gibbs-mean redundancy (`lift_complexity`, delivered at G2), the
counted cost stays exact and non-uniform
(`sectionCost_eq_sum_log_fiberCount`), and between them sits Jensen:
the Gibbs-mean log-redundancy bounds the priced increment from below
(`lift_complexity_ge_gibbs_log_rate`), with gap zero exactly at
constant redundancy — full Gibbs support makes the boundary exact
(`lift_complexity_sub_eq_iff_fiberCount_const`). The ratchet's
defect is the Jensen gap of redundancy, one more fluctuation
quantity. **The impossibility anchor is the standing
`sectionCostE_eq_zero_iff`**: free reversal is impossible off
bijections. The strictness witness is G2's two-sector pair
(`twoSector_jensen_gap_pos`, at the file's tail); the
constant-redundancy chart is the demoted `sectionCost_uniformLift`
below. -/

section TimeNonUniform

variable (A : SectorAction.{u}) {X : Type u} [Fintype X]
  (f : X → A.Λ) [Fintype A.Λ]

/-- **The time recognition** (G9): the priced increment of the lift
is the cumulant functional of the log-redundancy — a rewrite of
`lift_complexity`, since `Real.exp` inverts `Real.log` on the
redundancy profile (`one_le_fiberCount`). -/
theorem lift_complexity_eq_cgf (hf : Function.Surjective f) :
    (A.lift f hf).complexity - A.complexity
      = A.cgf (fun d => Real.log (fiberCount f d)) := by
  rw [A.lift_complexity f hf, add_sub_cancel_left]
  show _ = Real.log (A.gibbsExpect fun k =>
    Real.exp (Real.log (fiberCount f k)))
  rw [show (fun k => Real.exp (Real.log (fiberCount f k)))
      = fiberCount f from funext fun k => Real.exp_log
    (lt_of_lt_of_le one_pos (one_le_fiberCount hf k))]

/-- **THE JENSEN RATCHET BOUND** (G5, the law with correction term):
the Gibbs-mean log-redundancy is at most the priced increment of the
lift — `⟨log ∘ fiberCount f⟩ ≤ K(lift f) − K`. The gap is the Jensen
defect of the redundancy profile. Demoted at G9 (rule 3): re-derived
from the KL identity through the time recognition
(`lift_complexity_eq_cgf`, `gibbsExpect_le_cgf`); the external
`strictConcaveOn_log_Ioi` route is retired. -/
theorem lift_complexity_ge_gibbs_log_rate (hf : Function.Surjective f) :
    A.gibbsExpect (fun d => Real.log (fiberCount f d))
      ≤ (A.lift f hf).complexity - A.complexity := by
  rw [A.lift_complexity_eq_cgf f hf]
  exact A.gibbsExpect_le_cgf _

/-- **The boundary** (G5): the Jensen gap vanishes exactly at
constant redundancy — every sector carries positive Gibbs mass, so
full support makes the boundary exact. Demoted at G9 (rule 3):
re-derived from the KL identity's boundary
(`cgf_sub_gibbsExpect_eq_zero_iff`) through the time recognition;
the external `StrictConcaveOn` route is retired. -/
theorem lift_complexity_sub_eq_iff_fiberCount_const
    (hf : Function.Surjective f) :
    (A.lift f hf).complexity - A.complexity
        = A.gibbsExpect (fun d => Real.log (fiberCount f d))
      ↔ ∀ d d', fiberCount f d = fiberCount f d' := by
  have hpos : ∀ d, 0 < fiberCount f d := fun d =>
    lt_of_lt_of_le one_pos (one_le_fiberCount hf d)
  rw [A.lift_complexity_eq_cgf f hf, ← sub_eq_zero,
    A.cgf_sub_gibbsExpect_eq_zero_iff]
  constructor
  · intro h d d'
    have hlog := h d d'
    rw [← Real.exp_log (hpos d), ← Real.exp_log (hpos d'), hlog]
  · intro h k k'
    rw [h k k']

end TimeNonUniform

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

omit [Fintype A.Λ] in
/-- **The lift decomposes as base ⊗ free sectors** (review #21): the
priced uniform lift is energy-equivalent to the independent product
of the base with a free action on any `m`-element sector type — the
structured form of the fiber decomposition `uniformLift_partFn`
computes numerically. -/
theorem uniformLift_energyEquiv (W : Type u) [Fintype W] [Nonempty W]
    (hW : Fintype.card W = m) :
    (A.uniformLift f hm hfib).EnergyEquiv (A.prod (uniformAction W)) := by
  have ef : ∀ d, Nonempty ({x : X // f x = d} ≃ W) := fun d =>
    Finite.card_eq.mp (by rw [hfib d, Nat.card_eq_fintype_card, hW])
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight fun d => (ef d).some).trans
      (Equiv.sigmaEquivProd A.Λ W)), fun x => ?_⟩
  show A.E (f x) + 0 = A.E (f x)
  rw [add_zero]

/-- **TIME, GENERIC AND PRICED — the constant-redundancy chart**
(review #14; demoted at G5, PLAN rule 3): for a constant-fiber map
into a finite sector action's sector type, the normalized section
cost is exactly the complexity increment of the priced uniform lift —
`sectionCost f / |Λ| = K(uniformLift) − K(base)`. This is the
**constant-redundancy instance of the non-uniform time laws**: the
counted cost is `Σ_d log (fiberCount f d)`
(`sectionCost_eq_sum_log_fiberCount`), the priced increment is
`log ⟨fiberCount f⟩` (`lift_complexity`, with `uniformLift = lift`
by proof irrelevance), and constant redundancy collapses both sides
to `log m`. The independent route through
`sectionCost_eq_fiberInfoCost` and `uniformLift_complexity` is
retired. -/
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
  have hcf : fiberCount f = fun _ : A.Λ => (m : ℝ) := funext fun d => by
    show (Nat.card {x : X // f x = d} : ℝ) = m
    rw [hfib d]
  have hcost : sectionCost f = Fintype.card A.Λ * Real.log m := by
    rw [sectionCost_eq_sum_log_fiberCount hsurj, hcf]
    show ∑ _d : A.Λ, Real.log (m : ℝ) = Fintype.card A.Λ * Real.log m
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hlift : (A.uniformLift f hm hfib).complexity - A.complexity
      = Real.log m := by
    have h : (A.uniformLift f hm hfib).complexity
        = A.complexity + Real.log (A.gibbsExpect (fiberCount f)) :=
      A.lift_complexity f hsurj
    rw [h, hcf, A.gibbsExpect_const]
    ring
  have hcard : (0 : ℝ) < Fintype.card A.Λ := by
    have : Nonempty A.Λ := ⟨A.E_zero.choose⟩
    exact_mod_cast Fintype.card_pos
  rw [hcost, hlift, mul_div_cancel_left₀ _ hcard.ne']

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

omit [Fintype A.Λ] in
/-- **The coupling decomposes as base ⊗ (free ⊗ free)** (review #21):
the priced shared-base coupling is energy-equivalent to the
independent product of the base with two free actions — the
decomposition that carries the gravity theorem's sharing content. -/
theorem coupling_energyEquiv (W W' : Type u) [Fintype W] [Nonempty W]
    [Fintype W'] [Nonempty W'] (hW : Fintype.card W = m)
    (hW' : Fintype.card W' = m') :
    (A.coupling f g hm hm' hf hg).EnergyEquiv
      (A.prod ((uniformAction W).prod (uniformAction W'))) := by
  have ef : ∀ d, Nonempty ({x : X // f x = d} ≃ W) := fun d =>
    Finite.card_eq.mp (by rw [hf d, Nat.card_eq_fintype_card, hW])
  have eg : ∀ d, Nonempty ({y : Y // g y = d} ≃ W') := fun d =>
    Finite.card_eq.mp (by rw [hg d, Nat.card_eq_fintype_card, hW'])
  refine ⟨(SGD.Pullback.equivSigmaFiber f g).trans
    ((Equiv.sigmaCongrRight fun d =>
        Equiv.prodCongr (ef d).some (eg d).some).trans
      (Equiv.sigmaEquivProd A.Λ (W × W'))), fun p => ?_⟩
  show A.E (SGD.Pullback.base p) + (0 + 0) = A.E (SGD.Pullback.base p)
  rw [add_zero, add_zero]

omit [Fintype A.Λ] in
/-- **THE GRAVITY THEOREM — the zero-covariance chart** (reviews #13,
#21, #25, #28, #29; demoted at G2, PLAN rule 3):
`K(coupling) + K(base) = K(lift) + K(lift)` — merging two
descriptions over a shared base saves exactly the base's
complexity. This is the **constant-fiber instance of the covariance
gravity law** (`gravity_defect`): constant redundancy profiles have
zero Gibbs covariance, so the defect vanishes and the four-term
identity closes. The fiber hypotheses force the base finite; no
Fintype instance is taken in the statement (review #29) — the proof
constructs finiteness from surjectivity. The decomposition route
(`coupling_energyEquiv`, `uniformLift_energyEquiv`,
`complexity_prod`) remains standing as structure; the independent
proof route through it is retired. Counting gravity is the
zero-energy corollary (`counting_gravity`, below); the entropy form
is the Gibbs-split corollary (`entropy_gravity`). -/
theorem complexity_gravity :
    (A.coupling f g hm hm' hf hg).complexity + A.complexity
      = (A.uniformLift f hm hf).complexity
        + (A.uniformLift g hm' hg).complexity := by
  classical
  have hsf : Function.Surjective f := fun d => by
    have hpos : 0 < Nat.card {x : X // f x = d} := by rw [hf d]; exact hm
    obtain ⟨⟨x, hx⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨x, hx⟩
  have hsg : Function.Surjective g := fun d => by
    have hpos : 0 < Nat.card {y : Y // g y = d} := by rw [hg d]; exact hm'
    obtain ⟨⟨y, hy⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    exact ⟨y, hy⟩
  haveI : Finite A.Λ := Finite.of_surjective f hsf
  haveI : Fintype A.Λ := Fintype.ofFinite _
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hm'0 : (m' : ℝ) ≠ 0 := by exact_mod_cast hm'.ne'
  have hcf : fiberCount f = fun _ => (m : ℝ) := funext fun d => by
    show (Nat.card {x : X // f x = d} : ℝ) = m
    rw [hf d]
  have hcg : fiberCount g = fun _ => (m' : ℝ) := funext fun d => by
    show (Nat.card {y : Y // g y = d} : ℝ) = m'
    rw [hg d]
  have hconst : ∀ c : ℝ, A.gibbsExpect (fun _ => c) = c := fun c =>
    A.gibbsExpect_const c
  have hd := A.gravity_defect f g hsf hsg
  rw [hcf, hcg] at hd
  rw [show ((fun _ : A.Λ => (m : ℝ)) * fun _ : A.Λ => (m' : ℝ))
      = fun _ : A.Λ => (m : ℝ) * m' from rfl,
    hconst, hconst, hconst, Real.log_mul hm0 hm'0] at hd
  have hdef : A.gravityDefect f g hsf hsg
      = ((A.couple f g hsf hsg).complexity + A.complexity)
        - ((A.lift f hsf).complexity + (A.lift g hsg).complexity) := rfl
  have hzero : ((A.coupling f g hm hm' hf hg).complexity + A.complexity)
      - ((A.uniformLift f hm hf).complexity
          + (A.uniformLift g hm' hg).complexity) = 0 := by
    have h0 : ((A.couple f g hsf hsg).complexity + A.complexity)
        - ((A.lift f hsf).complexity + (A.lift g hsg).complexity) = 0 := by
      rw [← hdef]
      linarith
    exact h0
  linarith

omit [Fintype A.Λ] in
/-- **The action-level partition-function gravity identity**
(reviews #13, #21): `Z_pair · Z_base = Z_lift · Z_lift` — the
complexity gravity identity exponentiated, since every partition
function is positive. -/
theorem partFn_gravity :
    (A.coupling f g hm hm' hf hg).partFn * A.partFn
      = (A.uniformLift f hm hf).partFn
        * (A.uniformLift g hm' hg).partFn := by
  have h := congrArg Real.exp (complexity_gravity A f g hm hm' hf hg)
  simp only [SectorAction.complexity, Real.exp_add,
    Real.exp_log (A.coupling f g hm hm' hf hg).partFn_pos,
    Real.exp_log A.partFn_pos,
    Real.exp_log (A.uniformLift f hm hf).partFn_pos,
    Real.exp_log (A.uniformLift g hm' hg).partFn_pos] at h
  exact h

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

/-! ## Counting gravity — the zero-energy corollary -/

/-- **COUNTING GRAVITY** (review #25): for uniform-fiber maps into a
shared finite nonempty base,
`log |X ×_D Y| + log |D| = log |X| + log |Y|`. Not a parallel
type-level theory: this is `SectorAction.complexity_gravity`
instantiated at the zero-energy action `uniformAction D` — the
uniform lift and coupling of a zero-energy action are themselves
zero-energy actions on `X`, `Y`, and the pullback (identity
equivalences suffice), and `uniformAction_complexity` evaluates the
four complexities. Counting is the zero-energy special case of
pricing. -/
theorem counting_gravity {X Y D : Type u} [Fintype X] [Fintype Y]
    [Fintype D] [Nonempty D] (f : X → D) (g : Y → D)
    {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m')
    (hf : ∀ d, Nat.card {x : X // f x = d} = m)
    (hg : ∀ d, Nat.card {y : Y // g y = d} = m') :
    Real.log (Nat.card (SGD.Pullback f g)) + Real.log (Nat.card D)
      = Real.log (Nat.card X) + Real.log (Nat.card Y) := by
  haveI : DecidableEq D := Classical.decEq D
  obtain ⟨d₀⟩ := ‹Nonempty D›
  obtain ⟨⟨x₀, hx₀⟩⟩ :=
    (Nat.card_pos_iff.mp (lt_of_lt_of_eq hm (hf d₀).symm)).1
  obtain ⟨⟨y₀, hy₀⟩⟩ :=
    (Nat.card_pos_iff.mp (lt_of_lt_of_eq hm' (hg d₀).symm)).1
  haveI : Nonempty X := ⟨x₀⟩
  haveI : Nonempty Y := ⟨y₀⟩
  haveI : Nonempty (SGD.Pullback f g) := ⟨⟨(x₀, y₀), hx₀.trans hy₀.symm⟩⟩
  have hcoup : ((uniformAction D).coupling f g hm hm' hf hg).EnergyEquiv
      (uniformAction (SGD.Pullback f g)) := ⟨Equiv.refl _, fun _ => rfl⟩
  have hliftf : ((uniformAction D).uniformLift f hm hf).EnergyEquiv
      (uniformAction X) := ⟨Equiv.refl _, fun _ => rfl⟩
  have hliftg : ((uniformAction D).uniformLift g hm' hg).EnergyEquiv
      (uniformAction Y) := ⟨Equiv.refl _, fun _ => rfl⟩
  have key :=
    SectorAction.complexity_gravity (uniformAction D) f g hm hm' hf hg
  rw [SectorAction.complexity_congr hcoup,
    SectorAction.complexity_congr hliftf,
    SectorAction.complexity_congr hliftg,
    uniformAction_complexity, uniformAction_complexity,
    uniformAction_complexity, uniformAction_complexity] at key
  simpa [Nat.card_eq_fintype_card] using key

/-! ## The two-sector witness: the defect is not identically zero (G2)

The strictness anchor and the face's negative. Base `Bool` with
energies `0` and `1`; one map with redundancy profile `(1, 2)` used
on both legs. The defect is `log(⟨m²⟩/⟨m⟩²)`, strictly positive by
strict Gibbs fluctuation of the non-constant profile — so **there is
no correlation-free general coupling**: the constant-fiber identity
is the zero-covariance chart, not a law of coupling. -/

/-- **The two-sector base** (G2 strictness): sectors `Bool`, energies
`0` and `1`. -/
noncomputable def twoSectorAction : SectorAction.{0} where
  Λ := Bool
  E b := cond b 1 0
  E_zero := ⟨false, rfl⟩
  E_nonneg b := by cases b <;> norm_num
  summable := (hasSum_fintype _).summable

instance : Fintype twoSectorAction.Λ := inferInstanceAs (Fintype Bool)

/-- The witness map: redundancy profile `(1, 2)` over
`(false, true)`. -/
def twoSectorMap : Fin 3 → Bool := ![false, true, true]

instance : Fintype (@SGD.Pullback (Fin 3) (Fin 3) twoSectorAction.Λ
    twoSectorMap twoSectorMap) :=
  inferInstanceAs
    (Fintype {p : Fin 3 × Fin 3 // twoSectorMap p.1 = twoSectorMap p.2})

theorem twoSectorMap_surjective : Function.Surjective twoSectorMap := by
  decide

theorem twoSectorMap_fiberCount_false :
    fiberCount twoSectorMap false = 1 := by
  show (Nat.card {x : Fin 3 // twoSectorMap x = false} : ℝ) = 1
  rw [Nat.card_eq_fintype_card,
    show Fintype.card {x : Fin 3 // twoSectorMap x = false} = 1 from by
      decide]
  norm_num

theorem twoSectorMap_fiberCount_true :
    fiberCount twoSectorMap true = 2 := by
  show (Nat.card {x : Fin 3 // twoSectorMap x = true} : ℝ) = 2
  rw [Nat.card_eq_fintype_card,
    show Fintype.card {x : Fin 3 // twoSectorMap x = true} = 2 from by
      decide]
  norm_num

/-- **THE STRICTNESS WITNESS** (G2): at the two-sector base with the
`(1, 2)` redundancy profile on both legs, the defect is
`log⟨m²⟩ − 2 log⟨m⟩ > 0` — strict Gibbs fluctuation of a
non-constant profile. -/
theorem twoSector_gravityDefect_pos :
    0 < twoSectorAction.gravityDefect twoSectorMap twoSectorMap
        twoSectorMap_surjective twoSectorMap_surjective := by
  have hs := twoSectorMap_surjective
  have hvar : 0 < twoSectorAction.gibbsVariance (fiberCount twoSectorMap) := by
    rcases eq_or_ne
        (twoSectorAction.gibbsExpect (fiberCount twoSectorMap)) 1 with
      he | hne
    · refine twoSectorAction.gibbsVariance_pos _ (hasSum_fintype _).summable
        (hasSum_fintype _).summable (k₀ := true) ?_
      rw [twoSectorMap_fiberCount_true, he]
      norm_num
    · refine twoSectorAction.gibbsVariance_pos _ (hasSum_fintype _).summable
        (hasSum_fintype _).summable (k₀ := false) ?_
      rw [twoSectorMap_fiberCount_false]
      exact Ne.symm hne
  have hmpos : 0 < twoSectorAction.gibbsExpect (fiberCount twoSectorMap) :=
    twoSectorAction.gibbsExpect_fiberCount_pos twoSectorMap hs
  have hsq : twoSectorAction.gibbsExpect (fiberCount twoSectorMap) ^ 2
      < twoSectorAction.gibbsExpect
          (fiberCount twoSectorMap * fiberCount twoSectorMap) := by
    have hcongr : twoSectorAction.gibbsExpect
        (fiberCount twoSectorMap * fiberCount twoSectorMap)
        = twoSectorAction.gibbsExpect
            (fun k => fiberCount twoSectorMap k ^ 2) :=
      congrArg _ (funext fun k => by
        rw [Pi.mul_apply]
        exact (pow_two _).symm)
    have hvar' : twoSectorAction.gibbsVariance (fiberCount twoSectorMap)
        = twoSectorAction.gibbsExpect
            (fun k => fiberCount twoSectorMap k ^ 2)
          - twoSectorAction.gibbsExpect (fiberCount twoSectorMap) ^ 2 := rfl
    rw [hcongr]
    linarith
  rw [twoSectorAction.gravity_defect twoSectorMap twoSectorMap hs hs]
  have hlog := Real.log_lt_log (by positivity) hsq
  rw [Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- **THE IMPOSSIBILITY** (G2): there is no correlation-free general
coupling — the defect is not identically zero, so the uniform
identity (`complexity_gravity`) is the zero-covariance chart, not a
law of coupling. -/
theorem exists_gravity_defect_ne_zero :
    ∃ (A : SectorAction.{0}) (_ : Fintype A.Λ) (X Y : Type)
      (_ : Fintype X) (_ : Fintype Y) (f : X → A.Λ) (g : Y → A.Λ)
      (_ : Fintype (SGD.Pullback f g)) (hf : Function.Surjective f)
      (hg : Function.Surjective g),
      A.gravityDefect f g hf hg ≠ 0 :=
  ⟨twoSectorAction, inferInstance, Fin 3, Fin 3, inferInstance,
    inferInstance, twoSectorMap, twoSectorMap, inferInstance,
    twoSectorMap_surjective, twoSectorMap_surjective,
    ne_of_gt twoSector_gravityDefect_pos⟩

/-- **The strictness of the ratchet's Jensen gap** (G5): at the
two-sector witness the Gibbs-mean log-redundancy is strictly below
the priced increment — the ratchet's defect is a genuine fluctuation
quantity. -/
theorem twoSector_jensen_gap_pos :
    twoSectorAction.gibbsExpect
        (fun d => Real.log (fiberCount twoSectorMap d))
      < (twoSectorAction.lift twoSectorMap
          twoSectorMap_surjective).complexity
        - twoSectorAction.complexity := by
  have hle := twoSectorAction.lift_complexity_ge_gibbs_log_rate
    twoSectorMap twoSectorMap_surjective
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    have hconst :=
      (twoSectorAction.lift_complexity_sub_eq_iff_fiberCount_const
        twoSectorMap twoSectorMap_surjective).mp heq.symm
    have h01 : fiberCount twoSectorMap false = fiberCount twoSectorMap true :=
      hconst false true
    rw [twoSectorMap_fiberCount_false, twoSectorMap_fiberCount_true] at h01
    norm_num at h01

/-- **The strictness of the currency's Jensen gap** (G9): at the
two-sector witness the cumulant functional strictly exceeds the
Gibbs mean of the log-redundancy — through the time recognition and
the standing witness (`twoSector_jensen_gap_pos`), single route. -/
theorem twoSector_cgf_gap_pos :
    0 < twoSectorAction.cgf
          (fun d => Real.log (fiberCount twoSectorMap d))
        - twoSectorAction.gibbsExpect
          (fun d => Real.log (fiberCount twoSectorMap d)) := by
  have h := twoSector_jensen_gap_pos
  rw [twoSectorAction.lift_complexity_eq_cgf twoSectorMap
    twoSectorMap_surjective] at h
  linarith

/-- **The strictness of the currency's additivity defect** (G9): at
the two-sector witness the cumulant functional is strictly
superadditive on the pair of log-redundancies — through the gravity
recognition and the standing witness
(`twoSector_gravityDefect_pos`), single route. -/
theorem twoSector_cgf_bilinear_pos :
    0 < twoSectorAction.cgf
          ((fun d => Real.log (fiberCount twoSectorMap d))
            + fun d => Real.log (fiberCount twoSectorMap d))
        - twoSectorAction.cgf
          (fun d => Real.log (fiberCount twoSectorMap d))
        - twoSectorAction.cgf
          (fun d => Real.log (fiberCount twoSectorMap d)) := by
  have h := twoSector_gravityDefect_pos
  rwa [twoSectorAction.gravityDefect_eq_cgf twoSectorMap twoSectorMap
    twoSectorMap_surjective twoSectorMap_surjective] at h

/-- **THE IMPOSSIBILITY** (G9): there is no linear currency — the
cumulant functional is not additive in the observable, witnessed by
the two-sector data through the strict additivity defect. -/
theorem cgf_not_additive :
    ∃ (A : SectorAction.{0}) (φ ψ : A.Λ → ℝ),
      A.cgf (φ + ψ) ≠ A.cgf φ + A.cgf ψ := by
  refine ⟨twoSectorAction,
    fun d => Real.log (fiberCount twoSectorMap d),
    fun d => Real.log (fiberCount twoSectorMap d),
    sub_ne_zero.mp ?_⟩
  have h := twoSector_cgf_bilinear_pos
  rw [sub_sub] at h
  exact h.ne'

end Meno
