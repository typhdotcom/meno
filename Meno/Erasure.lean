import Meno.Record

/-! # Erasure: the rate a reset must pay

The **erasure** of a map `f` on a finite set `I` is
`log |I| − log |f '' I|`, the log-count `f` does not carry to its
image (`erasure`); it vanishes on an injective map
(`erasure_eq_zero_of_injOn`).

A **reset** returns noisy states to cocycles: it reads `x + s` (a
cocycle `x`, an error `s ∈ S`) together with a memory state in `A`, and
writes a cocycle together with a memory state in `A'`. The inputs number
at least `|cocycles| · |σ S| · |A|` (`card_le_card_noisyInputs`), the
outputs at most `|cocycles| · |A'|`. The face's anchors:

* **The tick law** (`log_card_syndrome_add_le`): `log |σ S| + log |A|
  ≤ log |A'| + erasure` — each tick either grows the occupied memory or
  erases, by `log |σ S|` together. No closure is assumed: the floor is
  the price of returning to zero syndrome.
* **THE RATE LAW** (`sum_erasure_ge`): over `T` ticks on a memory `M`,
  `Σ erasure ≥ T · log |σ S| + log |A₀| − log |M|` — the average
  erasure per tick is at least `log |σ S|`.
* **Attainment** (`Decoder.erasure_reset`): correcting by a decoder and
  leaving memory untouched erases exactly `log |σ S|`. With a decoder
  that closes `S`, `|σ S|` is the number of gauge classes `S` meets
  (`Decoder.card_records`).
* **The price, split** (`Decoder.log_card_le_erasure_add_gauge`): for a
  closable `S`, `log |S| ≤ erasure + log |gauge|` — of an error's
  log-count, the syndrome part is erased and the rest fits the gauge. -/

namespace Meno

universe u

/-- **The erasure** of `f` on `I`: the log-count `f` does not carry to
its image. -/
noncomputable def erasure {α β : Type*} (f : α → β) (I : Set α) : ℝ :=
  Real.log (Nat.card I) - Real.log (Nat.card (f '' I))

/-- An injective map erases nothing. -/
theorem erasure_eq_zero_of_injOn {α β : Type*} {f : α → β} {I : Set α}
    (h : Set.InjOn f I) : erasure f I = 0 := by
  rw [erasure, Nat.card_image_of_injOn h, sub_self]

namespace TwoComplex

variable {G : IncidenceGraph.{u}} (X : TwoComplex.{u} G) (R : Type u) [CommRing R]
  [Fintype R]

/-- **The noisy inputs**: an error from `S` on a cocycle, with memory
in `A`. -/
def noisyInputs {M : Type*} (S : Set (G.E → R)) (A : Set M) : Set ((G.E → R) × M) :=
  {p | (∃ x : X.cocyclesR R, ∃ s ∈ S, p.1 = x + s) ∧ p.2 ∈ A}

omit [Fintype R] in
theorem noisyInputs_nonempty {M : Type*} {S : Set (G.E → R)} (h0 : (0 : G.E → R) ∈ S)
    {A : Set M} (hA : A.Nonempty) : (X.noisyInputs R S A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  exact ⟨(0, a), ⟨0, 0, h0, by simp⟩, ha⟩

open Classical in
/-- **The input count**: a cocycle, a syndrome `S` attains, and a memory
state determine a noisy input. -/
theorem card_le_card_noisyInputs {M : Type*} [Finite M] (S : Set (G.E → R)) (A : Set M) :
    Nat.card (X.cocyclesR R) * Nat.card (X.syndrome R '' S) * Nat.card A
      ≤ Nat.card (X.noisyInputs R S A) := by
  have hL : Nat.card ((X.cocyclesR R × (X.syndrome R '' S)) × A)
      = Nat.card (X.cocyclesR R) * Nat.card (X.syndrome R '' S) * Nat.card A := by
    rw [Nat.card_prod, Nat.card_prod]
  rw [← hL]
  refine Nat.card_le_card_of_injective
    (fun p => ⟨((p.1.1 : G.E → R) + p.1.2.2.choose, p.2),
      ⟨p.1.1, _, p.1.2.2.choose_spec.1, rfl⟩, p.2.2⟩) ?_
  rintro ⟨⟨z, τ⟩, a⟩ ⟨⟨z', τ'⟩, a'⟩ h
  have hv := congrArg Subtype.val h
  simp only [Prod.mk.injEq] at hv
  obtain ⟨h1, h2⟩ := hv
  have hτ : τ = τ' := by
    apply Subtype.ext
    have := congrArg (X.syndrome R) h1
    rwa [map_add, map_add, LinearMap.mem_ker.mp z.2, LinearMap.mem_ker.mp z'.2, zero_add,
      zero_add, τ.2.choose_spec.2, τ'.2.choose_spec.2] at this
  subst hτ
  rw [Subtype.ext (add_right_cancel h1), Subtype.ext h2]

omit [Fintype R] in
/-- **The output count**: a reset landing in `A'` has at most
`|cocycles| · |A'|` outputs. -/
theorem card_image_le {M : Type*} [Finite R] [Finite M] (S : Set (G.E → R)) (A A' : Set M)
    (Φ : (G.E → R) × M → X.cocyclesR R × M)
    (hland : ∀ p ∈ X.noisyInputs R S A, (Φ p).2 ∈ A') :
    Nat.card (Φ '' X.noisyInputs R S A) ≤ Nat.card (X.cocyclesR R) * Nat.card A' := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun q => (q.1.1, ⟨q.1.2, ?_⟩)) ?_
  · obtain ⟨p, hp, hq⟩ := q.2
    rw [← hq]
    exact hland p hp
  · intro q q' h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    exact Subtype.ext (Prod.ext h.1 h.2)

/-- **THE TICK LAW**: a reset from memory states in `A` to memory states
in `A'` grows the occupied memory or erases, by `log |σ S|` together. -/
theorem log_card_syndrome_add_le {M : Type*} [Finite M] (S : Set (G.E → R))
    (h0 : (0 : G.E → R) ∈ S) (A A' : Set M) (hA : A.Nonempty)
    (Φ : (G.E → R) × M → X.cocyclesR R × M)
    (hland : ∀ p ∈ X.noisyInputs R S A, (Φ p).2 ∈ A') :
    Real.log (Nat.card (X.syndrome R '' S)) + Real.log (Nat.card A)
      ≤ Real.log (Nat.card A') + erasure Φ (X.noisyInputs R S A) := by
  have hI := X.noisyInputs_nonempty R h0 hA
  have hZ : 0 < Nat.card (X.cocyclesR R) := Nat.card_pos
  have hS : 0 < Nat.card (X.syndrome R '' S) := by
    have : Nonempty (X.syndrome R '' S) := ⟨⟨_, 0, h0, rfl⟩⟩
    exact Nat.card_pos
  have hAc : 0 < Nat.card A := by
    have := hA.to_subtype
    exact Nat.card_pos
  have hIm : 0 < Nat.card (Φ '' X.noisyInputs R S A) := by
    have := (hI.image Φ).to_subtype
    exact Nat.card_pos
  have hA' : 0 < Nat.card A' := by
    obtain ⟨p, hp⟩ := hI
    have : Nonempty A' := ⟨⟨_, hland p hp⟩⟩
    exact Nat.card_pos
  have h1 := X.card_le_card_noisyInputs R S A
  have h2 := X.card_image_le R S A A' Φ hland
  have l1 : Real.log (Nat.card (X.cocyclesR R)) + Real.log (Nat.card (X.syndrome R '' S))
      + Real.log (Nat.card A) ≤ Real.log (Nat.card (X.noisyInputs R S A)) := by
    rw [← Real.log_mul (by positivity) (by positivity),
      ← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) (by exact_mod_cast h1)
  have l2 : Real.log (Nat.card (Φ '' X.noisyInputs R S A))
      ≤ Real.log (Nat.card (X.cocyclesR R)) + Real.log (Nat.card A') := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) (by exact_mod_cast h2)
  unfold erasure
  linarith

/-- **THE RATE LAW**: over `T` resets on a memory `M`, the total erasure
is at least `T · log |σ S|`, less what the memory can hold. -/
theorem sum_erasure_ge {M : Type*} [Finite M] (S : Set (G.E → R))
    (h0 : (0 : G.E → R) ∈ S) (A : ℕ → Set M) (hA : (A 0).Nonempty)
    (Φ : ℕ → (G.E → R) × M → X.cocyclesR R × M)
    (hland : ∀ t, ∀ p ∈ X.noisyInputs R S (A t), (Φ t p).2 ∈ A (t + 1)) (T : ℕ) :
    T * Real.log (Nat.card (X.syndrome R '' S)) + Real.log (Nat.card (A 0))
        - Real.log (Nat.card M)
      ≤ ∑ t ∈ Finset.range T, erasure (Φ t) (X.noisyInputs R S (A t)) := by
  have hne : ∀ t, (A t).Nonempty := by
    intro t
    induction t with
    | zero => exact hA
    | succ t ih =>
      obtain ⟨p, hp⟩ := X.noisyInputs_nonempty R h0 ih
      exact ⟨_, hland t p hp⟩
  have key : ∀ T : ℕ, T * Real.log (Nat.card (X.syndrome R '' S)) + Real.log (Nat.card (A 0))
      ≤ Real.log (Nat.card (A T))
        + ∑ t ∈ Finset.range T, erasure (Φ t) (X.noisyInputs R S (A t)) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      have := X.log_card_syndrome_add_le R S h0 (A T) (A (T + 1)) (hne T) (Φ T) (hland T)
      rw [Finset.sum_range_succ]
      push_cast
      linarith
  have hM : Real.log (Nat.card (A T)) ≤ Real.log (Nat.card M) := by
    have : 0 < Nat.card (A T) := by
      have := (hne T).to_subtype
      exact Nat.card_pos
    exact Real.log_le_log (by positivity)
      (by exact_mod_cast Nat.card_le_card_of_injective _ Subtype.val_injective)
  linarith [key T]

variable {X R}

/-- **The reset by a decoder**: correct, and leave memory untouched. -/
def Decoder.reset {M : Type*} (D : X.Decoder R) (p : (G.E → R) × M) :
    X.cocyclesR R × M :=
  ((D.recorder p.1).1, p.2)

/-- **Attainment**: a decoder's reset erases exactly `log |σ S|`. -/
theorem Decoder.erasure_reset {M : Type*} [Finite M] (D : X.Decoder R)
    (S : Set (G.E → R)) (h0 : (0 : G.E → R) ∈ S) (A : Set M) (hA : A.Nonempty) :
    erasure D.reset (X.noisyInputs R S A) = Real.log (Nat.card (X.syndrome R '' S)) := by
  have hlow := X.log_card_syndrome_add_le R S h0 A A hA D.reset fun p hp => hp.2
  have hIm : 0 < Nat.card (D.reset '' X.noisyInputs R S A) := by
    have := ((X.noisyInputs_nonempty R h0 hA).image D.reset).to_subtype
    exact Nat.card_pos
  have hS : 0 < Nat.card (X.syndrome R '' S) := by
    have : Nonempty (X.syndrome R '' S) := ⟨⟨_, 0, h0, rfl⟩⟩
    exact Nat.card_pos
  have hup : Nat.card (X.noisyInputs R S A)
      ≤ Nat.card (D.reset '' X.noisyInputs R S A) * Nat.card (X.syndrome R '' S) := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun p => (⟨D.reset p.1, p.1, p.2, rfl⟩, ⟨X.syndrome R p.1.1, ?_⟩)) ?_
    · obtain ⟨⟨x, s, hs, hxs⟩, _⟩ := p.2
      refine ⟨s, hs, ?_⟩
      rw [hxs, map_add, LinearMap.mem_ker.mp x.2, zero_add]
    · rintro ⟨⟨y, m⟩, _⟩ ⟨⟨y', m'⟩, _⟩ h
      have h1 := congrArg (fun q => (q.1 : X.cocyclesR R × M)) h
      have hσ : X.syndrome R y = X.syndrome R y' :=
        congrArg (fun q => (q.2 : X.Faces → R)) h
      have hx : y - D.decode (X.syndrome R y) = y' - D.decode (X.syndrome R y') :=
        congrArg (fun z : X.cocyclesR R × M => (z.1 : G.E → R)) h1
      have hm : m = m' := congrArg Prod.snd h1
      rw [hσ] at hx
      exact Subtype.ext (Prod.ext (sub_left_inj.mp hx) hm)
  have hup' : erasure D.reset (X.noisyInputs R S A) ≤ Real.log (Nat.card (X.syndrome R '' S)) := by
    unfold erasure
    have : Real.log (Nat.card (X.noisyInputs R S A))
        ≤ Real.log (Nat.card (D.reset '' X.noisyInputs R S A))
          + Real.log (Nat.card (X.syndrome R '' S)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      have hI : 0 < Nat.card (X.noisyInputs R S A) := by
        have := (X.noisyInputs_nonempty R h0 hA).to_subtype
        exact Nat.card_pos
      exact Real.log_le_log (by positivity) (by exact_mod_cast hup)
    linarith
  linarith

open Classical in
/-- **The price, split**: for an error set some decoder closes, the
error's log-count is at most the reset's erasure plus the gauge. -/
theorem Decoder.log_card_le_erasure_add_gauge {M : Type*} [Finite M] (D : X.Decoder R)
    (S : Finset (G.E → R)) (h0 : (0 : G.E → R) ∈ S)
    (hD : ∀ s ∈ S, D.residual s ∈ LinearMap.range (G.gradLin R)) (A : Set M)
    (hA : A.Nonempty) :
    Real.log S.card ≤ erasure D.reset (X.noisyInputs R (↑S) A)
      + Real.log (Nat.card (LinearMap.range (G.gradLin R))) := by
  rw [D.erasure_reset (↑S) h0 A hA]
  have hc := X.card_le_card_syndrome_mul_gauge R S
    ((X.exists_closing_decoder_iff R (↑S) h0).mp ⟨D, hD⟩)
  have hσ : Nat.card (X.syndrome R '' ↑S) = (S.image (X.syndrome R)).card := by
    rw [← Finset.coe_image]
    simp
  rw [hσ, ← Real.log_mul]
  · have hS : 0 < S.card := Finset.card_pos.mpr ⟨0, h0⟩
    exact Real.log_le_log (by exact_mod_cast hS) (by exact_mod_cast hc)
  · have : 0 < (S.image (X.syndrome R)).card := Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ h0⟩
    positivity
  · have : 0 < Nat.card (LinearMap.range (G.gradLin R)) := Nat.card_pos
    positivity

end TwoComplex

end Meno
