import Meno.DecodingGibbs

/-! # Records: correction that does not erase

A corrector that erases nothing reads the noisy state `y` and writes a
fine state together with a record into blank memory `K`, by an
injective `Φ : Y → X × K` (`recordStep`). Injectivity sends the noisy
states reachable from one fiber into the one fiber the closed step
lands in (`card_reach_le_card_fiber`), so the fiber size of the
observation on `X × K` is the capacity, and only memory inside the
fiber counts.

On the carrier, fine states are cocycles, the observation is the class
modulo exact cocycles, and errors come from `S`. The face's anchors:

* **The hidden bound** (`record_hidden_bound`): when the observation
  ignores the record, the record takes at least as many values as `S`
  meets gauge classes.
* **The visible collapse** (`record_visible_closed`): when the
  observation includes the record, a closed non-erasing step tolerates
  only pure-gauge errors — exactly the errorless law, the memory adding
  nothing.
* **Attainment** (`Decoder.recorder_injective`,
  `Decoder.recorder_closed`, `Decoder.card_records`): recording the
  syndrome and correcting by a decoder that closes `S` is injective,
  closed, and writes exactly as many records as `S` meets gauge
  classes.
* **The erasing alternative** (`Decoder.eraser_closed`,
  `Decoder.eraser_not_injective`): the same correction with a
  one-point record is closed, and is not injective once `S` meets two
  gauge classes. -/

namespace Meno

universe u

section Abstract

variable {X Y K O O' : Type*}

/-- **A recording step**: the noisy state `y` is read, and a fine state
together with a record is written by `Φ`. -/
def recordStep (n : X → Y → Prop) (Φ : Y → X × K) (x : X) (z : X × K) : Prop :=
  ∃ y, n x y ∧ Φ y = z

/-- **THE RECORD BOUND**: a non-erasing step closed over `π`, `π'` sends
the noisy states reachable from the fiber over `o` injectively into the
fiber over `g o`. -/
theorem card_reach_le_card_fiber [Finite X] [Finite K] (n : X → Y → Prop)
    {Φ : Y → X × K} (hΦ : Function.Injective Φ) (π : X → O) (π' : X × K → O')
    {g : O → O'} (hg : ∀ x z, recordStep n Φ x z → π' z = g (π x)) (o : O) :
    Nat.card {y // ∃ x, π x = o ∧ n x y} ≤ Nat.card {z // π' z = g o} := by
  refine Nat.card_le_card_of_injective (fun y => ⟨Φ y.1, ?_⟩) fun a b h => ?_
  · obtain ⟨x, hx, hn⟩ := y.2
    exact (hg _ _ ⟨_, hn, rfl⟩).trans (congrArg g hx)
  · exact Subtype.ext (hΦ (congrArg Subtype.val h))

end Abstract

namespace TwoComplex

variable {G : IncidenceGraph.{u}} (X : TwoComplex.{u} G) (R : Type u) [CommRing R]
  [Fintype R]

/-- **Cocycle noise**: a cocycle `x` is read as `x + s`, `s ∈ S`. -/
def cocycleNoise (S : Set (G.E → R)) (x : X.cocyclesR R) (y : G.E → R) : Prop :=
  ∃ s ∈ S, y = x + s

omit [Fintype R] in
/-- Exact cocycles are the gauge. -/
theorem card_exactR [Finite R] :
    Nat.card (X.exactR R) = Nat.card (LinearMap.range (G.gradLin R)) :=
  Nat.card_congr (Submodule.comapSubtypeEquivOfLe (X.range_grad_le_cocyclesR R)).toEquiv

omit [Fintype R] in
/-- Every class fiber of the cocycles is a copy of the gauge. -/
theorem card_classFiber [Finite R]
    (ξ : X.cocyclesR R ⧸ X.exactR R) :
    Nat.card {x : X.cocyclesR R // (X.exactR R).mkQ x = ξ}
      = Nat.card (LinearMap.range (G.gradLin R)) := by
  obtain ⟨x₀, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  have h := Nat.card_congr (fiberEquivKer (X.exactR R).mkQ x₀ rfl)
  rw [Submodule.ker_mkQ] at h
  rw [← X.card_exactR R]
  exact h

open Classical in
/-- **The reach of the zero class**: the gauge times the gauge classes
`S` meets, injected by `(b, ξ) ↦ b + rep ξ`. -/
theorem card_mul_le_card_reach (S : Set (G.E → R)) :
    Nat.card (LinearMap.range (G.gradLin R)) * Nat.card (gaugeMk R '' S)
      ≤ Nat.card {y // ∃ x, (X.exactR R).mkQ x = 0 ∧ X.cocycleNoise R S x y} := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p => ⟨(p.1 : G.E → R) + p.2.2.choose, ?_⟩) ?_
  · refine ⟨⟨p.1, X.range_grad_le_cocyclesR R p.1.2⟩, ?_,
      p.2.2.choose, p.2.2.choose_spec.1, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr p.1.2)
  · rintro ⟨b₁, ξ₁⟩ ⟨b₂, ξ₂⟩ h
    have hv : (b₁ : G.E → R) + ξ₁.2.choose = b₂ + ξ₂.2.choose := congrArg Subtype.val h
    have hξ : ξ₁ = ξ₂ := by
      refine Subtype.ext (ξ₁.2.choose_spec.2.symm.trans (Eq.trans ?_ ξ₂.2.choose_spec.2))
      refine (Submodule.Quotient.eq _).mpr ?_
      have : ξ₁.2.choose - ξ₂.2.choose = (b₂ : G.E → R) - b₁ := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm]
        exact hv
      rw [this]
      exact sub_mem b₂.2 b₁.2
    subst hξ
    rw [Subtype.ext (add_right_cancel hv)]

/-- **THE HIDDEN BOUND**: a non-erasing step, closed on classes with the
record unobserved, writes at least as many records as `S` meets gauge
classes. -/
theorem record_hidden_bound {K : Type*} [Finite K] (S : Set (G.E → R))
    {Φ : (G.E → R) → X.cocyclesR R × K} (hΦ : Function.Injective Φ)
    {g : X.cocyclesR R ⧸ X.exactR R → X.cocyclesR R ⧸ X.exactR R}
    (hg : ∀ x z, recordStep (X.cocycleNoise R S) Φ x z →
      (X.exactR R).mkQ z.1 = g ((X.exactR R).mkQ x)) :
    Nat.card (gaugeMk R '' S) ≤ Nat.card K := by
  have h2 := card_reach_le_card_fiber _ hΦ _ (fun z : X.cocyclesR R × K =>
    (X.exactR R).mkQ z.1) hg 0
  have h3 : Nat.card {z : X.cocyclesR R × K // (X.exactR R).mkQ z.1 = g 0}
      = Nat.card (LinearMap.range (G.gradLin R)) * Nat.card K := by
    rw [Nat.card_congr (Equiv.prodSubtypeFstEquivSubtypeProd
      (p := fun x => (X.exactR R).mkQ x = g 0)), Nat.card_prod,
      card_classFiber]
  exact Nat.le_of_mul_le_mul_left ((X.card_mul_le_card_reach R S).trans (h2.trans h3.le))
    Nat.card_pos

/-- **THE VISIBLE COLLAPSE**: a non-erasing step, closed on classes with
the record observed, tolerates only pure-gauge errors. -/
theorem record_visible_closed {K : Type*} [Finite K] (S : Set (G.E → R))
    (h0 : (0 : G.E → R) ∈ S) {Φ : (G.E → R) → X.cocyclesR R × K}
    (hΦ : Function.Injective Φ)
    {g : X.cocyclesR R ⧸ X.exactR R → (X.cocyclesR R ⧸ X.exactR R) × K}
    (hg : ∀ x z, recordStep (X.cocycleNoise R S) Φ x z →
      ((X.exactR R).mkQ z.1, z.2) = g ((X.exactR R).mkQ x)) :
    S ⊆ LinearMap.range (G.gradLin R) := by
  have h2 := card_reach_le_card_fiber _ hΦ _ (fun z : X.cocyclesR R × K =>
    ((X.exactR R).mkQ z.1, z.2)) hg 0
  have h3 : Nat.card {z : X.cocyclesR R × K // ((X.exactR R).mkQ z.1, z.2) = g 0}
      ≤ Nat.card (LinearMap.range (G.gradLin R)) * 1 := by
    rw [mul_one, ← X.card_classFiber R (g 0).1]
    refine Nat.card_le_card_of_injective (fun z => ⟨z.1.1, congrArg Prod.fst z.2⟩)
      fun a b h => Subtype.ext (Prod.ext (congrArg Subtype.val h)
        ((congrArg Prod.snd a.2).trans (congrArg Prod.snd b.2).symm))
  have h1 : Nat.card (gaugeMk R '' S) ≤ 1 :=
    Nat.le_of_mul_le_mul_left ((X.card_mul_le_card_reach R S).trans (h2.trans h3))
      Nat.card_pos
  have hsub := (Finite.card_le_one_iff_subsingleton.mp h1)
  intro s hs
  have := congrArg Subtype.val
    (hsub.elim ⟨gaugeMk R s, s, hs, rfl⟩ ⟨gaugeMk R 0, 0, h0, rfl⟩)
  simpa using (Submodule.Quotient.eq _).mp this

variable {X R}

/-- **The syndrome recorder**: correct by the decoder and write the
syndrome as the record. -/
def Decoder.recorder (D : X.Decoder R) (y : G.E → R) :
    X.cocyclesR R × (X.Faces → R) :=
  (⟨y - D.decode (X.syndrome R y),
    LinearMap.mem_ker.mpr (by rw [map_sub, D.syndrome_decode, sub_self])⟩,
    X.syndrome R y)

omit [Fintype R] in
/-- The syndrome recorder erases nothing. -/
theorem Decoder.recorder_injective (D : X.Decoder R) :
    Function.Injective D.recorder := by
  intro y y' h
  have hσ : X.syndrome R y = X.syndrome R y' := congrArg Prod.snd h
  have hx : y - D.decode (X.syndrome R y) = y' - D.decode (X.syndrome R y') :=
    congrArg (fun z => (z.1 : G.E → R)) h
  rw [hσ] at hx
  exact sub_left_inj.mp hx

omit [Fintype R] in
/-- **Attainment, closure**: with a decoder that closes `S`, the
syndrome recorder fixes every class. -/
theorem Decoder.recorder_closed (D : X.Decoder R) (S : Set (G.E → R))
    (hD : ∀ s ∈ S, D.residual s ∈ LinearMap.range (G.gradLin R)) :
    ∀ x z, recordStep (X.cocycleNoise R S) D.recorder x z →
      (X.exactR R).mkQ z.1 = (X.exactR R).mkQ x := by
  rintro x z ⟨y, ⟨s, hs, rfl⟩, rfl⟩
  refine (Submodule.Quotient.eq _).mpr (Submodule.mem_comap.mpr ?_)
  show (x : G.E → R) + s - D.decode (X.syndrome R (x + s)) - x
    ∈ LinearMap.range (G.gradLin R)
  rw [map_add, LinearMap.mem_ker.mp x.2, zero_add, add_sub_assoc, add_sub_cancel_left]
  exact hD s hs

omit [Fintype R] in
/-- **Attainment, count**: a decoder closing `S` writes exactly as many
syndromes on `S` as `S` meets gauge classes. -/
theorem Decoder.card_records (D : X.Decoder R) (S : Set (G.E → R))
    (hD : ∀ s ∈ S, D.residual s ∈ LinearMap.range (G.gradLin R)) :
    Nat.card (X.syndrome R '' S) = Nat.card (gaugeMk R '' S) := by
  have hcomp : X.syndrome R '' S = (LinearMap.range (G.gradLin R)).liftQ (X.syndrome R)
      (X.range_grad_le_cocyclesR R) '' (gaugeMk R '' S) := by
    rw [Set.image_image]
    rfl
  rw [hcomp]
  refine Nat.card_image_of_injOn ?_
  rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩ hσ
  have hσ' : X.syndrome R s = X.syndrome R s' := hσ
  refine (Submodule.Quotient.eq _).mpr ?_
  have := sub_mem (hD s hs) (hD s' hs')
  rwa [Decoder.residual, Decoder.residual, hσ', sub_sub_sub_cancel_right] at this

/-- **The eraser**: the same correction with a one-point record. -/
def Decoder.eraser (D : X.Decoder R) (y : G.E → R) : X.cocyclesR R × Unit :=
  ((D.recorder y).1, ())

omit [Fintype R] in
/-- **The erasing alternative, closure**: the eraser fixes every class
whenever its decoder closes `S`. -/
theorem Decoder.eraser_closed (D : X.Decoder R) (S : Set (G.E → R))
    (hD : ∀ s ∈ S, D.residual s ∈ LinearMap.range (G.gradLin R)) :
    ∀ x z, recordStep (X.cocycleNoise R S) D.eraser x z →
      (X.exactR R).mkQ z.1 = (X.exactR R).mkQ x := by
  rintro x z ⟨y, hn, rfl⟩
  exact D.recorder_closed S hD x _ ⟨y, hn, rfl⟩

/-- **The erasing alternative, erasure**: once `S` meets two gauge
classes, the eraser is not injective. -/
theorem Decoder.eraser_not_injective (D : X.Decoder R) (S : Set (G.E → R))
    (hD : ∀ s ∈ S, D.residual s ∈ LinearMap.range (G.gradLin R))
    (h2 : 1 < Nat.card (gaugeMk R '' S)) :
    ¬ Function.Injective D.eraser := fun hinj => by
  have := X.record_hidden_bound R S hinj (g := id) (D.eraser_closed S hD)
  have hu : Nat.card Unit = 1 := Nat.card_unique
  omega

end TwoComplex

end Meno
