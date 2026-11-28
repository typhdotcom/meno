import Meno.Decoding
import Meno.ResolutionCount

/-! # The price of a corrected step

The corrected step `(ω, s) ↦ ω + (s − D(σ s))` forgets the error.
Every output's fiber is a copy of the error set
(`Decoder.recoveryCost_correctedMap`): recovering the input costs
`log |S|`. When the step is closed on classes, that price is bounded
by what the syndrome reports plus the gauge — the class term never
enters.

* **The decoder-free closure law** (`exists_closing_decoder_iff`): a
  decoder with every residual exact exists iff errors of equal
  syndrome differ by gauge.
* **THE CAPACITY LAW** (`card_le_card_syndrome_mul_gauge`,
  `card_eq_iff_saturated`): a closable error set satisfies
  `|S| ≤ |σ S| · |gauge|`, with equality iff `S` is gauge-saturated.
* **The price** (`Decoder.recoveryCost_le`, `Decoder.recoveryCost_eq_iff`):
  the closed step's recovery cost is at most
  `log |σ S| + log |gauge|`, exact iff saturated; at resolution `q`
  the gauge term is K2's, `(|E| − b₁) · log q`
  (`Decoder.recoveryCost_le_resolution`).
* **The strictness witness** (`cylinder_recoveryCost_lt`): single
  errors on the cylinder are not gauge-saturated; their price falls
  strictly below the bound.
* **The boundary witness** (`gaugeErrors_card_eq`): pure-gauge
  error sets attain it. -/

namespace Meno

open scoped BigOperators

universe u

variable {G : IncidenceGraph.{u}}

namespace TwoComplex

variable (X : TwoComplex.{u} G) (R : Type*) [CommRing R]

/-- **The decoder-free closure law**: some decoder leaves every
residual exact iff errors of equal syndrome differ by gauge. -/
theorem exists_closing_decoder_iff (S : Set (G.E → R)) (h0 : (0 : G.E → R) ∈ S) :
    (∃ D : X.Decoder R, ∀ s ∈ S, D.residual s ∈ LinearMap.range (G.gradLin R)) ↔
      ∀ s ∈ S, ∀ s' ∈ S, X.syndrome R s = X.syndrome R s' →
        s - s' ∈ LinearMap.range (G.gradLin R) := by
  classical
  constructor
  · rintro ⟨D, hD⟩ s hs s' hs' hσ
    have := sub_mem (hD s hs) (hD s' hs')
    rwa [Decoder.residual, Decoder.residual, hσ, sub_sub_sub_cancel_right] at this
  · intro h
    refine ⟨⟨fun τ => if τ = 0 then 0 else
        if hs : ∃ s ∈ S, X.syndrome R s = τ then hs.choose
        else if hc : ∃ c, X.syndrome R c = τ then hc.choose else 0,
      fun c => ?_, ite_eq_left rfl⟩, fun s hs => ?_⟩
    · by_cases hz : X.syndrome R c = 0
      · rw [ite_eq_left hz, map_zero, hz]
      · rw [ite_eq_right hz]
        split_ifs with hs hc'
        · exact hs.choose_spec.2
        · exact hc'.choose_spec
        · exact absurd ⟨c, rfl⟩ hc'
    · show s - (if X.syndrome R s = 0 then 0 else _) ∈ _
      by_cases hz : X.syndrome R s = 0
      · rw [ite_eq_left hz, sub_zero]
        have := h s hs 0 h0 (by rw [hz, map_zero])
        rwa [sub_zero] at this
      · have hs' : ∃ s' ∈ S, X.syndrome R s' = X.syndrome R s := ⟨s, hs, rfl⟩
        rw [ite_eq_right hz, dite_eq_left hs']
        exact h s hs _ hs'.choose_spec.1 hs'.choose_spec.2.symm

variable {X R}

/-- **The corrected step as a map**: a cocycle and an error go to the
corrected cocycle. -/
def Decoder.correctedMap (D : X.Decoder R) (S : Set (G.E → R)) :
    X.cocyclesR R × S → X.cocyclesR R :=
  fun p => p.1 + ⟨D.residual p.2, D.residual_mem p.2⟩

/-- **The price of the corrected step**: every fiber is a copy of the
error set, so recovering an input costs `log |S|`. -/
theorem Decoder.recoveryCost_correctedMap [Finite R] (D : X.Decoder R)
    (S : Set (G.E → R)) (z : X.cocyclesR R) :
    recoveryCost (D.correctedMap S) z = Real.log (Nat.card S) := by
  unfold recoveryCost
  congr 2
  refine Nat.card_congr
    { toFun := fun p => p.1.2
      invFun := fun s => ⟨(z - ⟨D.residual s, D.residual_mem s⟩, s), by
        show (z - _) + _ = z
        exact sub_add_cancel _ _⟩
      left_inv := fun p => ?_
      right_inv := fun _ => rfl }
  have hp : p.1.1 + ⟨D.residual p.1.2, D.residual_mem p.1.2⟩ = z := p.2
  refine Subtype.ext (Prod.ext ?_ rfl)
  exact (eq_sub_of_add_eq hp).symm

variable (X R) [Fintype R]

/-- A syndrome fiber of a closable error set injects into the gauge. -/
theorem card_fiber_le_gauge (S : Finset (G.E → R))
    (h : ∀ s ∈ S, ∀ s' ∈ S, X.syndrome R s = X.syndrome R s' →
      s - s' ∈ LinearMap.range (G.gradLin R))
    {s₀ : G.E → R} (hs₀ : s₀ ∈ S) [DecidableEq (X.Faces → R)] :
    (S.filter fun s => X.syndrome R s = X.syndrome R s₀).card
      ≤ Nat.card (LinearMap.range (G.gradLin R)) := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_le_card_of_injective
    (fun x => ⟨x.1 - s₀, h _ (Finset.mem_filter.mp x.2).1 _ hs₀
      (Finset.mem_filter.mp x.2).2⟩) fun x y hxy => ?_
  exact Subtype.ext (sub_left_injective (congrArg Subtype.val hxy))

/-- **THE CAPACITY LAW**: a closable error set is at most its syndrome
count times the gauge. -/
theorem card_le_card_syndrome_mul_gauge (S : Finset (G.E → R))
    [DecidableEq (X.Faces → R)]
    (h : ∀ s ∈ S, ∀ s' ∈ S, X.syndrome R s = X.syndrome R s' →
      s - s' ∈ LinearMap.range (G.gradLin R)) :
    S.card ≤ (S.image (X.syndrome R)).card * Nat.card (LinearMap.range (G.gradLin R)) := by
  rw [Finset.card_eq_sum_card_image (X.syndrome R) S, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun τ hτ => ?_
  obtain ⟨s₀, hs₀, rfl⟩ := Finset.mem_image.mp hτ
  exact X.card_fiber_le_gauge R S h hs₀

/-- **The boundary of the capacity law**: equality iff the error set is
gauge-saturated — closed under adding any gradient. -/
theorem card_eq_iff_saturated (S : Finset (G.E → R)) [DecidableEq (X.Faces → R)]
    (h : ∀ s ∈ S, ∀ s' ∈ S, X.syndrome R s = X.syndrome R s' →
      s - s' ∈ LinearMap.range (G.gradLin R)) :
    S.card = (S.image (X.syndrome R)).card * Nat.card (LinearMap.range (G.gradLin R)) ↔
      ∀ s ∈ S, ∀ b ∈ LinearMap.range (G.gradLin R), s + b ∈ S := by
  have hb0 : ∀ b ∈ LinearMap.range (G.gradLin R), X.syndrome R b = 0 :=
    fun b hb => X.range_grad_le_cocyclesR R hb
  rw [Finset.card_eq_sum_card_image (X.syndrome R) S, ← smul_eq_mul, ← Finset.sum_const,
    Finset.sum_eq_sum_iff_of_le fun τ hτ => by
      obtain ⟨s₀, hs₀, rfl⟩ := Finset.mem_image.mp hτ
      exact X.card_fiber_le_gauge R S h hs₀]
  constructor
  · intro heq s hs b hb
    have hcard := heq _ (Finset.mem_image_of_mem _ hs)
    rw [← Nat.card_eq_finsetCard] at hcard
    have hinj : Function.Injective (fun x : S.filter (fun s' => X.syndrome R s' = X.syndrome R s) =>
        (⟨x.1 - s, h _ (Finset.mem_filter.mp x.2).1 _ hs (Finset.mem_filter.mp x.2).2⟩ :
          LinearMap.range (G.gradLin R))) :=
      fun x y hxy => Subtype.ext (sub_left_injective (congrArg Subtype.val hxy))
    obtain ⟨x, hx⟩ := (hinj.bijective_of_nat_card_le hcard.ge).2 ⟨b, hb⟩
    have hxb : x.1 - s = b := congrArg Subtype.val hx
    rw [← hxb, add_sub_cancel]
    exact (Finset.mem_filter.mp x.2).1
  · intro hsat τ hτ
    obtain ⟨s₀, hs₀, rfl⟩ := Finset.mem_image.mp hτ
    refine le_antisymm (X.card_fiber_le_gauge R S h hs₀) ?_
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective
      (fun b => ⟨s₀ + b.1, Finset.mem_filter.mpr ⟨hsat s₀ hs₀ b.1 b.2, by
        rw [map_add, hb0 b.1 b.2, add_zero]⟩⟩) fun x y hxy => ?_
    exact Subtype.ext (add_left_cancel (congrArg Subtype.val hxy))

variable {X R}

/-- **THE PRICE BOUND**: a closed corrected step costs at most the
syndrome count plus the gauge, in logs. -/
theorem Decoder.recoveryCost_le (D : X.Decoder R) (S : Finset (G.E → R))
    [DecidableEq (X.Faces → R)] (h0 : (0 : G.E → R) ∈ S)
    (hD : ∀ s ∈ S, D.residual s ∈ LinearMap.range (G.gradLin R)) (z : X.cocyclesR R) :
    recoveryCost (D.correctedMap ↑S) z
      ≤ Real.log (S.image (X.syndrome R)).card
        + Real.log (Nat.card (LinearMap.range (G.gradLin R))) := by
  have h := (X.exists_closing_decoder_iff R ↑S h0).mp ⟨D, hD⟩
  rw [D.recoveryCost_correctedMap, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    ← Real.log_mul (by exact_mod_cast
        (Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ h0⟩).ne')
      (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]
  have hpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr ⟨0, h0⟩
  refine Real.log_le_log hpos ?_
  exact_mod_cast X.card_le_card_syndrome_mul_gauge R S h

/-- **The price, exactly**: the bound is attained iff the error set is
gauge-saturated. -/
theorem Decoder.recoveryCost_eq_iff (D : X.Decoder R) (S : Finset (G.E → R))
    [DecidableEq (X.Faces → R)] (h0 : (0 : G.E → R) ∈ S)
    (hD : ∀ s ∈ S, D.residual s ∈ LinearMap.range (G.gradLin R)) (z : X.cocyclesR R) :
    recoveryCost (D.correctedMap ↑S) z
        = Real.log (S.image (X.syndrome R)).card
          + Real.log (Nat.card (LinearMap.range (G.gradLin R))) ↔
      ∀ s ∈ S, ∀ b ∈ LinearMap.range (G.gradLin R), s + b ∈ S := by
  have h := (X.exists_closing_decoder_iff R ↑S h0).mp ⟨D, hD⟩
  have him : 0 < (S.image (X.syndrome R)).card :=
    Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ h0⟩
  rw [D.recoveryCost_correctedMap, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    ← Real.log_mul (by exact_mod_cast him.ne') (Nat.cast_ne_zero.mpr Nat.card_pos.ne'),
    ← X.card_eq_iff_saturated R S h]
  constructor
  · intro heq
    have hS : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr ⟨0, h0⟩
    have hR : (0 : ℝ) < ((S.image (X.syndrome R)).card : ℝ)
        * (Nat.card (LinearMap.range (G.gradLin R)) : ℝ) := by
      have : (0 : ℝ) < Nat.card (LinearMap.range (G.gradLin R)) := by
        exact_mod_cast Nat.card_pos
      have : (0 : ℝ) < (S.image (X.syndrome R)).card := by exact_mod_cast him
      positivity
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr hS) (Set.mem_Ioi.mpr hR) heq
    exact_mod_cast this
  · intro heq
    rw [heq, Nat.cast_mul]

/-- **The price at resolution `q`**: the gauge term is K2's,
`(|E| − b₁) · log q`; the class term `b₁ · log q` never enters. -/
theorem Decoder.recoveryCost_le_resolution {n : ℕ}
    (Bas : Module.Basis (Fin n) ℤ G.cycleLattice) (q : ℕ) [NeZero q]
    {X : TwoComplex.{u} G} (D : X.Decoder (ZMod q)) (S : Finset (G.E → ZMod q))
    [DecidableEq (X.Faces → ZMod q)] (h0 : (0 : G.E → ZMod q) ∈ S)
    (hD : ∀ s ∈ S, D.residual s ∈ LinearMap.range (G.gradLin (ZMod q)))
    (z : X.cocyclesR (ZMod q)) :
    recoveryCost (D.correctedMap ↑S) z
      ≤ Real.log (S.image (X.syndrome (ZMod q))).card
        + ((Fintype.card G.E - n : ℕ) : ℝ) * Real.log q := by
  have := D.recoveryCost_le S h0 hD z
  rwa [G.card_gauge Bas q, Nat.cast_pow, Real.log_pow] at this

end TwoComplex

/-! ## The witnesses -/

open Classical in
/-- **THE STRICTNESS WITNESS**: on the cylinder over `ZMod 2`, single
errors are corrected, but a gradient of weight `3` leaves the error
set — the price falls strictly below syndrome plus gauge. -/
theorem cylinder_recoveryCost_lt :
    ∃ D : cylinderComplex.Decoder (ZMod 2), ∀ z,
      recoveryCost (D.correctedMap
          ↑(Finset.univ.filter fun s : Fin 15 → ZMod 2 => hammingNorm s ≤ 1)) z
        < Real.log ((Finset.univ.filter fun s : Fin 15 → ZMod 2 => hammingNorm s ≤ 1).image
            (cylinderComplex.syndrome (ZMod 2))).card
          + Real.log (Nat.card (LinearMap.range (cylinderGraph.gradLin (ZMod 2)))) := by
  set S := Finset.univ.filter fun s : Fin 15 → ZMod 2 => hammingNorm s ≤ 1
  have h0 : (0 : Fin 15 → ZMod 2) ∈ S := by simp [S, hammingNorm_zero]
  obtain ⟨D, hD⟩ := cylinder_decodable_one
  have hres : ∀ s ∈ S, D.residual s ∈ LinearMap.range (cylinderGraph.gradLin (ZMod 2)) :=
    fun s hs => (D.corrected_closed_iff {s | hammingNorm s ≤ 1}
      (by simp [hammingNorm_zero])).mp hD s (by simpa [S] using hs)
  refine ⟨D, fun z => lt_of_le_of_ne (D.recoveryCost_le S h0 hres z) fun heq => ?_⟩
  have hsat := (D.recoveryCost_eq_iff S h0 hres z).mp heq
  have hb : cylinderGraph.grad (Pi.single (0 : Fin 9) (1 : ZMod 2))
      ∈ LinearMap.range (cylinderGraph.gradLin (ZMod 2)) := ⟨_, rfl⟩
  have hw : hammingNorm (cylinderGraph.grad (Pi.single (0 : Fin 9) (1 : ZMod 2))) = 3 := by
    decide
  have := hsat 0 h0 _ hb
  simp only [S, zero_add, Finset.mem_filter, Finset.mem_univ, true_and, hw] at this
  omega

open Classical in
/-- **THE BOUNDARY WITNESS**: pure-gauge errors attain the capacity law
— one syndrome, a full gauge coset. -/
theorem gaugeErrors_card_eq (X : TwoComplex.{u} G) (R : Type*) [CommRing R] [Fintype R] :
    (Finset.univ.filter (· ∈ LinearMap.range (G.gradLin R))).card
      = ((Finset.univ.filter (· ∈ LinearMap.range (G.gradLin R))).image
          (X.syndrome R)).card * Nat.card (LinearMap.range (G.gradLin R)) := by
  refine (X.card_eq_iff_saturated R _ fun s hs s' hs' _ => ?_).mpr fun s hs b hb => ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs hs'
    exact sub_mem hs hs'
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact add_mem hs hb

end Meno
