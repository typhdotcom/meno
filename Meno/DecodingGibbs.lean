import Meno.DecodingCost

/-! # Correction under fully supported noise

The capacity law (`card_le_card_syndrome_mul_gauge`) needs the error
set to be closable, and a fully supported error law never is: every
error of the distance's weight has positive mass. Under such noise the
class step is one-valued only with some probability, and the price
splits three ways.

Factor the syndrome through the gauge quotient `π`:
`σ = σ̄ ∘ π`, where `σ̄` reads the syndrome of a gauge class.

* **THE ERROR-ENTROPY SPLIT** (`entropy_split`):
  `H(P) = H(σ_*P) + H(π_*P | σ̄) + H(P | π)` — syndrome information,
  the **logical entropy** (which class, given the syndrome), and the
  gauge term.
* **The gauge bound** (`condEntropy_gauge_le`): on a fully supported
  law the gauge term is at most `log |gauge|`, strictly unless the law
  is uniform on gauge cosets (`condEntropy_gauge_lt`).
* **The success law** (`successProb_eq_sum`, `successProb_le_ml`): a
  decoding rule guesses a class per syndrome; its success probability
  is the mass of the guessed classes, and the maximum-likelihood rule
  — a heaviest class in each syndrome fiber — beats every rule, in
  particular every decoder (`Decoder.successProb_eq`).
* **The boundary** (`Decoder.successProb_eq_one`,
  `logicalEntropy_eq_zero`): when a decoder closes the support, it
  succeeds with probability one and the logical entropy vanishes —
  the counting face is the zero-logical-entropy chart. -/

namespace Meno

open scoped BigOperators
open Classical

universe u

/-- **Zero conditional entropy on an injective support**: if `f`
separates the points of positive mass, knowing `f x` determines `x`. -/
theorem FinDist.condEntropy_eq_zero_of_injOn {X D : Type u} [Fintype X] [Fintype D]
    [DecidableEq D] (f : X → D) (P : FinDist X)
    (h : ∀ x y, 0 < P.mass x → 0 < P.mass y → f x = f y → x = y) :
    P.condEntropy f = 0 := by
  unfold FinDist.condEntropy
  rw [neg_eq_zero]
  refine Finset.sum_eq_zero fun x _ => ?_
  rcases eq_or_lt_of_le (P.nonneg x) with h0 | hp
  · rw [← h0, zero_mul]
  · have hmap : (P.map f).mass (f x) = P.mass x := by
      show ∑ y ∈ Finset.univ.filter (fun y => f y = f x), P.mass y = P.mass x
      refine Finset.sum_eq_single_of_mem x (by simp) fun y hy hyx => ?_
      rcases eq_or_lt_of_le (P.nonneg y) with h0 | hpy
      · exact h0.symm
      · exact absurd (h y x hpy hp (Finset.mem_filter.mp hy).2) hyx
    rw [hmap, div_self hp.ne', Real.log_one, mul_zero]

variable {G : IncidenceGraph.{u}}

namespace TwoComplex

variable (X : TwoComplex.{u} G) (R : Type u) [CommRing R] [Fintype R]
  [Fintype X.Faces]

/-- The gauge quotient map. -/
noncomputable abbrev gaugeMk : (G.E → R) → (G.E → R) ⧸ LinearMap.range (G.gradLin R) :=
  (LinearMap.range (G.gradLin R)).mkQ

/-- **The syndrome of a gauge class**: gradients have zero syndrome, so
the syndrome descends to the gauge quotient. -/
noncomputable def classSyndrome :
    (G.E → R) ⧸ LinearMap.range (G.gradLin R) → (X.Faces → R) :=
  (LinearMap.range (G.gradLin R)).liftQ (X.syndrome R) (X.range_grad_le_cocyclesR R)

omit [Fintype R] [Fintype X.Faces] in
theorem classSyndrome_mk (s : G.E → R) :
    X.classSyndrome R (gaugeMk R s) = X.syndrome R s := rfl

omit [Fintype R] [Fintype X.Faces] in
theorem classSyndrome_comp : X.classSyndrome R ∘ gaugeMk R = X.syndrome R := rfl

/-- **The logical entropy**: the uncertainty of the gauge class once
the syndrome is known. -/
noncomputable def logicalEntropy (P : FinDist (G.E → R)) : ℝ :=
  (P.map (gaugeMk R)).condEntropy (X.classSyndrome R)

/-- **THE ERROR-ENTROPY SPLIT**: error entropy is syndrome entropy plus
logical entropy plus the gauge term. -/
theorem entropy_split (P : FinDist (G.E → R)) :
    P.entropy = (P.map (X.syndrome R)).entropy + X.logicalEntropy R P
      + P.condEntropy (gaugeMk R) := by
  have h1 := FinDist.entropy_eq_map_add_condEntropy (gaugeMk R) P
  have h2 := FinDist.entropy_eq_map_add_condEntropy (X.classSyndrome R) (P.map (gaugeMk R))
  rw [← FinDist.map_comp, classSyndrome_comp] at h2
  rw [logicalEntropy]
  linarith

omit [Fintype R] in
/-- Every gauge fiber is a copy of the gauge. -/
theorem card_gaugeFiber (ξ : (G.E → R) ⧸ LinearMap.range (G.gradLin R)) :
    Nat.card {x : G.E → R // gaugeMk R x = ξ}
      = Nat.card (LinearMap.range (G.gradLin R)) := by
  obtain ⟨x₀, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  have h := Nat.card_congr (fiberEquivKer
    (LinearMap.range (G.gradLin R)).mkQ x₀ rfl)
  rwa [Submodule.ker_mkQ] at h

/-- **The gauge bound**: on a fully supported law the gauge term is at
most `log |gauge|`. -/
theorem condEntropy_gauge_le (P : FinDist (G.E → R)) (hP : P.FullSupport) :
    P.condEntropy (gaugeMk R) ≤ Real.log (Nat.card (LinearMap.range (G.gradLin R))) :=
  FinDist.condEntropy_le_log _ Nat.card_pos (card_gaugeFiber R) P hP

/-- **The strict gauge bound**: strict unless the law is uniform on
gauge cosets. -/
theorem condEntropy_gauge_lt (P : FinDist (G.E → R)) (hP : P.FullSupport)
    (hne : P ≠ (P.map (gaugeMk R)).uniformLift (gaugeMk R) Nat.card_pos
      (card_gaugeFiber R)) :
    P.condEntropy (gaugeMk R) < Real.log (Nat.card (LinearMap.range (G.gradLin R))) :=
  FinDist.condEntropy_lt_log _ Nat.card_pos (card_gaugeFiber R) P hP hne

/-- **The success probability** of a decoding rule — a gauge-class
guess for each syndrome: the mass of the errors whose class it
guesses. -/
noncomputable def successProb (P : FinDist (G.E → R))
    (g : (X.Faces → R) → (G.E → R) ⧸ LinearMap.range (G.gradLin R)) : ℝ :=
  ∑ s, P.mass s * if gaugeMk R s = g (X.syndrome R s) then 1 else 0

/-- **The success law**: a rule succeeds with the mass of each guessed
class that carries its syndrome. -/
theorem successProb_eq_sum (P : FinDist (G.E → R))
    (g : (X.Faces → R) → (G.E → R) ⧸ LinearMap.range (G.gradLin R)) :
    X.successProb R P g = ∑ τ, if X.classSyndrome R (g τ) = τ
      then (P.map (gaugeMk R)).mass (g τ) else 0 := by
  unfold successProb
  rw [← Finset.sum_fiberwise Finset.univ (X.syndrome R)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hterm : ∀ s ∈ Finset.univ.filter (fun s => X.syndrome R s = τ),
      (P.mass s * if gaugeMk R s = g (X.syndrome R s) then 1 else 0)
        = if gaugeMk R s = g τ then P.mass s else 0 := by
    intro s hs
    rw [(Finset.mem_filter.mp hs).2, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  split_ifs with hτ
  · show _ = ∑ y ∈ Finset.univ.filter (fun y => gaugeMk R y = g τ), P.mass y
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rw [← classSyndrome_mk, h, hτ]
  · refine Finset.sum_eq_zero fun s hs => absurd ?_ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    rw [← hs.2, classSyndrome_mk, hs.1]

/-- **The maximum-likelihood rule**: a heaviest gauge class in each
attained syndrome fiber. -/
noncomputable def mlRule (P : FinDist (G.E → R)) (τ : X.Faces → R) :
    (G.E → R) ⧸ LinearMap.range (G.gradLin R) :=
  if h : (Finset.univ.filter fun ξ => X.classSyndrome R ξ = τ).Nonempty then
    (Finset.exists_max_image _ (P.map (gaugeMk R)).mass h).choose
  else 0

/-- **ML optimality**: no decoding rule beats the maximum-likelihood
rule. -/
theorem successProb_le_ml (P : FinDist (G.E → R))
    (g : (X.Faces → R) → (G.E → R) ⧸ LinearMap.range (G.gradLin R)) :
    X.successProb R P g ≤ X.successProb R P (X.mlRule R P) := by
  rw [successProb_eq_sum, successProb_eq_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  split_ifs with hg hml hml
  · have hne : (Finset.univ.filter fun ξ => X.classSyndrome R ξ = τ).Nonempty :=
      ⟨g τ, by simpa using hg⟩
    have hspec := (Finset.exists_max_image _ (P.map (gaugeMk R)).mass hne).choose_spec
    have hmlv : X.mlRule R P τ
        = (Finset.exists_max_image _ (P.map (gaugeMk R)).mass hne).choose := dif_pos hne
    rw [hmlv]
    exact hspec.2 _ (by simpa using hg)
  · have hne : (Finset.univ.filter fun ξ => X.classSyndrome R ξ = τ).Nonempty :=
      ⟨g τ, by simpa using hg⟩
    have hspec := (Finset.exists_max_image _ (P.map (gaugeMk R)).mass hne).choose_spec
    have hmlv : X.mlRule R P τ
        = (Finset.exists_max_image _ (P.map (gaugeMk R)).mass hne).choose := dif_pos hne
    exact absurd (by rw [hmlv]; simpa using hspec.1) hml
  · exact (P.map (gaugeMk R)).nonneg _
  · exact le_rfl

omit [Fintype X.Faces] in
/-- **A decoder is a rule**: its success probability is the mass of the
errors it leaves with an exact residual. -/
theorem Decoder.successProb_eq (D : X.Decoder R) (P : FinDist (G.E → R)) :
    X.successProb R P (gaugeMk R ∘ D.decode)
      = ∑ s, P.mass s *
          if D.residual s ∈ LinearMap.range (G.gradLin R) then 1 else 0 := by
  unfold successProb
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  refine if_congr ?_ rfl rfl
  exact Submodule.Quotient.eq _

omit [Fintype X.Faces] in
/-- **The boundary**: a decoder closing the support succeeds with
probability one. -/
theorem Decoder.successProb_eq_one (D : X.Decoder R) (P : FinDist (G.E → R))
    (hD : ∀ s, 0 < P.mass s → D.residual s ∈ LinearMap.range (G.gradLin R)) :
    X.successProb R P (gaugeMk R ∘ D.decode) = 1 := by
  rw [D.successProb_eq]
  refine (Finset.sum_congr rfl fun s _ => ?_).trans P.sum_one
  rcases eq_or_lt_of_le (P.nonneg s) with h0 | hp
  · rw [← h0, zero_mul]
  · rw [if_pos (hD s hp), mul_one]

/-- **The boundary, in entropy**: a decoder closing the support leaves
no logical entropy — the counting face is this chart. -/
theorem logicalEntropy_eq_zero (D : X.Decoder R) (P : FinDist (G.E → R))
    (hD : ∀ s, 0 < P.mass s → D.residual s ∈ LinearMap.range (G.gradLin R)) :
    X.logicalEntropy R P = 0 := by
  refine FinDist.condEntropy_eq_zero_of_injOn _ _ fun ξ ξ' hξ hξ' hσ => ?_
  have hpos : ∀ ξ, 0 < (P.map (gaugeMk R)).mass ξ →
      ∃ s, gaugeMk R s = ξ ∧ 0 < P.mass s := by
    intro ξ hξ
    by_contra hall
    push Not at hall
    refine absurd hξ (not_lt.mpr (Finset.sum_nonpos fun s hs => ?_))
    exact le_of_eq (le_antisymm (hall s (Finset.mem_filter.mp hs).2) (P.nonneg s))
  obtain ⟨s, rfl, hs⟩ := hpos ξ hξ
  obtain ⟨s', rfl, hs'⟩ := hpos ξ' hξ'
  rw [classSyndrome_mk, classSyndrome_mk] at hσ
  refine (Submodule.Quotient.eq _).mpr ?_
  have := sub_mem (hD s hs) (hD s' hs')
  rwa [Decoder.residual, Decoder.residual, hσ, sub_sub_sub_cancel_right] at this

end TwoComplex

end Meno
