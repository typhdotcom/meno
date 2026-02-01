import Meno.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-! # Log-Cardinality Instance

The unique non-trivial instance of the abstract complexity hierarchy:
C(A) = log|A|, valued in ℝ≥0∞. Finite nonempty types get log(|A|),
empty or infinite types get ⊤. -/

open scoped ENNReal

namespace SGD

universe u

/-- Log-cardinality complexity: log(|A|) for finite nonempty types, ⊤ otherwise. -/
noncomputable def logCard (A : Type u) : ℝ≥0∞ :=
  if Nat.card A = 0 then ⊤ else ENNReal.ofReal (Real.log (Nat.card A))

private lemma logCard_of_pos {A : Type u} (h : Nat.card A > 0) :
    logCard A = ENNReal.ofReal (Real.log (Nat.card A)) :=
  if_neg (by omega)

private lemma logCard_of_zero {A : Type u} (h : Nat.card A = 0) :
    logCard A = ⊤ :=
  if_pos h

private lemma logCard_unique (A : Type u) [Unique A] : logCard A = 0 := by
  rw [logCard_of_pos (by rw [Nat.card_unique]; omega)]
  simp [Real.log_one]

private lemma logCard_congr {A B : Type u} (e : A ≃ B) : logCard A = logCard B := by
  simp only [logCard, Nat.card_congr e]

private lemma logCard_prod_eq (A B : Type u) : logCard (A × B) = logCard A + logCard B := by
  simp only [logCard, Nat.card_prod]
  by_cases ha : Nat.card A = 0
  · simp [ha, top_add]
  by_cases hb : Nat.card B = 0
  · simp [hb, add_top]
  · have hab : Nat.card A * Nat.card B ≠ 0 := Nat.mul_ne_zero ha hb
    rw [if_neg hab, if_neg ha, if_neg hb,
        Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb),
        ENNReal.ofReal_add (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)]

private lemma logCard_sigma_le (D : Type u) (P : D → Type u) :
    logCard (Σ d, P d) ≤ logCard D + ⨆ (d : D), logCard (P d) := by
  by_cases hD : Nat.card D = 0
  · simp [logCard_of_zero hD, top_add]
  by_cases hfib : ∃ d, Nat.card (P d) = 0
  · have : ⨆ d, logCard (P d) = ⊤ := by
      obtain ⟨d₀, hd₀⟩ := hfib
      exact eq_top_iff.mpr (le_iSup_of_le d₀ (by rw [logCard_of_zero hd₀]))
    simp [this, add_top]
  push_neg at hfib
  have hD_pos : 0 < Nat.card D := Nat.pos_of_ne_zero hD
  have hfib_pos : ∀ d, 0 < Nat.card (P d) := fun d => Nat.pos_of_ne_zero (hfib d)
  haveI : Finite D := Nat.finite_of_card_ne_zero hD
  haveI : Fintype D := Fintype.ofFinite D
  haveI (d : D) : Finite (P d) := Nat.finite_of_card_ne_zero (hfib d)
  haveI : Nonempty D := Fintype.card_pos_iff.mp (by rw [← Nat.card_eq_fintype_card]; omega)
  have hS_pos : 0 < Nat.card (Σ d, P d) := by
    rw [Nat.card_sigma]
    exact Finset.sum_pos (fun d _ => hfib_pos d) ⟨Classical.arbitrary D, Finset.mem_univ _⟩
  rw [logCard_of_pos hS_pos, logCard_of_pos hD_pos]
  -- max fiber cardinality
  let hne : (Finset.univ : Finset D).Nonempty := ⟨Classical.arbitrary D, Finset.mem_univ _⟩
  let f : D → ℕ := fun d => Nat.card (P d)
  set M := Finset.univ.sup' hne f
  have hmax : ∀ d, f d ≤ M := fun d => Finset.le_sup' f (Finset.mem_univ d)
  have hM_pos : 0 < M := lt_of_lt_of_le (hfib_pos (Classical.arbitrary D)) (hmax _)
  -- Σ_d |P d| ≤ |D| * M
  have hsum_le : (∑ d : D, Nat.card (P d)) ≤ Fintype.card D * M :=
    Finset.sum_le_card_nsmul _ _ _ (fun d _ => hmax d)
  -- Nat.card (Σ d, P d) = ∑ d, Nat.card (P d), and this sum ≤ |D| * M
  rw [Nat.card_sigma]
  set S := ∑ d : D, Nat.card (P d)
  have hS_pos' : (0 : ℝ) < S := by
    exact_mod_cast Finset.sum_pos (fun d _ => hfib_pos d)
      ⟨Classical.arbitrary D, Finset.mem_univ _⟩
  rw [Nat.card_eq_fintype_card]
  have hlog_le : Real.log (S : ℝ) ≤ Real.log (Fintype.card D : ℝ) + Real.log (M : ℝ) := by
    have h1 : (S : ℝ) ≤ ↑(Fintype.card D) * (M : ℝ) := by exact_mod_cast hsum_le
    calc Real.log (S : ℝ)
        ≤ Real.log (↑(Fintype.card D) * (M : ℝ)) :=
          Real.log_le_log hS_pos' h1
      _ = Real.log (Fintype.card D : ℝ) + Real.log (M : ℝ) :=
          Real.log_mul (by exact_mod_cast Fintype.card_pos.ne') (by positivity)
  -- Lift to ℝ≥0∞
  apply le_trans (ENNReal.ofReal_le_ofReal hlog_le)
  rw [ENNReal.ofReal_add (Real.log_natCast_nonneg _) (by positivity : 0 ≤ Real.log (M : ℝ))]
  -- log M ≤ ⨆ d, logCard (P d)
  apply add_le_add (le_refl _)
  obtain ⟨d₀, _, hd₀⟩ := Finset.exists_mem_eq_sup' hne f
  -- hd₀ : M = Nat.card (P d₀)
  have : (M : ℝ) = ↑(Nat.card (P d₀)) := by exact_mod_cast hd₀
  rw [this, ← logCard_of_pos (hfib_pos d₀)]
  exact le_iSup (fun d => logCard (P d)) d₀

noncomputable instance : AdditiveComplexity ℝ≥0∞ where
  C := logCard
  unique_zero := logCard_unique
  congr := logCard_congr
  prod_le := fun A B => le_of_eq (logCard_prod_eq A B)
  sigma_le := logCard_sigma_le
  prod_eq := logCard_prod_eq

end SGD
