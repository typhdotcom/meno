import Meno.FundamentalPresentation
import Meno.ThetaHarmonic

/-! # Concrete Graph Topology: connectivity and Betti numbers (C1)

The concrete graphs' topological invariants, computed through the C1/C2
machinery instead of hand-built cycle bases:

* `cycleGraph_preconnected`, `cycleGraph_b1` — `C_n` is connected and
  has `b₁ = 1`, by walks and Euler's formula.
* **The genuine wedge** (`wedgeGraph`): `C_{n₁} ∨ C_{n₂}` on
  `n₁ + n₂ − 1` vertices — the C1 rebuild that retires the Phase-21
  spectator vertex. Connected (`wedgeGraph_preconnected`), and
  `b₁ = 2` (`wedgeGraph_b1`) — by Euler, with **no hand-built basis**:
  the fundamental presentation supplies the rank, connectivity
  supplies the component count, and the vertex count is genuinely
  `n₁ + n₂ − 1`.
* `cycleGraph_b1'`, `thetaGraph_b1` — rank corroborations through
  `IntegralCyclePresentation.r_eq_b1`: the hand-built presentations'
  ranks (1 and 2) equal the graphs' Betti numbers.

The spectator model (`wedgeSpectatorGraph`) remains in the tree until
C5 re-derives its consumers over this wedge; its `b₁` is also `2`
(`wedgeSpectatorGraph_b1`), which is exactly why its defect is the
*vertex count*, not the cycle count — Euler hides the spectator by
counting it as its own component. -/

namespace Meno

open scoped BigOperators

universe u v

/-! ## The cycle graph -/

theorem cycleGraph_preconnected (n : ℕ) (hn : 0 < n) :
    ∀ u v, (cycleGraph n hn).Reaches u v := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hbase : ∀ (m : ℕ) (hm : m < n),
      (cycleGraph n hn).Reaches ⟨0, hn⟩ ⟨m, hm⟩ := by
    intro m
    induction m with
    | zero => intro hm; exact ⟨.nil _⟩
    | succ k ih =>
      intro hm
      have hk : k < n := by omega
      have h1n : 1 < n := by omega
      have hadd : (⟨k, hk⟩ : Fin n) + 1 = ⟨k + 1, hm⟩ := by
        apply Fin.ext
        rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt h1n]
        exact Nat.mod_eq_of_lt hm
      rw [← hadd]
      obtain ⟨p⟩ := ih hk
      exact ⟨p.append
        (IncidenceGraph.Walk.consF (G := cycleGraph n hn)
          (⟨k, hk⟩ : Fin n) (.nil _))⟩
  intro u v
  obtain ⟨p⟩ := hbase u.val u.isLt
  obtain ⟨q⟩ := hbase v.val v.isLt
  exact ⟨p.reverse.append q⟩

/-- `b₁(C_n) = 1`, by Euler: `n − n + 1`. -/
theorem cycleGraph_b1 (n : ℕ) (hn : 0 < n) : (cycleGraph n hn).b1 = 1 := by
  have h := (cycleGraph n hn).b1_eq
  have hc : (cycleGraph n hn).componentCard = 1 :=
    (cycleGraph n hn).componentCard_eq_one ⟨⟨0, hn⟩⟩
      (cycleGraph_preconnected n hn)
  have hV : Fintype.card (cycleGraph n hn).V = n := Fintype.card_fin n
  have hE : Fintype.card (cycleGraph n hn).E = n := Fintype.card_fin n
  rw [hc] at h
  omega

/-- The hand-built cycle presentation's rank corroborates: `r = b₁`. -/
theorem cycleGraph_b1' (n : ℕ) (hn : 0 < n) : (cycleGraph n hn).b1 = 1 :=
  ((cycleIntegralPresentation n hn).r_eq_b1).symm.trans rfl

/-- The theta graph's Betti number is `2`: the hand-built rank-2
presentation meets the fundamental one through `r_eq_b1`. -/
theorem thetaGraph_b1 : thetaGraph.b1 = 2 :=
  (thetaIntegralPresentation.r_eq_b1).symm.trans rfl

/-- The spectator wedge's Betti number is also `2` — Euler counts the
spectator as its own component, which is exactly why the defect is
the vertex count, not the cycle count. -/
theorem wedgeSpectatorGraph_b1 (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    (wedgeSpectatorGraph n₁ n₂ h₁ h₂).b1 = 2 :=
  ((wedgeIntegralPresentation n₁ n₂ h₁ h₂).r_eq_b1).symm.trans rfl

/-! ## The genuine wedge -/

/-- Route the `j`-th vertex of an `m`-cycle into `Option (Fin (m−1))`:
the basepoint `0` goes to `none`, vertex `j ≠ 0` to `some (j − 1)`. -/
def wedgeRoute (m : ℕ) (j : Fin m) : Option (Fin (m - 1)) :=
  if h : j.val = 0 then none
  else some ⟨j.val - 1, by have := j.isLt; omega⟩

theorem wedgeRoute_zero (m : ℕ) [NeZero m] : wedgeRoute m 0 = none := by
  unfold wedgeRoute
  rw [dif_pos (Fin.val_zero m)]

theorem wedgeRoute_succ (m : ℕ) (k : ℕ) (hk : k + 1 < m) :
    wedgeRoute m ⟨k + 1, hk⟩ = some ⟨k, by omega⟩ := by
  unfold wedgeRoute
  rw [dif_neg (show ¬ ((⟨k + 1, hk⟩ : Fin m) : ℕ) = 0 by simp)]
  congr 1

/-- **The genuine wedge** `C_{n₁} ∨ C_{n₂}` (C1): both cycles share
the basepoint `none`; `n₁ + n₂ − 1` vertices, no spectator. -/
@[reducible] def wedgeGraph (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    IncidenceGraph :=
  haveI : NeZero n₁ := ⟨h₁.ne'⟩
  haveI : NeZero n₂ := ⟨h₂.ne'⟩
  { V := Option (Fin (n₁ - 1) ⊕ Fin (n₂ - 1))
    E := Fin n₁ ⊕ Fin n₂
    src := Sum.elim (fun j => (wedgeRoute n₁ j).map Sum.inl)
      (fun j => (wedgeRoute n₂ j).map Sum.inr)
    tgt := Sum.elim (fun j => (wedgeRoute n₁ (j + 1)).map Sum.inl)
      (fun j => (wedgeRoute n₂ (j + 1)).map Sum.inr) }

theorem wedgeGraph_card_V (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    Fintype.card (wedgeGraph n₁ n₂ h₁ h₂).V = n₁ + n₂ - 1 := by
  show Fintype.card (Option (Fin (n₁ - 1) ⊕ Fin (n₂ - 1))) = n₁ + n₂ - 1
  rw [Fintype.card_option, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin]
  omega

theorem wedgeGraph_card_E (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    Fintype.card (wedgeGraph n₁ n₂ h₁ h₂).E = n₁ + n₂ := by
  show Fintype.card (Fin n₁ ⊕ Fin n₂) = n₁ + n₂
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]

/-- The genuine wedge is connected: every vertex walks to the shared
basepoint along its own cycle. -/
theorem wedgeGraph_preconnected (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    ∀ u v, (wedgeGraph n₁ n₂ h₁ h₂).Reaches u v := by
  haveI : NeZero n₁ := ⟨h₁.ne'⟩
  haveI : NeZero n₂ := ⟨h₂.ne'⟩
  have hb₁ : ∀ (m : ℕ) (hm : m < n₁),
      (wedgeGraph n₁ n₂ h₁ h₂).Reaches none
        ((wedgeRoute n₁ ⟨m, hm⟩).map Sum.inl) := by
    intro m
    induction m with
    | zero =>
      intro hm
      rw [show (⟨0, hm⟩ : Fin n₁) = 0 from Fin.ext (by simp),
        wedgeRoute_zero]
      exact ⟨.nil _⟩
    | succ k ih =>
      intro hm
      have hk : k < n₁ := by omega
      have h1n : 1 < n₁ := by omega
      have hadd : (⟨k, hk⟩ : Fin n₁) + 1 = ⟨k + 1, hm⟩ := by
        apply Fin.ext
        rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt h1n]
        exact Nat.mod_eq_of_lt hm
      rw [← hadd]
      obtain ⟨p⟩ := ih hk
      exact ⟨p.append
        (IncidenceGraph.Walk.consF (G := wedgeGraph n₁ n₂ h₁ h₂)
          (Sum.inl (⟨k, hk⟩ : Fin n₁)) (.nil _))⟩
  have hb₂ : ∀ (m : ℕ) (hm : m < n₂),
      (wedgeGraph n₁ n₂ h₁ h₂).Reaches none
        ((wedgeRoute n₂ ⟨m, hm⟩).map Sum.inr) := by
    intro m
    induction m with
    | zero =>
      intro hm
      rw [show (⟨0, hm⟩ : Fin n₂) = 0 from Fin.ext (by simp),
        wedgeRoute_zero]
      exact ⟨.nil _⟩
    | succ k ih =>
      intro hm
      have hk : k < n₂ := by omega
      have h1n : 1 < n₂ := by omega
      have hadd : (⟨k, hk⟩ : Fin n₂) + 1 = ⟨k + 1, hm⟩ := by
        apply Fin.ext
        rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt h1n]
        exact Nat.mod_eq_of_lt hm
      rw [← hadd]
      obtain ⟨p⟩ := ih hk
      exact ⟨p.append
        (IncidenceGraph.Walk.consF (G := wedgeGraph n₁ n₂ h₁ h₂)
          (Sum.inr (⟨k, hk⟩ : Fin n₂)) (.nil _))⟩
  have hall : ∀ w : (wedgeGraph n₁ n₂ h₁ h₂).V,
      (wedgeGraph n₁ n₂ h₁ h₂).Reaches none w := by
    intro w
    rcases w with _ | (k | k)
    · exact ⟨.nil _⟩
    · have hk1 : k.val + 1 < n₁ := by have := k.isLt; omega
      have h := hb₁ (k.val + 1) hk1
      rw [wedgeRoute_succ n₁ k.val hk1] at h
      exact h
    · have hk1 : k.val + 1 < n₂ := by have := k.isLt; omega
      have h := hb₂ (k.val + 1) hk1
      rw [wedgeRoute_succ n₂ k.val hk1] at h
      exact h
  intro u v
  obtain ⟨p⟩ := hall u
  obtain ⟨q⟩ := hall v
  exact ⟨p.reverse.append q⟩

/-- **`b₁(C_{n₁} ∨ C_{n₂}) = 2` on the genuine wedge** (the C1
acceptance number): Euler's formula on `n₁ + n₂` edges,
`n₁ + n₂ − 1` vertices, one component — no hand-built basis, no
spectator. -/
theorem wedgeGraph_b1 (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    (wedgeGraph n₁ n₂ h₁ h₂).b1 = 2 := by
  have h := (wedgeGraph n₁ n₂ h₁ h₂).b1_eq
  have hc : (wedgeGraph n₁ n₂ h₁ h₂).componentCard = 1 :=
    (wedgeGraph n₁ n₂ h₁ h₂).componentCard_eq_one ⟨none⟩
      (wedgeGraph_preconnected n₁ n₂ h₁ h₂)
  rw [hc, wedgeGraph_card_V n₁ n₂ h₁ h₂, wedgeGraph_card_E n₁ n₂ h₁ h₂] at h
  omega

end Meno
