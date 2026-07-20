import Meno.GraphHomology
import Meno.ThetaGraph

/-! # Concrete Graph Topology: connectivity, Betti numbers, bases (C1/C5)

The concrete graphs' topological invariants and their **lattice
bases**, all through the pure graph-homology layer — this file imports
only `Meno/GraphHomology.lean` and `Meno/ThetaGraph.lean`, so the
"unpriced topology" grouping of `Meno.lean` is true by the import DAG
(review #5, finding 1):

* `cycleGraph` — `C_n`, with `b₁ = 1` derived through its lattice
  basis (`cycleGraph_b1'`).
* **The genuine wedge** (`wedgeGraph`): `C_{n₁} ∨ C_{n₂}` on
  `n₁ + n₂ − 1` vertices — connected, `b₁ = 2` by Euler, with no
  spectator vertex.
* `thetaGraph_preconnected`, `thetaGraph_b1` — `K₂,₃` is connected and
  has `b₁ = 2`, by walks and Euler's formula.
* **The concrete lattice bases** (review #5, finding 2):
  `cycleLatticeBasis`, `thetaLatticeBasis`, `wedgeLatticeBasis` —
  genuine `Module.Basis _ ℤ G.cycleLattice` objects assembled by
  `IncidenceGraph.basisOfCycles` from raw closedness, independence,
  and integral-spanning facts. Their cardinalities re-derive each
  `b₁` through `card_eq_b1` (`cycleGraph_b1'`, `thetaGraph_b1'`,
  `wedgeGraph_b1'`), corroborating the Euler computations. -/

namespace Meno

open scoped BigOperators

universe u v

/-! ## The cycle graph -/


/-! ### The cycle graph's boundary and cycle facts

Stated through the substrate's single operator (review #3): the
boundary closed form over any commutative ring, constancy of closed
cochains, and the raw ingredients of the lattice basis. -/

/-- The cycle graph's boundary in closed form: inflow minus outflow —
over any commutative ring. -/
theorem cycleGraph_boundary_eq {R : Type*} [CommRing R]
    (n : ℕ) (hn : 0 < n) [NeZero n] (ω : Fin n → R) (v : Fin n) :
    (cycleGraph n hn).boundary ω v = ω (v - 1) - ω v := by
  show ∑ e : Fin n, ((if e + 1 = v then (1 : R) else 0)
    - (if e = v then (1 : R) else 0)) * ω e = ω (v - 1) - ω v
  rw [show (fun e : Fin n => ((if e + 1 = v then (1 : R) else 0)
      - (if e = v then (1 : R) else 0)) * ω e)
      = fun e => ((if e = v - 1 then ω e else 0) - if e = v then ω e else 0) from
    funext fun e => by
      by_cases h1 : e + 1 = v
      · have h1' : e = v - 1 := by rw [eq_sub_iff_add_eq]; exact h1
        by_cases h2 : e = v
        · rw [if_pos h1, if_pos h2, if_pos h1', if_pos h2]; ring
        · rw [if_pos h1, if_neg h2, if_pos h1', if_neg h2]; ring
      · have h1' : ¬(e = v - 1) := fun hc =>
          h1 (by rw [← eq_sub_iff_add_eq]; exact hc)
        by_cases h2 : e = v
        · rw [if_neg h1, if_pos h2, if_neg h1', if_pos h2]; ring
        · rw [if_neg h1, if_neg h2, if_neg h1', if_neg h2]; ring]
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ (v - 1) ω,
    Finset.sum_ite_eq' Finset.univ v ω]
  simp

/-- The integral basis cycle of `C_n`: the all-ones cochain. -/
def cycleCyclesZ (n : ℕ) : Fin 1 → Fin n → ℤ := fun _ _ => 1

/-- The all-ones cochain is an integral cycle. -/
theorem cycleCyclesZ_mem (n : ℕ) (hn : 0 < n) (i : Fin 1) :
    cycleCyclesZ n i ∈ (cycleGraph n hn).cycleLattice := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [IncidenceGraph.mem_cycleLattice]
  intro v
  rw [cycleGraph_boundary_eq]
  show (1 : ℤ) - 1 = 0
  ring

/-- **A closed cochain on `C_n` is constant**: flow conservation
around the cycle equalizes consecutive edges. -/
theorem eq_const_of_cycle_boundary_eq_zero (n : ℕ) (hn : 0 < n)
    [NeZero n] (ω : Fin n → ℝ)
    (h : ∀ v, (cycleGraph n hn).boundary ω v = 0) :
    ω = fun _ => ω 0 := by
  have hstep : ∀ v : Fin n, ω (v - 1) = ω v := by
    intro v
    have := h v
    rw [cycleGraph_boundary_eq] at this
    linarith
  have hsucc : ∀ v : Fin n, ω v = ω (v + 1) := fun v => by
    have := hstep (v + 1)
    rwa [add_sub_cancel_right] at this
  have hval : ∀ (m : ℕ) (hm : m < n), ω ⟨m, hm⟩ = ω 0 := by
    intro m
    induction m with
    | zero =>
      intro hm
      have h0 : (⟨0, hm⟩ : Fin n) = 0 := Fin.ext (by simp)
      rw [h0]
    | succ m ih =>
      intro hm
      have hm' : m < n := Nat.lt_of_succ_lt hm
      have hmk : (⟨m + 1, hm⟩ : Fin n) = ⟨m, hm'⟩ + 1 := by
        apply Fin.ext
        rw [Fin.val_add]
        have h1 : (1 : Fin n).val = 1 := by
          rw [Fin.val_one']
          exact Nat.mod_eq_of_lt (by omega)
        rw [h1]
        exact (Nat.mod_eq_of_lt hm).symm
      rw [hmk, ← hsucc ⟨m, hm'⟩]
      exact ih hm'
  funext e
  rw [show e = ⟨e.val, e.isLt⟩ from (Fin.eta e e.isLt).symm,
    hval e.val e.isLt]

/-- Independence of the cast all-ones cycle. -/
theorem cycle_cast_independent (n : ℕ) (hn : 0 < n) (x : Fin 1 → ℝ)
    (hx : (fun e => ∑ i, x i * ((cycleCyclesZ n i e : ℤ) : ℝ)) = 0) :
    x = 0 := by
  have h0 := congrFun hx ⟨0, hn⟩
  rw [Fin.sum_univ_one] at h0
  have hx0 : x 0 = 0 := by
    have : x 0 * ((1 : ℤ) : ℝ) = 0 := h0
    simpa using this
  funext i
  fin_cases i
  exact hx0

/-- **Integral spanning for `C_n`**: an integral cycle is a constant
integer multiple of the all-ones cycle. -/
theorem cycle_integral_spanning (n : ℕ) (hn : 0 < n) (x : Fin n → ℤ)
    (hx : x ∈ (cycleGraph n hn).cycleLattice) :
    ∃ a : Fin 1 → ℤ, x = fun e => ∑ i, a i * cycleCyclesZ n i e := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hclosed : ∀ v,
      (cycleGraph n hn).boundary (fun e => ((x e : ℤ) : ℝ)) v = 0 := by
    intro v
    rw [(cycleGraph n hn).boundary_castR,
      (IncidenceGraph.mem_cycleLattice _ |>.mp hx) v, Int.cast_zero]
  have hr := eq_const_of_cycle_boundary_eq_zero n hn
    (fun e => ((x e : ℤ) : ℝ)) hclosed
  refine ⟨![x 0], ?_⟩
  funext e
  apply Int.cast_injective (α := ℝ)
  have he := congrFun hr e
  rw [he]
  push_cast
  rw [Fin.sum_univ_one]
  show ((x 0 : ℤ) : ℝ) = ((x 0 : ℤ) : ℝ) * ((1 : ℤ) : ℝ)
  simp

/-- **The cycle graph's lattice basis**: the all-ones cycle, as a
genuine `ℤ`-basis of `H₁(C_n; ℤ)`. -/
noncomputable def cycleLatticeBasis (n : ℕ) (hn : 0 < n) :
    Module.Basis (Fin 1) ℤ (cycleGraph n hn).cycleLattice :=
  (cycleGraph n hn).basisOfCycles (cycleCyclesZ n)
    (cycleCyclesZ_mem n hn) (cycle_cast_independent n hn)
    (cycle_integral_spanning n hn)

/-- The basis's integer cycles are the all-ones family. -/
theorem cyclesZ_cycleLatticeBasis (n : ℕ) (hn : 0 < n) :
    (cycleGraph n hn).cyclesZ (cycleLatticeBasis n hn) = cycleCyclesZ n :=
  (cycleGraph n hn).cyclesZ_basisOfCycles _ _ _ _

/-- `b₁(C_n) = 1` **through the basis** — by `card_eq_b1`. -/
theorem cycleGraph_b1' (n : ℕ) (hn : 0 < n) : (cycleGraph n hn).b1 = 1 :=
  ((cycleGraph n hn).card_eq_b1 (cycleLatticeBasis n hn)).symm

/-! ## The theta graph -/

/-- The theta graph is connected: the junction `0` reaches every
vertex along its own path. -/
theorem thetaGraph_preconnected : ∀ u v, thetaGraph.Reaches u v := by
  have hbase : ∀ w : Fin 5, thetaGraph.Reaches 0 w := by
    intro w
    fin_cases w
    · exact ⟨.nil _⟩
    · exact ⟨IncidenceGraph.Walk.consF (G := thetaGraph) 0
        (IncidenceGraph.Walk.consF (G := thetaGraph) 1 (.nil _))⟩
    · exact ⟨IncidenceGraph.Walk.consF (G := thetaGraph) 0 (.nil _)⟩
    · exact ⟨IncidenceGraph.Walk.consF (G := thetaGraph) 2 (.nil _)⟩
    · exact ⟨IncidenceGraph.Walk.consF (G := thetaGraph) 4 (.nil _)⟩
  intro u v
  obtain ⟨p⟩ := hbase u
  obtain ⟨q⟩ := hbase v
  exact ⟨p.reverse.append q⟩

/-- **`b₁(K₂,₃) = 2`**, by Euler: `6 − 5 + 1` — topology only. -/
theorem thetaGraph_b1 : thetaGraph.b1 = 2 := by
  have h := thetaGraph.b1_eq
  have hc : thetaGraph.componentCard = 1 :=
    thetaGraph.componentCard_eq_one ⟨0⟩ thetaGraph_preconnected
  have hV : Fintype.card thetaGraph.V = 5 := by
    show Fintype.card (Fin 5) = 5
    simp
  have hE : Fintype.card thetaGraph.E = 6 := by
    show Fintype.card (Fin 6) = 6
    simp
  rw [hc, hV, hE] at h
  omega

/-- **The theta graph's lattice basis**: `c₁ = p₁ − p₃`,
`c₂ = p₂ − p₃`, as a genuine `ℤ`-basis of `H₁(K₂,₃; ℤ)` — assembled
from the raw facts of `Meno/ThetaGraph.lean`. -/
noncomputable def thetaLatticeBasis :
    Module.Basis (Fin 2) ℤ thetaGraph.cycleLattice :=
  thetaGraph.basisOfCycles thetaCyclesZ thetaCyclesZ_mem
    theta_cast_independent theta_integral_spanning

/-- The basis's integer cycles are the theta cycles. -/
theorem cyclesZ_thetaLatticeBasis :
    thetaGraph.cyclesZ thetaLatticeBasis = thetaCyclesZ :=
  thetaGraph.cyclesZ_basisOfCycles _ _ _ _

/-- `b₁(K₂,₃) = 2` **through the basis** — corroborating the Euler
computation (`thetaGraph_b1`) by `card_eq_b1`. -/
theorem thetaGraph_b1' : thetaGraph.b1 = 2 :=
  (thetaGraph.card_eq_b1 thetaLatticeBasis).symm

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

/-! ### The wedge's lattice basis -/

/-- The wedge's integral basis cycles: all-ones on the left cycle's
edges, all-ones on the right cycle's edges. Disjoint supports. -/
def wedgeCyclesZ (n₁ n₂ : ℕ) : Fin 2 → Fin n₁ ⊕ Fin n₂ → ℤ :=
  ![Sum.elim (fun _ => 1) (fun _ => 0), Sum.elim (fun _ => 0) (fun _ => 1)]

/-- The wedge's indicator cycles are integral cycles: the boundary of
an indicator telescopes by the shift reindexing `j ↦ j + 1`. -/
theorem wedgeCyclesZ_mem (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂)
    (i : Fin 2) :
    wedgeCyclesZ n₁ n₂ i ∈ (wedgeGraph n₁ n₂ h₁ h₂).cycleLattice := by
  haveI : NeZero n₁ := ⟨h₁.ne'⟩
  haveI : NeZero n₂ := ⟨h₂.ne'⟩
  rw [IncidenceGraph.mem_cycleLattice]
  intro v
  fin_cases i
  · show (wedgeGraph n₁ n₂ h₁ h₂).boundary (wedgeCyclesZ n₁ n₂ 0) v = 0
    rw [IncidenceGraph.boundary_eq_sum, Fintype.sum_sum_type]
    have hL : ∀ j : Fin n₁,
        (wedgeGraph n₁ n₂ h₁ h₂).bcoeff v (Sum.inl j)
            * wedgeCyclesZ n₁ n₂ 0 (Sum.inl j)
          = (if (wedgeRoute n₁ (j + 1)).map Sum.inl = v then (1 : ℤ) else 0)
            - (if (wedgeRoute n₁ j).map Sum.inl = v then 1 else 0) := by
      intro j
      rw [show wedgeCyclesZ n₁ n₂ 0 (Sum.inl j) = 1 from rfl, mul_one]
      rfl
    have hR : ∀ j : Fin n₂,
        (wedgeGraph n₁ n₂ h₁ h₂).bcoeff v (Sum.inr j)
            * wedgeCyclesZ n₁ n₂ 0 (Sum.inr j) = 0 := by
      intro j
      rw [show wedgeCyclesZ n₁ n₂ 0 (Sum.inr j) = 0 from rfl, mul_zero]
    rw [Finset.sum_congr rfl fun j _ => hL j,
      Finset.sum_congr rfl fun j _ => hR j, Finset.sum_const_zero, add_zero,
      Finset.sum_sub_distrib]
    rw [Fintype.sum_equiv (Equiv.addRight (1 : Fin n₁))
      (fun j => if (wedgeRoute n₁ (j + 1)).map Sum.inl = v then (1 : ℤ) else 0)
      (fun j => if (wedgeRoute n₁ j).map Sum.inl = v then (1 : ℤ) else 0)
      (fun j => rfl)]
    exact sub_self _
  · show (wedgeGraph n₁ n₂ h₁ h₂).boundary (wedgeCyclesZ n₁ n₂ 1) v = 0
    rw [IncidenceGraph.boundary_eq_sum, Fintype.sum_sum_type]
    have hL : ∀ j : Fin n₁,
        (wedgeGraph n₁ n₂ h₁ h₂).bcoeff v (Sum.inl j)
            * wedgeCyclesZ n₁ n₂ 1 (Sum.inl j) = 0 := by
      intro j
      rw [show wedgeCyclesZ n₁ n₂ 1 (Sum.inl j) = 0 from rfl, mul_zero]
    have hR : ∀ j : Fin n₂,
        (wedgeGraph n₁ n₂ h₁ h₂).bcoeff v (Sum.inr j)
            * wedgeCyclesZ n₁ n₂ 1 (Sum.inr j)
          = (if (wedgeRoute n₂ (j + 1)).map Sum.inr = v then (1 : ℤ) else 0)
            - (if (wedgeRoute n₂ j).map Sum.inr = v then 1 else 0) := by
      intro j
      rw [show wedgeCyclesZ n₁ n₂ 1 (Sum.inr j) = 1 from rfl, mul_one]
      rfl
    rw [Finset.sum_congr rfl fun j _ => hL j,
      Finset.sum_congr rfl fun j _ => hR j, Finset.sum_const_zero, zero_add,
      Finset.sum_sub_distrib]
    rw [Fintype.sum_equiv (Equiv.addRight (1 : Fin n₂))
      (fun j => if (wedgeRoute n₂ (j + 1)).map Sum.inr = v then (1 : ℤ) else 0)
      (fun j => if (wedgeRoute n₂ j).map Sum.inr = v then (1 : ℤ) else 0)
      (fun j => rfl)]
    exact sub_self _

/-- Independence of the cast indicator cycles: disjoint supports, read
off at one edge of each cycle. -/
theorem wedge_cast_independent (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂)
    (x : Fin 2 → ℝ)
    (hx : (fun e : Fin n₁ ⊕ Fin n₂ =>
      ∑ i, x i * ((wedgeCyclesZ n₁ n₂ i e : ℤ) : ℝ)) = 0) : x = 0 := by
  have hL := congrFun hx (Sum.inl ⟨0, h₁⟩)
  have hR := congrFun hx (Sum.inr ⟨0, h₂⟩)
  rw [Fin.sum_univ_two] at hL hR
  have hL' : x 0 * ((1 : ℤ) : ℝ) + x 1 * ((0 : ℤ) : ℝ) = 0 := hL
  have hR' : x 0 * ((0 : ℤ) : ℝ) + x 1 * ((1 : ℤ) : ℝ) = 0 := hR
  simp at hL' hR'
  funext i
  fin_cases i
  · exact hL'
  · exact hR'

/-- Integer period surjectivity for the wedge: single-edge witnesses,
one per cycle. -/
theorem wedge_periods_onto (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂)
    (k : Fin 2 → ℤ) :
    ∃ τ : Fin n₁ ⊕ Fin n₂ → ℤ,
      ∀ j, τ ⬝ᵥ wedgeCyclesZ n₁ n₂ j = k j := by
  haveI : NeZero n₁ := ⟨h₁.ne'⟩
  haveI : NeZero n₂ := ⟨h₂.ne'⟩
  refine ⟨Sum.elim (fun e => if e = 0 then k 0 else 0)
    (fun e => if e = 0 then k 1 else 0), fun j => ?_⟩
  fin_cases j
  · show ∑ e : Fin n₁ ⊕ Fin n₂,
        Sum.elim (fun e => if e = 0 then k 0 else 0)
          (fun e => if e = 0 then k 1 else 0) e
        * Sum.elim (fun _ => (1 : ℤ)) (fun _ => 0) e = k 0
    rw [Fintype.sum_sum_type]
    simp
  · show ∑ e : Fin n₁ ⊕ Fin n₂,
        Sum.elim (fun e => if e = 0 then k 0 else 0)
          (fun e => if e = 0 then k 1 else 0) e
        * Sum.elim (fun _ => (0 : ℤ)) (fun _ => 1) e = k 1
    rw [Fintype.sum_sum_type]
    simp

/-- **Real spanning for the wedge, by Euler**: two independent closed
cycles in a `b₁ = 2` cycle space must span
(`spanning_of_card_eq_b1` + `wedgeGraph_b1`). -/
theorem wedge_spanningR (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂)
    (ω : Fin n₁ ⊕ Fin n₂ → ℝ)
    (hω : ∀ v, (wedgeGraph n₁ n₂ h₁ h₂).boundary ω v = 0) :
    ∃ a : Fin 2 → ℝ,
      ω = fun e => ∑ i, a i * ((wedgeCyclesZ n₁ n₂ i e : ℤ) : ℝ) :=
  (wedgeGraph n₁ n₂ h₁ h₂).spanning_of_card_eq_b1
    (wedgeGraph_b1 n₁ n₂ h₁ h₂).symm
    (fun i e => ((wedgeCyclesZ n₁ n₂ i e : ℤ) : ℝ))
    (fun i v => by
      rw [(wedgeGraph n₁ n₂ h₁ h₂).boundary_castR,
        (IncidenceGraph.mem_cycleLattice _ |>.mp
          (wedgeCyclesZ_mem n₁ n₂ h₁ h₂ i)) v, Int.cast_zero])
    (wedge_cast_independent n₁ n₂ h₁ h₂)
    ω hω

/-- **The wedge's lattice basis**: the two indicator cycles, as a
genuine `ℤ`-basis of `H₁(C_{n₁} ∨ C_{n₂}; ℤ)`. Integral spanning is
derived by primitivity (`exists_int_coords`): real spanning by Euler
plus the single-edge period realizers. -/
noncomputable def wedgeLatticeBasis (n₁ n₂ : ℕ) (h₁ : 0 < n₁)
    (h₂ : 0 < n₂) :
    Module.Basis (Fin 2) ℤ (wedgeGraph n₁ n₂ h₁ h₂).cycleLattice :=
  (wedgeGraph n₁ n₂ h₁ h₂).basisOfCycles (wedgeCyclesZ n₁ n₂)
    (wedgeCyclesZ_mem n₁ n₂ h₁ h₂)
    (wedge_cast_independent n₁ n₂ h₁ h₂)
    (fun _ hx => (wedgeGraph n₁ n₂ h₁ h₂).exists_int_coords
      (wedgeCyclesZ n₁ n₂) (wedge_spanningR n₁ n₂ h₁ h₂)
      (wedge_periods_onto n₁ n₂ h₁ h₂) hx)

/-- The basis's integer cycles are the indicator family. -/
theorem cyclesZ_wedgeLatticeBasis (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    (wedgeGraph n₁ n₂ h₁ h₂).cyclesZ (wedgeLatticeBasis n₁ n₂ h₁ h₂)
      = wedgeCyclesZ n₁ n₂ :=
  (wedgeGraph n₁ n₂ h₁ h₂).cyclesZ_basisOfCycles _ _ _ _

/-- `b₁ = 2` **through the basis** — corroborating the Euler
computation (`wedgeGraph_b1`) by `card_eq_b1`. -/
theorem wedgeGraph_b1' (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    (wedgeGraph n₁ n₂ h₁ h₂).b1 = 2 :=
  ((wedgeGraph n₁ n₂ h₁ h₂).card_eq_b1
    (wedgeLatticeBasis n₁ n₂ h₁ h₂)).symm

end Meno
