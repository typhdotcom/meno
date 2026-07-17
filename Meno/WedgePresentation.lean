import Meno.GraphInstances
import Meno.BasisIndependence
import Meno.Matter

/-! # The Genuine Wedge's Presentation (C5)

The spectator-free wedge (`wedgeGraph`, Phase 29c) becomes a full
citizen: a cycle presentation and an integral presentation, built as
**consumers of the general machinery** —

* `cycles_closed` by a *shift reindexing*: the boundary of an
  indicator cycle telescopes because summing `j ↦ route (j+1)` over
  all `j` is the same as summing `j ↦ route j` (`Fintype.sum_equiv`
  along `+1`). No case analysis on vertices.
* `spanning` by **Euler** (`spanning_of_card_eq_b1` +
  `wedgeGraph_b1`): two independent closed cycles in a `b₁ = 2` cycle
  space must span. The Phase-21 constancy argument is not ported — it
  is obsoleted.
* the integral fields by the same single-edge witnesses as before
  (they never mentioned vertices) and Option-routed prefix sums
  (`wedgePotential`).

The Gram matrix is unchanged — `gramOf wedgeCycles` never saw the
vertex type — so the diagonal closed form and the derived energies
carry over identically. The Phase-21 spectator stack (its graph, its
presentations, and its constancy machinery) has been removed; the
wedge consumers in `Meno/CycleHarmonic.lean` run through this file. -/

namespace Meno

open scoped BigOperators
open Matrix

private lemma independent_of_gramOf_posDef {r : ℕ} {ι : Type*} [Fintype ι]
    (c : Fin r → ι → ℝ) (hpd : (gramOf c).PosDef)
    (x : Fin r → ℝ) (hx : (fun e => ∑ i, x i * c i e) = 0) : x = 0 := by
  by_contra hne
  have hpos := (posDef_iff_dotProduct_mulVec.mp hpd).2 (show x ≠ 0 from hne)
  have hsx : star x = x := funext fun i => star_trivial _
  rw [hsx, IncidenceGraph.dotProduct_gramOf_mulVec] at hpos
  rw [hx, dotProduct_zero] at hpos
  exact lt_irrefl 0 hpos

/-! ## Closedness by shift reindexing -/

theorem wedgeGraph_cycles_closed (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    ∀ i v, (wedgeGraph n₁ n₂ h₁ h₂).boundary (wedgeCycles n₁ n₂ i) v = 0 := by
  haveI : NeZero n₁ := ⟨h₁.ne'⟩
  haveI : NeZero n₂ := ⟨h₂.ne'⟩
  intro i v
  fin_cases i
  · show (wedgeGraph n₁ n₂ h₁ h₂).boundary (wedgeCycles n₁ n₂ 0) v = 0
    rw [IncidenceGraph.boundary_eq_sum, Fintype.sum_sum_type]
    have hL : ∀ j : Fin n₁,
        (wedgeGraph n₁ n₂ h₁ h₂).bcoeff v (Sum.inl j)
            * wedgeCycles n₁ n₂ 0 (Sum.inl j)
          = (if (wedgeRoute n₁ (j + 1)).map Sum.inl = v then (1 : ℝ) else 0)
            - (if (wedgeRoute n₁ j).map Sum.inl = v then 1 else 0) := by
      intro j
      rw [show wedgeCycles n₁ n₂ 0 (Sum.inl j) = 1 from rfl, mul_one]
      rfl
    have hR : ∀ j : Fin n₂,
        (wedgeGraph n₁ n₂ h₁ h₂).bcoeff v (Sum.inr j)
            * wedgeCycles n₁ n₂ 0 (Sum.inr j) = 0 := by
      intro j
      rw [show wedgeCycles n₁ n₂ 0 (Sum.inr j) = 0 from rfl, mul_zero]
    rw [Finset.sum_congr rfl fun j _ => hL j,
      Finset.sum_congr rfl fun j _ => hR j, Finset.sum_const_zero, add_zero,
      Finset.sum_sub_distrib]
    rw [Fintype.sum_equiv (Equiv.addRight (1 : Fin n₁))
      (fun j => if (wedgeRoute n₁ (j + 1)).map Sum.inl = v then (1 : ℝ) else 0)
      (fun j => if (wedgeRoute n₁ j).map Sum.inl = v then (1 : ℝ) else 0)
      (fun j => rfl)]
    exact sub_self _
  · show (wedgeGraph n₁ n₂ h₁ h₂).boundary (wedgeCycles n₁ n₂ 1) v = 0
    rw [IncidenceGraph.boundary_eq_sum, Fintype.sum_sum_type]
    have hL : ∀ j : Fin n₁,
        (wedgeGraph n₁ n₂ h₁ h₂).bcoeff v (Sum.inl j)
            * wedgeCycles n₁ n₂ 1 (Sum.inl j) = 0 := by
      intro j
      rw [show wedgeCycles n₁ n₂ 1 (Sum.inl j) = 0 from rfl, mul_zero]
    have hR : ∀ j : Fin n₂,
        (wedgeGraph n₁ n₂ h₁ h₂).bcoeff v (Sum.inr j)
            * wedgeCycles n₁ n₂ 1 (Sum.inr j)
          = (if (wedgeRoute n₂ (j + 1)).map Sum.inr = v then (1 : ℝ) else 0)
            - (if (wedgeRoute n₂ j).map Sum.inr = v then 1 else 0) := by
      intro j
      rw [show wedgeCycles n₁ n₂ 1 (Sum.inr j) = 1 from rfl, mul_one]
      rfl
    rw [Finset.sum_congr rfl fun j _ => hL j,
      Finset.sum_congr rfl fun j _ => hR j, Finset.sum_const_zero, zero_add,
      Finset.sum_sub_distrib]
    rw [Fintype.sum_equiv (Equiv.addRight (1 : Fin n₂))
      (fun j => if (wedgeRoute n₂ (j + 1)).map Sum.inr = v then (1 : ℝ) else 0)
      (fun j => if (wedgeRoute n₂ j).map Sum.inr = v then (1 : ℝ) else 0)
      (fun j => rfl)]
    exact sub_self _

/-! ## The presentation: spanning by Euler -/

/-- The genuine wedge's cycle presentation — spanning derived from
`b₁ = 2` by the Euler criterion, not from a constancy argument. -/
@[reducible] noncomputable def wedgeGraphPresentation (n₁ n₂ : ℕ)
    (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    CyclePresentation (wedgeGraph n₁ n₂ h₁ h₂) :=
  haveI : NeZero n₁ := ⟨h₁.ne'⟩
  haveI : NeZero n₂ := ⟨h₂.ne'⟩
  { r := 2
    cycles := wedgeCycles n₁ n₂
    cycles_closed := wedgeGraph_cycles_closed n₁ n₂ h₁ h₂
    spanning := fun ω hω =>
      (wedgeGraph n₁ n₂ h₁ h₂).spanning_of_card_eq_b1
        (wedgeGraph_b1 n₁ n₂ h₁ h₂).symm (wedgeCycles n₁ n₂)
        (wedgeGraph_cycles_closed n₁ n₂ h₁ h₂)
        (fun x hx => independent_of_gramOf_posDef (wedgeCycles n₁ n₂)
          (gramOf_wedgeCycles_posDef n₁ n₂ h₁ h₂) x hx)
        ω hω
    gram_posDef := gramOf_wedgeCycles_posDef n₁ n₂ h₁ h₂ }

/-! ## The integral presentation: routed prefix sums -/

/-- The wedge potential: per-side prefix sums, `0` at the shared
basepoint. -/
def wedgePotential (n₁ n₂ : ℕ) (ω : Fin n₁ ⊕ Fin n₂ → ℤ) :
    Option (Fin (n₁ - 1) ⊕ Fin (n₂ - 1)) → ℤ
  | none => 0
  | some (Sum.inl k) => finPrefixSum (fun m => ω (Sum.inl m))
      ⟨k.val + 1, by have := k.isLt; omega⟩
  | some (Sum.inr k) => finPrefixSum (fun m => ω (Sum.inr m))
      ⟨k.val + 1, by have := k.isLt; omega⟩

theorem wedgePotential_route₁ (n₁ n₂ : ℕ) [NeZero n₁]
    (ω : Fin n₁ ⊕ Fin n₂ → ℤ) (j : Fin n₁) :
    wedgePotential n₁ n₂ ω ((wedgeRoute n₁ j).map Sum.inl)
      = finPrefixSum (fun m => ω (Sum.inl m)) j := by
  unfold wedgeRoute
  by_cases hj : j.val = 0
  · rw [dif_pos hj]
    show (0 : ℤ) = finPrefixSum (fun m => ω (Sum.inl m)) j
    rw [show j = 0 from Fin.ext (by simpa using hj), finPrefixSum_zero]
  · rw [dif_neg hj]
    show finPrefixSum (fun m => ω (Sum.inl m)) ⟨j.val - 1 + 1, _⟩
      = finPrefixSum (fun m => ω (Sum.inl m)) j
    congr 1
    exact Fin.ext (by show j.val - 1 + 1 = j.val; omega)

theorem wedgePotential_route₂ (n₁ n₂ : ℕ) [NeZero n₂]
    (ω : Fin n₁ ⊕ Fin n₂ → ℤ) (j : Fin n₂) :
    wedgePotential n₁ n₂ ω ((wedgeRoute n₂ j).map Sum.inr)
      = finPrefixSum (fun m => ω (Sum.inr m)) j := by
  unfold wedgeRoute
  by_cases hj : j.val = 0
  · rw [dif_pos hj]
    show (0 : ℤ) = finPrefixSum (fun m => ω (Sum.inr m)) j
    rw [show j = 0 from Fin.ext (by simpa using hj), finPrefixSum_zero]
  · rw [dif_neg hj]
    show finPrefixSum (fun m => ω (Sum.inr m)) ⟨j.val - 1 + 1, _⟩
      = finPrefixSum (fun m => ω (Sum.inr m)) j
    congr 1
    exact Fin.ext (by show j.val - 1 + 1 = j.val; omega)

/-- The genuine wedge as an **integral** presentation: same integer
basis and single-edge period witnesses as ever (they never mentioned
vertices); potentials by routed prefix sums. -/
@[reducible] noncomputable def wedgeGraphIntegralPresentation (n₁ n₂ : ℕ)
    (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    IntegralCyclePresentation (wedgeGraph n₁ n₂ h₁ h₂) :=
  haveI : NeZero n₁ := ⟨h₁.ne'⟩
  haveI : NeZero n₂ := ⟨h₂.ne'⟩
  { wedgeGraphPresentation n₁ n₂ h₁ h₂ with
    cyclesZ := ![Sum.elim (fun _ => 1) (fun _ => 0),
      Sum.elim (fun _ => 0) (fun _ => 1)]
    cyclesZ_cast := fun i e => by
      fin_cases i <;> cases e <;> simp [wedgeCycles]
    periods_onto := fun k => by
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
    integral_potentials := fun ω h => by
      have hL : ∑ m, ω (Sum.inl m) = 0 := by
        have h0 : ω ⬝ᵥ Sum.elim (fun _ => (1 : ℤ)) (fun _ => 0) = 0 := h 0
        rw [show ω ⬝ᵥ Sum.elim (fun _ => (1 : ℤ)) (fun _ => 0)
            = ∑ e, ω e * Sum.elim (fun _ => (1 : ℤ)) (fun _ => 0) e
          from rfl, Fintype.sum_sum_type] at h0
        simpa using h0
      have hR : ∑ m, ω (Sum.inr m) = 0 := by
        have h1 : ω ⬝ᵥ Sum.elim (fun _ => (0 : ℤ)) (fun _ => 1) = 0 := h 1
        rw [show ω ⬝ᵥ Sum.elim (fun _ => (0 : ℤ)) (fun _ => 1)
            = ∑ e, ω e * Sum.elim (fun _ => (0 : ℤ)) (fun _ => 1) e
          from rfl, Fintype.sum_sum_type] at h1
        simpa using h1
      refine ⟨wedgePotential n₁ n₂ ω, funext fun e => ?_⟩
      cases e with
      | inl a =>
        show wedgePotential n₁ n₂ ω ((wedgeRoute n₁ (a + 1)).map Sum.inl)
            - wedgePotential n₁ n₂ ω ((wedgeRoute n₁ a).map Sum.inl)
          = ω (Sum.inl a)
        rw [wedgePotential_route₁, wedgePotential_route₁]
        exact finPrefixSum_grad _ hL a
      | inr b =>
        show wedgePotential n₁ n₂ ω ((wedgeRoute n₂ (b + 1)).map Sum.inr)
            - wedgePotential n₁ n₂ ω ((wedgeRoute n₂ b).map Sum.inr)
          = ω (Sum.inr b)
        rw [wedgePotential_route₂, wedgePotential_route₂]
        exact finPrefixSum_grad _ hR b }

/-- The genuine wedge has matter: nontrivial topology (`b₁ = 2`)
forces it. -/
theorem wedgeGraph_exists_matter (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    Nonempty (MatterSector (wedgeGraph n₁ n₂ h₁ h₂)) :=
  exists_matter _ (by rw [wedgeGraph_b1 n₁ n₂ h₁ h₂]; norm_num)

/-! ## C5's acceptance witnesses

Each concrete presentation is a rebase-image of its graph's
fundamental presentation — instances of C3's
`exists_rebase_related`. (The theta instance lives with its
presentation in `Meno/ThetaHarmonic.lean`, review #3.) -/

/-- The hand-built cycle presentation's rank corroborates the Euler
proof: `r = b₁ = 1` (moved from `Meno/GraphInstances.lean`, review #3
— that file is pure topology now). -/
theorem cycleGraph_b1' (n : ℕ) (hn : 0 < n) : (cycleGraph n hn).b1 = 1 :=
  ((cycleIntegralPresentation n hn).r_eq_b1).symm.trans rfl

theorem cycleIntegralPresentation_rebase_related (n : ℕ) (hn : 0 < n) :
    ∃ (U : Matrix (Fin ((cycleGraph n hn).fundamentalPresentation).r)
        (Fin ((cycleGraph n hn).fundamentalPresentation).r) ℤ)
      (hU : IsUnit U.det),
      ∀ i e, (cycleIntegralPresentation n hn).cycles
          (Fin.cast (((cycleGraph n hn).fundamentalPresentation).r_eq_b1.trans
            (cycleIntegralPresentation n hn).r_eq_b1.symm) i) e
        = (((cycleGraph n hn).fundamentalPresentation).toCyclePresentation.rebase
            U hU).cycles i e :=
  IntegralCyclePresentation.exists_rebase_related _ _

theorem wedgeGraphIntegralPresentation_rebase_related
    (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    ∃ (U : Matrix (Fin ((wedgeGraph n₁ n₂ h₁ h₂).fundamentalPresentation).r)
        (Fin ((wedgeGraph n₁ n₂ h₁ h₂).fundamentalPresentation).r) ℤ)
      (hU : IsUnit U.det),
      ∀ i e, (wedgeGraphIntegralPresentation n₁ n₂ h₁ h₂).cycles
          (Fin.cast
            (((wedgeGraph n₁ n₂ h₁ h₂).fundamentalPresentation).r_eq_b1.trans
              (wedgeGraphIntegralPresentation n₁ n₂ h₁ h₂).r_eq_b1.symm) i) e
        = (((wedgeGraph n₁ n₂ h₁ h₂).fundamentalPresentation).toCyclePresentation.rebase
            U hU).cycles i e :=
  IntegralCyclePresentation.exists_rebase_related _ _

end Meno
