import Meno.CyclePresentation

/-! # The Period Lattice: the Keystone, ℤ-form

The connecting theorem stated in PLAN (Phase 24), endorsed and built:
**integer descriptions modulo integer local re-description are exactly
the period lattice `ℤ^{b₁}`** (`latticeQuotEquiv`). This is the
keystone's mathematical content — the incompressible residue of
neighbor-local re-description, now as a *lattice* (counting-ready)
statement rather than a real vector space. Note the quotient
`(G.E → ℤ) ⧸ range (G.gradLin ℤ)` depends only on the graph — this is
the working model of `H¹(G;ℤ)`; the presentation supplies coordinates.

An `IntegralCyclePresentation` extends a `CyclePresentation` with an
integer form of the cycle basis and two lattice-level fields:

* `periods_onto` — every integer period vector is realized by an
  integer cochain;
* `integral_potentials` — an integer cochain with zero integer
  periods has an **integer** potential.

Concrete instances discharge these by hand (prefix sums, single-edge
cochains); the Completion Path's C2 (`fundamentalPresentation`)
discharges them for **every** finite graph via the walk-integration
engine of `Meno/IncidenceGraph.lean`. Everything else is generic:
integer Stokes is inherited from the real theorem by casting, and the
quotient equivalence is the first isomorphism theorem over `ℤ`. -/

namespace Meno

open scoped BigOperators
open Matrix

universe u v

/-! ## Prefix sums: integer integration around a cycle -/

/-- Prefix sum of an integer cochain strictly below a vertex. -/
def finPrefixSum {n : ℕ} (ω : Fin n → ℤ) (v : Fin n) : ℤ :=
  ∑ m, if m < v then ω m else 0

theorem finPrefixSum_zero {n : ℕ} [NeZero n] (ω : Fin n → ℤ) :
    finPrefixSum ω 0 = 0 :=
  Finset.sum_eq_zero fun m _ => if_neg (by
    rw [Fin.lt_def, Fin.val_zero]
    omega)

/-- **Discrete integration**: on a cycle with total sum zero, the
prefix sum is an integer potential — its gradient along edge
`e : e → e + 1` recovers `ω e`, wrap-around included. -/
theorem finPrefixSum_grad {n : ℕ} [NeZero n] (ω : Fin n → ℤ)
    (hsum : ∑ m, ω m = 0) (e : Fin n) :
    finPrefixSum ω (e + 1) - finPrefixSum ω e = ω e := by
  by_cases hlt : e.val + 1 < n
  · -- No wrap: (e+1).val = e.val + 1.
    have hval : ((e + 1 : Fin n)).val = e.val + 1 := by
      rw [Fin.val_add]
      have h1 : (1 : Fin n).val = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by omega)
      rw [h1, Nat.mod_eq_of_lt hlt]
    have hpoint : ∀ m : Fin n,
        (if m < e + 1 then ω m else 0) - (if m < e then ω m else 0)
          = if m = e then ω m else 0 := by
      intro m
      by_cases h1 : m < e
      · have h2 : m < e + 1 := by
          rw [Fin.lt_def] at h1 ⊢
          omega
        rw [if_pos h2, if_pos h1, if_neg (Fin.ne_of_lt h1)]
        ring
      · by_cases h3 : m = e
        · have h2 : m < e + 1 := by
            rw [Fin.lt_def, hval, h3]
            omega
          rw [if_pos h2, if_neg h1, if_pos h3, h3]
          ring
        · have hne : m.val ≠ e.val := fun hc => h3 (Fin.ext hc)
          have h2 : ¬ m < e + 1 := by
            rw [Fin.lt_def, hval]
            rw [Fin.lt_def] at h1
            omega
          rw [if_neg h2, if_neg h1, if_neg h3]
          ring
    calc finPrefixSum ω (e + 1) - finPrefixSum ω e
        = ∑ m, ((if m < e + 1 then ω m else 0)
            - (if m < e then ω m else 0)) :=
          (Finset.sum_sub_distrib _ _).symm
      _ = ∑ m, if m = e then ω m else 0 :=
          Finset.sum_congr rfl fun m _ => hpoint m
      _ = ω e := by
          rw [Finset.sum_ite_eq' Finset.univ e ω]
          simp
  · -- Wrap: e is the last vertex, e + 1 = 0.
    have hle := e.isLt
    have hval : e.val = n - 1 := by omega
    have he1 : (e + 1 : Fin n) = 0 := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_one', Fin.val_zero]
      rcases Nat.lt_or_ge 1 n with h1 | h1
      · rw [Nat.mod_eq_of_lt h1]
        have : e.val + 1 = n := by omega
        rw [this, Nat.mod_self]
      · -- n = 1
        have hn1 : n = 1 := by omega
        subst hn1
        omega
    rw [he1, finPrefixSum_zero]
    have hmax : ∀ m : Fin n, m ≠ e → m < e := by
      intro m hm
      rw [Fin.lt_def]
      have hne : m.val ≠ e.val := fun hc => hm (Fin.ext hc)
      have := m.isLt
      omega
    have hsplit : ∀ m : Fin n,
        ω m = (if m < e then ω m else 0) + (if m = e then ω m else 0) := by
      intro m
      by_cases h1 : m = e
      · rw [if_pos h1, if_neg (by rw [h1]; exact lt_irrefl e)]
        ring
      · rw [if_neg h1, if_pos (hmax m h1)]
        ring
    have hpre : finPrefixSum ω e + ω e = ∑ m, ω m := by
      have hωe : ω e = ∑ m, (if m = e then ω m else 0) := by
        rw [Finset.sum_ite_eq' Finset.univ e ω]
        simp
      calc finPrefixSum ω e + ω e
          = (∑ m, if m < e then ω m else 0)
            + ∑ m, (if m = e then ω m else 0) := by
            rw [← hωe]
            rfl
        _ = ∑ m, ((if m < e then ω m else 0)
              + (if m = e then ω m else 0)) :=
            (Finset.sum_add_distrib).symm
        _ = ∑ m, ω m := Finset.sum_congr rfl fun m _ => (hsplit m).symm
    omega

/-! ## The integral presentation -/

/-- A cycle presentation with an integer form of its basis and the
two lattice-level integrality facts. -/
structure IntegralCyclePresentation (G : IncidenceGraph.{u, v})
    extends CyclePresentation G where
  /-- The integer form of the cycle basis. -/
  cyclesZ : Fin r → G.E → ℤ
  /-- The integer basis casts to the real one. -/
  cyclesZ_cast : ∀ i e, ((cyclesZ i e : ℤ) : ℝ) = cycles i e
  /-- Every integer period vector is realized by an integer cochain. -/
  periods_onto : ∀ k : Fin r → ℤ, ∃ ω : G.E → ℤ, ∀ j, ω ⬝ᵥ cyclesZ j = k j
  /-- Integer integration: an integer cochain with zero integer
  periods has an integer potential. -/
  integral_potentials : ∀ ω : G.E → ℤ, (∀ j, ω ⬝ᵥ cyclesZ j = 0) →
    ∃ g : G.V → ℤ, G.grad g = ω

namespace IntegralCyclePresentation

variable {G : IncidenceGraph.{u, v}} (Q : IntegralCyclePresentation G)

private lemma cast_dotProduct {ι : Type v} [Fintype ι] (x y : ι → ℤ) :
    ((x ⬝ᵥ y : ℤ) : ℝ) = (fun e => (x e : ℝ)) ⬝ᵥ (fun e => (y e : ℝ)) := by
  show ((∑ e, x e * y e : ℤ) : ℝ) = ∑ e, (x e : ℝ) * (y e : ℝ)
  push_cast
  rfl

/-- **Integer Stokes**, inherited from the real theorem by casting:
integer gradients have zero integer periods. -/
theorem gradZ_period (g : G.V → ℤ) (j : Fin Q.r) :
    G.grad g ⬝ᵥ Q.cyclesZ j = 0 := by
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_zero, cast_dotProduct]
  have h1 : (fun e => ((G.grad g e : ℤ) : ℝ))
      = G.grad (fun v => (g v : ℝ)) := by
    funext e
    show ((g (G.tgt e) - g (G.src e) : ℤ) : ℝ)
      = (g (G.tgt e) : ℝ) - (g (G.src e) : ℝ)
    push_cast
    rfl
  have h2 : (fun e => (Q.cyclesZ j e : ℝ)) = Q.cycles j :=
    funext fun e => Q.cyclesZ_cast j e
  rw [h1, h2]
  exact Q.toCyclePresentation.grad_period _ j

/-- The integer period map as a `ℤ`-linear map. -/
noncomputable def periodLinZ : (G.E → ℤ) →ₗ[ℤ] (Fin Q.r → ℤ) where
  toFun ω := fun j => ω ⬝ᵥ Q.cyclesZ j
  map_add' ω η := funext fun j => add_dotProduct ω η (Q.cyclesZ j)
  map_smul' c ω := funext fun j => smul_dotProduct c ω (Q.cyclesZ j)

/-- Lattice exactness: the kernel of the integer period map is exactly
the image of the integer gradient. -/
theorem range_gradLinZ_eq_ker_periodLinZ :
    LinearMap.range (G.gradLin ℤ) = LinearMap.ker Q.periodLinZ := by
  ext ω
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨g, rfl⟩
    funext j
    exact Q.gradZ_period g j
  · intro h
    exact Q.integral_potentials ω (fun j => congrFun h j)

/-- The integer period map is surjective. -/
theorem periodLinZ_surjective : Function.Surjective Q.periodLinZ := by
  intro k
  obtain ⟨ω, hω⟩ := Q.periods_onto k
  exact ⟨ω, funext hω⟩

/-- **THE KEYSTONE, ℤ-form**: integer descriptions modulo integer
local re-description are exactly the period lattice `ℤ^{b₁}`. The
incompressible residue of neighbor-local re-description is `b₁`
integer degrees of freedom — as a lattice, ready for counting at any
finite resolution. The quotient depends only on the graph. -/
noncomputable def latticeQuotEquiv :
    ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) ≃ₗ[ℤ] (Fin Q.r → ℤ) :=
  (Submodule.quotEquivOfEq _ _ Q.range_gradLinZ_eq_ker_periodLinZ).trans
    (Q.periodLinZ.quotKerEquivOfSurjective Q.periodLinZ_surjective)

end IntegralCyclePresentation

/-! ## Instances: the cycle graph and the (spectator) wedge -/

/-- The cycle graph as an integral presentation. -/
noncomputable def cycleIntegralPresentation (n : ℕ) (hn : 0 < n) :
    IntegralCyclePresentation (cycleGraph n hn) :=
  haveI : NeZero n := ⟨hn.ne'⟩
  { cyclePresentation n hn with
    cyclesZ := fun _ _ => 1
    cyclesZ_cast := fun _ _ => by
      show ((1 : ℤ) : ℝ) = 1
      norm_num
    periods_onto := fun k => by
      refine ⟨fun e => if e = 0 then k 0 else 0, fun j => ?_⟩
      have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      show ∑ e, (if e = 0 then k 0 else 0) * 1 = k 0
      simp
    integral_potentials := fun ω h => by
      have hsum : ∑ m, ω m = 0 := by
        have h0 := h 0
        show _ = (0 : ℤ)
        rw [← h0]
        show ∑ m, ω m = ∑ m, ω m * 1
        simp
      exact ⟨finPrefixSum ω, funext fun e => finPrefixSum_grad ω hsum e⟩ }

/-- The (spectator) wedge of two cycles as an integral presentation. -/
noncomputable def wedgeIntegralPresentation (n₁ n₂ : ℕ)
    (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    IntegralCyclePresentation (wedgeSpectatorGraph n₁ n₂ h₁ h₂) :=
  haveI : NeZero n₁ := ⟨h₁.ne'⟩
  haveI : NeZero n₂ := ⟨h₂.ne'⟩
  { wedgePresentation n₁ n₂ h₁ h₂ with
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
      refine ⟨Sum.elim (finPrefixSum (fun m => ω (Sum.inl m)))
        (finPrefixSum (fun m => ω (Sum.inr m))), ?_⟩
      have hgv : ∀ v : Fin n₂,
          Sum.elim (finPrefixSum (fun m => ω (Sum.inl m)))
            (finPrefixSum (fun m => ω (Sum.inr m))) (wedgeVertex n₁ n₂ v)
          = finPrefixSum (fun m => ω (Sum.inr m)) v := by
        intro v
        unfold wedgeVertex
        by_cases hv : v = 0
        · rw [if_pos hv, hv]
          show finPrefixSum (fun m => ω (Sum.inl m)) 0
            = finPrefixSum (fun m => ω (Sum.inr m)) 0
          rw [finPrefixSum_zero, finPrefixSum_zero]
        · rw [if_neg hv]
          rfl
      funext e
      cases e with
      | inl a =>
        show finPrefixSum (fun m => ω (Sum.inl m)) (a + 1)
            - finPrefixSum (fun m => ω (Sum.inl m)) a = ω (Sum.inl a)
        exact finPrefixSum_grad _ hL a
      | inr b =>
        show Sum.elim (finPrefixSum (fun m => ω (Sum.inl m)))
              (finPrefixSum (fun m => ω (Sum.inr m)))
              (wedgeVertex n₁ n₂ (b + 1))
            - Sum.elim (finPrefixSum (fun m => ω (Sum.inl m)))
              (finPrefixSum (fun m => ω (Sum.inr m)))
              (wedgeVertex n₁ n₂ b)
          = ω (Sum.inr b)
        rw [hgv, hgv]
        exact finPrefixSum_grad _ hR b }

end Meno
