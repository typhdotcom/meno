import Meno.Simplicial
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # General Hodge Theory for Graphs

Hodge decomposition for arbitrary finite graphs. The key structural results:
- Edge-supported 1-cochains (EC1) have a natural energy functional
- The harmonic subspace is divergence-free (already in Simplicial.lean)
- For a graph with b₁ independent cycles, the partition function sums over ℤ^{b₁}
- For b₁ = 1 (cycle graphs), this recovers the existing partition function -/

namespace Simplicial

open Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## EC1 Equality -/

omit [Fintype V] [DecidableEq V] in
@[ext] theorem EC1.ext {G : Graph V} {σ τ : EC1 G}
    (h : ∀ i j, σ.val i j = τ.val i j) : σ = τ := by
  cases σ; cases τ; simp only [mk.injEq]; funext i j; exact h i j

/-! ## Energy on Edge Cochains -/

/-- Energy (squared norm) of an edge cochain: ½ Σᵢⱼ σ(i,j)². -/
noncomputable def EC1.energy {G : Graph V} (σ : EC1 G) : ℝ :=
  (1/2) * ∑ i : V, ∑ j : V, σ.val i j * σ.val i j

omit [DecidableEq V] in
theorem EC1.energy_nonneg {G : Graph V} (σ : EC1 G) : 0 ≤ σ.energy := by
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  exact mul_self_nonneg _

omit [DecidableEq V] in
theorem EC1.energy_eq_zero_iff {G : Graph V} (σ : EC1 G) :
    σ.energy = 0 ↔ ∀ i j, σ.val i j = 0 := by
  simp only [EC1.energy]
  constructor
  · intro h
    have := (mul_eq_zero.mp h).resolve_left (by norm_num : (1/2 : ℝ) ≠ 0)
    intro i j
    have h_i := (Finset.sum_eq_zero_iff_of_nonneg (fun i' _ =>
        Finset.sum_nonneg (fun j' _ => mul_self_nonneg (σ.val i' j')))).mp this
        i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun j' _ =>
        mul_self_nonneg (σ.val i j'))).mp h_i j (Finset.mem_univ j))
  · intro h; simp [h]

/-! ## Graph Partition Function -/

/-- The partition function of a graph with b₁ independent cycles,
    summing Boltzmann weights exp(-k^T Q k) over winding vectors k ∈ ℤ^{b₁}. -/
noncomputable def graphPartitionFn (b₁ : ℕ)
    (Q : Fin b₁ → Fin b₁ → ℝ)
    (_hsum : Summable (fun k : Fin b₁ → ℤ =>
      Real.exp (-∑ i, ∑ j, Q i j * (k i : ℝ) * (k j : ℝ)))) : ℝ :=
  ∑' k : Fin b₁ → ℤ, Real.exp (-∑ i, ∑ j, Q i j * (k i : ℝ) * (k j : ℝ))

/-- Complexity of a graph: log of the partition function. -/
noncomputable def graphComplexity (b₁ : ℕ)
    (Q : Fin b₁ → Fin b₁ → ℝ)
    (hsum : Summable (fun k : Fin b₁ → ℤ =>
      Real.exp (-∑ i, ∑ j, Q i j * (k i : ℝ) * (k j : ℝ)))) : ℝ :=
  Real.log (graphPartitionFn b₁ Q hsum)

/-! ## Rank-1 Recovery: Cycle Graphs -/

/-- For b₁ = 1 with Q = (1/n), the graph partition function recovers
    the cycle partition function Z(Cₙ) = Σ_k exp(-k²/n). -/
theorem graphPartitionFn_rank1_eq (n : ℕ) (hn : n ≥ 3)
    (hsum : Summable (fun k : Fin 1 → ℤ =>
      Real.exp (-∑ i, ∑ j, (fun _ _ => (1 : ℝ) / n) i j * (k i : ℝ) * (k j : ℝ)))) :
    graphPartitionFn 1 (fun _ _ => (1 : ℝ) / n) hsum = partitionFn n hn := by
  unfold graphPartitionFn partitionFn
  let e : (Fin 1 → ℤ) ≃ ℤ := Equiv.funUnique (Fin 1) ℤ
  have hrw : (fun k : Fin 1 → ℤ =>
      Real.exp (-∑ i, ∑ j, (1 : ℝ) / ↑n * ↑(k i) * ↑(k j))) =
      (fun z : ℤ => Real.exp (-(z : ℝ) ^ 2 / ↑n)) ∘ e := by
    ext k; simp [e, Equiv.funUnique, sq]; ring
  simp only [hrw, Function.comp_def]
  exact e.tsum_eq (fun z : ℤ => Real.exp (-(z : ℝ) ^ 2 / ↑n))

/-! ## Siegel Theta Function -/

/-- The Siegel theta function: Θ(Q) = Σ_{k ∈ ℤ^b₁} exp(-π k^T Q k).
    For b₁ = 1 and Q = (1/(πn)), this is the Jacobi theta ϑ₃(i/(πn)). -/
noncomputable def siegelTheta (b₁ : ℕ) (Q : Fin b₁ → Fin b₁ → ℝ)
    (_hsum : Summable (fun k : Fin b₁ → ℤ =>
      Real.exp (-Real.pi * ∑ i, ∑ j, Q i j * (k i : ℝ) * (k j : ℝ)))) : ℝ :=
  ∑' k : Fin b₁ → ℤ, Real.exp (-Real.pi * ∑ i, ∑ j, Q i j * (k i : ℝ) * (k j : ℝ))

/-- The graph partition function equals the Siegel theta with rescaled Q.
    Z(Q) = Θ(Q/π) when using the physical normalization. -/
theorem graphPartitionFn_eq_siegelTheta (b₁ : ℕ)
    (Q : Fin b₁ → Fin b₁ → ℝ)
    (hsum : Summable (fun k : Fin b₁ → ℤ =>
      Real.exp (-∑ i, ∑ j, Q i j * (k i : ℝ) * (k j : ℝ))))
    (hsum' : Summable (fun k : Fin b₁ → ℤ =>
      Real.exp (-Real.pi * ∑ i, ∑ j, (Q i j / Real.pi) * (k i : ℝ) * (k j : ℝ)))) :
    graphPartitionFn b₁ Q hsum = siegelTheta b₁ (fun i j => Q i j / Real.pi) hsum' := by
  unfold graphPartitionFn siegelTheta
  congr 1; ext k; congr 1
  rw [neg_mul]; congr 1
  rw [Finset.mul_sum]; congr 1; ext i
  rw [Finset.mul_sum]; congr 1; ext j
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

/-! ## Torus Example Setup -/

private lemma torus_reindex (m n : ℕ) :
    (∑' k : Fin 2 → ℤ,
    Real.exp (-(k 0 : ℝ) ^ 2 / ↑m) * Real.exp (-(k 1 : ℝ) ^ 2 / ↑n)) =
    ∑' p : ℤ × ℤ,
    Real.exp (-(p.1 : ℝ) ^ 2 / ↑m) * Real.exp (-(p.2 : ℝ) ^ 2 / ↑n) := by
  change (∑' k : Fin 2 → ℤ, (fun p : ℤ × ℤ =>
      Real.exp (-(p.1 : ℝ) ^ 2 / ↑m) * Real.exp (-(p.2 : ℝ) ^ 2 / ↑n))
      (finTwoArrowEquiv ℤ k)) = _
  exact (finTwoArrowEquiv ℤ).tsum_eq (fun p : ℤ × ℤ =>
      Real.exp (-(p.1 : ℝ) ^ 2 / ↑m) * Real.exp (-(p.2 : ℝ) ^ 2 / ↑n))

private lemma torus_summable_prod (m n : ℕ)
    (hsum : Summable (fun k : Fin 2 → ℤ =>
      Real.exp (-(k 0 : ℝ) ^ 2 / ↑m) * Real.exp (-(k 1 : ℝ) ^ 2 / ↑n))) :
    Summable (fun p : ℤ × ℤ =>
      Real.exp (-(p.1 : ℝ) ^ 2 / ↑m) * Real.exp (-(p.2 : ℝ) ^ 2 / ↑n)) := by
  rw [← (finTwoArrowEquiv ℤ).summable_iff]; convert hsum using 1

private lemma torus_summable_swap (m n : ℕ)
    (hprod : Summable (fun p : ℤ × ℤ =>
      Real.exp (-(p.1 : ℝ) ^ 2 / ↑m) * Real.exp (-(p.2 : ℝ) ^ 2 / ↑n))) :
    Summable (fun p : ℤ × ℤ =>
      Real.exp (-(p.2 : ℝ) ^ 2 / ↑m) * Real.exp (-(p.1 : ℝ) ^ 2 / ↑n)) := by
  change Summable ((fun p : ℤ × ℤ =>
      Real.exp (-(p.1 : ℝ) ^ 2 / ↑m) * Real.exp (-(p.2 : ℝ) ^ 2 / ↑n)) ∘
      (Equiv.prodComm ℤ ℤ))
  exact (Equiv.prodComm ℤ ℤ).summable_iff.mpr hprod

private lemma torus_summable_n (m n : ℕ)
    (hprod : Summable (fun p : ℤ × ℤ =>
      Real.exp (-(p.1 : ℝ) ^ 2 / ↑m) * Real.exp (-(p.2 : ℝ) ^ 2 / ↑n))) :
    Summable (fun b : ℤ => Real.exp (-(b : ℝ) ^ 2 / ↑n)) := by
  have := hprod.prod_factor (0 : ℤ)
  simp only [Int.cast_zero] at this; norm_num at this; exact this

private lemma torus_summable_m (m n : ℕ)
    (hprod : Summable (fun p : ℤ × ℤ =>
      Real.exp (-(p.1 : ℝ) ^ 2 / ↑m) * Real.exp (-(p.2 : ℝ) ^ 2 / ↑n))) :
    Summable (fun a : ℤ => Real.exp (-(a : ℝ) ^ 2 / ↑m)) := by
  have := (torus_summable_swap m n hprod).prod_factor (0 : ℤ)
  simp only [Int.cast_zero] at this; norm_num at this; exact this

private lemma torus_factor (m n : ℕ)
    (hprod : Summable (fun p : ℤ × ℤ =>
      Real.exp (-(p.1 : ℝ) ^ 2 / ↑m) * Real.exp (-(p.2 : ℝ) ^ 2 / ↑n))) :
    (∑' p : ℤ × ℤ,
      Real.exp (-(p.1 : ℝ) ^ 2 / ↑m) * Real.exp (-(p.2 : ℝ) ^ 2 / ↑n)) =
    (∑' a : ℤ, Real.exp (-(a : ℝ) ^ 2 / ↑m)) *
    (∑' b : ℤ, Real.exp (-(b : ℝ) ^ 2 / ↑n)) :=
  ((torus_summable_m m n hprod).tsum_mul_tsum
    (torus_summable_n m n hprod) hprod).symm

/-- The torus T² = C_m × C_n has b₁ = 2. The Gram matrix is diag(1/m, 1/n).
    The partition function factors: Z(T²) = Z(C_m) · Z(C_n). -/
theorem torus_partitionFn_factors (m n : ℕ) (hm : m ≥ 3) (hn : n ≥ 3)
    (Q : Fin 2 → Fin 2 → ℝ)
    (hQ : Q 0 0 = 1 / m ∧ Q 0 1 = 0 ∧ Q 1 0 = 0 ∧ Q 1 1 = 1 / n)
    (hsum : Summable (fun k : Fin 2 → ℤ =>
      Real.exp (-∑ i, ∑ j, Q i j * (k i : ℝ) * (k j : ℝ)))) :
    graphPartitionFn 2 Q hsum = partitionFn m hm * partitionFn n hn := by
  simp only [graphPartitionFn, partitionFn]
  obtain ⟨h00, h01, h10, h11⟩ := hQ
  -- Simplify quadratic form pointwise
  have hrw : ∀ k : Fin 2 → ℤ,
      Real.exp (-∑ i, ∑ j, Q i j * ↑(k i) * ↑(k j)) =
      Real.exp (-(k 0 : ℝ) ^ 2 / ↑m) * Real.exp (-(k 1 : ℝ) ^ 2 / ↑n) := by
    intro k; simp only [Fin.sum_univ_two, h00, h01, h10, h11,
      zero_mul, add_zero, zero_add, ← Real.exp_add]; congr 1; ring
  simp_rw [hrw]
  -- Transfer summability and factor
  have hsum' := hsum.congr hrw
  rw [torus_reindex]
  exact torus_factor m n (torus_summable_prod m n hsum')

end Simplicial
