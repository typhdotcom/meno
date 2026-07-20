import Meno.Simplicial
import Meno.QuadraticAction
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # The Graph Partition Function, Identified with the Spine

What survives of the walk model's Hodge chapter is its partition
function and the identification that makes it the spine's: for a graph
with `b₁` independent cycles, `graphPartitionFn` sums Boltzmann
weights over winding vectors `k ∈ ℤ^{b₁}`, and it **is** the spine's
partition function definitionally (`graphPartitionFn_eq_spine`).
Diagonal duality is subsumed by the full Siegel–Poisson theorem,
`Meno/SiegelPoisson.lean`. -/

namespace Simplicial

open Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Energy on edge cochains -/

omit [Fintype V] [DecidableEq V] in
@[ext] theorem EC1.ext {G : Graph V} {σ τ : EC1 G}
    (h : ∀ i j, σ.val i j = τ.val i j) : σ = τ := by
  cases σ; cases τ; simp only [mk.injEq]; funext i j; exact h i j

/-- Energy (squared norm) of an edge cochain: ½ Σᵢⱼ σ(i,j)². -/
noncomputable def EC1.energy {G : Graph V} (σ : EC1 G) : ℝ :=
  (1/2) * ∑ i : V, ∑ j : V, σ.val i j * σ.val i j

omit [DecidableEq V] in
theorem EC1.energy_nonneg {G : Graph V} (σ : EC1 G) : 0 ≤ σ.energy := by
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  exact mul_self_nonneg _

/-! ## The graph partition function -/

/-- The partition function of a graph with b₁ independent cycles,
    summing Boltzmann weights exp(-k^T Q k) over winding vectors k ∈ ℤ^{b₁}. -/
noncomputable def graphPartitionFn (b₁ : ℕ)
    (Q : Fin b₁ → Fin b₁ → ℝ)
    (_hsum : Summable (fun k : Fin b₁ → ℤ =>
      Real.exp (-∑ i, ∑ j, Q i j * (k i : ℝ) * (k j : ℝ)))) : ℝ :=
  ∑' k : Fin b₁ → ℤ, Real.exp (-∑ i, ∑ j, Q i j * (k i : ℝ) * (k j : ℝ))

/-- `graphPartitionFn` *is* the
spine's partition function — for any `QuadraticAction` packaging the
same Gram matrix, definitionally. Retained as the graph-facing
wrapper; the analytic source of truth is the spine. -/
theorem graphPartitionFn_eq_spine {b₁ : ℕ}
    (A : Meno.QuadraticAction b₁)
    (hsum : Summable (fun k : Fin b₁ → ℤ =>
      Real.exp (-∑ i, ∑ j, A.Q i j * (k i : ℝ) * (k j : ℝ)))) :
    graphPartitionFn b₁ A.Q hsum = A.toSectorAction.partFn := rfl

end Simplicial
