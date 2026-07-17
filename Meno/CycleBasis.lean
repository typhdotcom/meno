import Meno.IncidenceGraph

/-! # Chosen Cycle Bases: the topological layer

A `CycleBasis` on an incidence graph `G` is purely topological data:
`r` closed cochains spanning the cycle space (`ker ∂`), stated entirely
through `G.boundary`. It carries **no** harmonic content — no Gram
matrix, no positive-definiteness, no pricing. The harmonic extension is
`CyclePresentation` (`Meno/CyclePresentation.lean`), which `extends`
this structure with the positive-definite chain Gram. Split out in
Phase 39 (review #3) so that the topology layer — this file and the
concrete graphs' bases — does not import the variational machinery. -/

namespace Meno

open scoped BigOperators

universe u v

/-- A chosen **topological** cycle basis on the graph `G`: `r` closed
cycle vectors spanning the cycle space. No Gram matrix, no pricing —
see `CyclePresentation` for the harmonic extension. -/
structure CycleBasis (G : IncidenceGraph.{u, v}) where
  /-- Number of basis cycles (the intended `b₁`). -/
  r : ℕ
  /-- The chosen cycle vectors. -/
  cycles : Fin r → G.E → ℝ
  /-- Each basis vector is a cycle: zero boundary at every vertex. -/
  cycles_closed : ∀ i v, G.boundary (cycles i) v = 0
  /-- The basis spans the cycle space. -/
  spanning : ∀ ω : G.E → ℝ, (∀ v, G.boundary ω v = 0) →
    ∃ a : Fin r → ℝ, ω = fun e => ∑ i, a i * cycles i e
  /-- The basis is linearly independent — a genuine basis, not merely
  a closed spanning family (review #4: duplicated cycles and inflated
  ranks are excluded *here*, topologically; positive-definiteness of
  the Gram is then derived downstream, `CycleBasis.gramOf_posDef`). -/
  independent : ∀ x : Fin r → ℝ,
    (fun e => ∑ i, x i * cycles i e) = 0 → x = 0

end Meno
