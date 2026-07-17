import Meno.HarmonicClass

/-! # Basis Independence (C3)

**Any two lattice bases of a graph are `GL(n,ℤ)`-related**, and the
partition function is a function of the graph alone.

With the presentation being an actual
`Module.Basis (Fin n) ℤ G.cycleLattice` (review #5, finding 2), C3's
content is largely definitional:

* **Rank well-definedness** is `card_eq_b1`
  (`Meno/GraphHomology.lean`): every basis has exactly `b₁` elements.
* **Primitivity** is `Module.Basis.sum_repr`: every integral cycle is
  an integer combination of any basis.
* **Unimodular relatedness** (`exists_unimodular_relating`): the
  change-of-basis matrix `B.toMatrix B'` is invertible over `ℤ`
  (`Module.Basis.invertibleToMatrix`), so its determinant is a unit —
  no hand-rolled coordinate pairing.
* **The partition function does not see the basis**
  (`basisGramData_partFn`): reindex the Boltzmann sum along the
  keystone equivalence `ℤ^n ≃ H¹(G;ℤ)` and transport each term by the
  chart identity `basisGramData_energy_latticeQuot` — no `GL(n,ℤ)`
  matrices in the proof.

The graph-level readout: `IncidenceGraph.partFn`, with
`basisGramData_partFn` saying every basis computes it. -/

namespace Meno

open scoped BigOperators
open Matrix

universe u v

namespace IncidenceGraph

variable (G : IncidenceGraph.{u, v})

/-- **C3's acceptance**: any two lattice bases of the same graph are
related by a unimodular change of basis — the change-of-basis matrix
is integral with unit determinant, and it recombines one basis's
cycles into the other's. -/
theorem exists_unimodular_relating {n : ℕ}
    (B B' : Module.Basis (Fin n) ℤ G.cycleLattice) :
    ∃ U : Matrix (Fin n) (Fin n) ℤ, IsUnit U.det ∧
      ∀ j, G.cyclesZ B' j = fun e => ∑ i, U i j * G.cyclesZ B i e := by
  letI := B.invertibleToMatrix B'
  refine ⟨B.toMatrix ⇑B', Matrix.isUnit_det_of_invertible _, fun j => ?_⟩
  have h : ∑ i, B.toMatrix ⇑B' i j • B i = B' j :=
    B.sum_toMatrix_smul_self ⇑B' j
  have hval := congrArg Subtype.val h
  rw [AddSubmonoidClass.coe_finset_sum] at hval
  funext e
  have he := congrFun hval e
  rw [Finset.sum_apply] at he
  exact he.symm

/-- **The partition function of the graph** — computed through the
fundamental basis; every basis agrees (`basisGramData_partFn`). -/
noncomputable def partFn : ℝ :=
  (G.basisGramData G.cycleBasis).toQuadraticAction.toSectorAction.partFn

/-- Every lattice basis's Boltzmann sum is the intrinsic class sum:
reindex along the keystone equivalence and transport each term by the
chart identity. -/
theorem basisGramData_partFn_eq_tsum_classes {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) :
    (G.basisGramData B).toQuadraticAction.toSectorAction.partFn
      = ∑' κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ),
          Real.exp (-(G.harmonicEnergy κ)) := by
  show ∑' k : Fin n → ℤ, Real.exp (-(G.basisGramData B).energy k) = _
  rw [← Equiv.tsum_eq (G.latticeQuotEquiv B).toEquiv
    (fun k => Real.exp (-(G.basisGramData B).energy k))]
  exact tsum_congr fun κ => by
    rw [show ((G.latticeQuotEquiv B).toEquiv κ : Fin n → ℤ)
        = G.latticeQuotEquiv B κ from rfl,
      G.basisGramData_energy_latticeQuot B κ]

/-- **The partition function does not see the basis** (C3): every
lattice basis computes the graph's partition function. -/
theorem basisGramData_partFn {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) :
    (G.basisGramData B).toQuadraticAction.toSectorAction.partFn
      = G.partFn := by
  rw [G.basisGramData_partFn_eq_tsum_classes B,
    ← G.basisGramData_partFn_eq_tsum_classes G.cycleBasis]
  rfl

end IncidenceGraph

end Meno
