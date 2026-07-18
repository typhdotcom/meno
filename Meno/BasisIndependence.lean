import Meno.HarmonicClass
import Mathlib.LinearAlgebra.Matrix.Basis

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

/-! ## The intrinsic carrier

The thesis's carrier, as one object (review #6, finding 1): the sector
lattice is `H¹(G;ℤ)` and the action is the harmonic energy — the
positive-definite quadratic action in intrinsic form, with the zero
class as vacuum. Every basis-coordinate quadratic action is a *chart*
of this carrier: the keystone equivalence `latticeQuotEquiv B`
transports the energies (`classSectorAction_energy`) and the partition
functions agree (`classSectorAction_partFn`,
`basisGramData_partFn_eq_classSectorAction`). The finite-resolution
reductions of this carrier live in `Meno/ResolutionCount.lean`
(`h1ResQuotEquiv`, `uniformComplexity_split_carrier`). -/

/-- The class weights are summable — transported from the fundamental
basis's sector action along the keystone equivalence. -/
theorem summable_classWeight :
    Summable (fun κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) =>
      Real.exp (-G.harmonicEnergy κ)) := by
  have h := (Equiv.summable_iff (G.h1QuotEquiv.toEquiv)
    (f := fun k : Fin G.b1 → ℤ =>
      Real.exp (-((G.basisGramData G.cycleBasis).energy k)))).mpr
    (G.basisGramData G.cycleBasis).toQuadraticAction.toSectorAction.summable
  exact h.congr fun κ => rfl

/-- **The intrinsic polarized form on `H¹(G;ℤ)`** (review #7): the
Gram bilinear form of the fundamental basis at the classes' keystone
coordinates. Basis-independent by `classForm_chart`. -/
noncomputable def classForm
    (κ κ' : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) : ℝ :=
  (G.basisGramData G.cycleBasis).interaction
    (G.h1QuotEquiv κ) (G.h1QuotEquiv κ')

/-- The quadratic law: the harmonic energy is the form's diagonal. -/
theorem classForm_self (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :
    G.classForm κ κ = G.harmonicEnergy κ := rfl

theorem classForm_comm (κ κ') : G.classForm κ κ' = G.classForm κ' κ := by
  unfold classForm HarmonicGramData.interaction
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show (G.basisGramData G.cycleBasis).gram j i
      = (G.basisGramData G.cycleBasis).gram i j from by
    have h := (G.basisGramData G.cycleBasis).gram_symm
    calc (G.basisGramData G.cycleBasis).gram j i
        = (G.basisGramData G.cycleBasis).gramᵀ i j := rfl
      _ = (G.basisGramData G.cycleBasis).gram i j := by rw [h]]
  ring

theorem classForm_add_left (κ₁ κ₂ κ') :
    G.classForm (κ₁ + κ₂) κ' = G.classForm κ₁ κ' + G.classForm κ₂ κ' := by
  unfold classForm HarmonicGramData.interaction
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_add]
  push_cast [Pi.add_apply]
  ring

/-- Positive-definiteness of the intrinsic form. -/
theorem classForm_posDef (κ) (hκ : κ ≠ 0) : 0 < G.classForm κ κ := by
  rw [G.classForm_self]
  exact G.harmonicEnergy_pos hκ

/-- **THE INTRINSIC QUADRATIC-LATTICE ACTION** (review #7): the
thesis's carrier as one bundled object — the lattice `H¹(G;ℤ)` with
the positive-definite polarized form `classForm`, summable. Every
basis chart is a form-preserving linear equivalence
(`classForm_chart` + `latticeQuotEquiv`). -/
noncomputable def classQuadAction : QuadLatticeAction.{v} where
  Λ := (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)
  form := G.classForm
  form_comm := G.classForm_comm
  form_add_left := G.classForm_add_left
  form_posDef := fun κ hκ => G.classForm_posDef κ hκ
  summable := G.summable_classWeight

/-- **THE INTRINSIC CARRIER** (review #6, finding 1): the analytic
projection of the intrinsic quadratic-lattice action (review #7) —
the sector lattice `H¹(G;ℤ)` with the harmonic energy
`E κ = classForm κ κ`, as a `SectorAction`. -/
noncomputable def classSectorAction : SectorAction.{v} :=
  (G.classQuadAction).toSectorAction

/-- The carrier's energy is the harmonic energy — definitionally. -/
theorem classSectorAction_E :
    (G.classSectorAction).E = G.harmonicEnergy := rfl

/-- **Basis charts preserve the form** (review #7): the Gram
interaction of any basis at the keystone coordinates is the intrinsic
polarized form — via polarization from the chart identity for
energies, with no coordinate transport. -/
theorem classForm_chart {n : ℕ} (B : Module.Basis (Fin n) ℤ G.cycleLattice)
    (κ κ' : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :
    (G.basisGramData B).interaction
        (G.latticeQuotEquiv B κ) (G.latticeQuotEquiv B κ')
      = G.classForm κ κ' := by
  have hpol : ∀ (H : HarmonicGramData G.V) (a b : Fin H.r → ℤ),
      H.interaction a b = (H.energy (a + b) - H.energy a - H.energy b) / 2 := by
    intro H a b
    have h := H.energy_add a b
    linarith
  show _ = (G.basisGramData G.cycleBasis).interaction
    (G.h1QuotEquiv κ) (G.h1QuotEquiv κ')
  rw [hpol, hpol]
  have h1 : (G.basisGramData B).energy
      (G.latticeQuotEquiv B κ + G.latticeQuotEquiv B κ')
      = (G.basisGramData G.cycleBasis).energy
        (G.h1QuotEquiv κ + G.h1QuotEquiv κ') := by
    rw [show G.latticeQuotEquiv B κ + G.latticeQuotEquiv B κ'
        = G.latticeQuotEquiv B (κ + κ') from (map_add _ κ κ').symm,
      show G.h1QuotEquiv κ + G.h1QuotEquiv κ'
        = G.h1QuotEquiv (κ + κ') from (map_add _ κ κ').symm,
      G.basisGramData_energy_latticeQuot B (κ + κ')]
    rfl
  have h2 := G.basisGramData_energy_latticeQuot B κ
  have h3 := G.basisGramData_energy_latticeQuot B κ'
  rw [h1, h2, h3]
  rfl

/-- The carrier's sector lattice is `H¹(G;ℤ)` — definitionally. -/
theorem classSectorAction_Λ :
    (G.classSectorAction).Λ
      = ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) := rfl

/-- **Every basis action is a chart of the carrier** (energy half):
the keystone equivalence carries the basis-coordinate energy to the
intrinsic harmonic energy. -/
theorem classSectorAction_energy {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice)
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :
    ((G.basisGramData B).toQuadraticAction.toSectorAction).E
        (G.latticeQuotEquiv B κ)
      = (G.classSectorAction).E κ := by
  show (G.basisGramData B).toQuadraticAction.energy (G.latticeQuotEquiv B κ)
    = G.harmonicEnergy κ
  rw [(G.basisGramData B).toQuadraticAction_energy]
  exact G.basisGramData_energy_latticeQuot B κ

/-- The intrinsic carrier's partition function is the graph's. -/
theorem classSectorAction_partFn :
    (G.classSectorAction).partFn = G.partFn := by
  show (∑' κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ),
      Real.exp (-G.harmonicEnergy κ)) = G.partFn
  rw [← G.basisGramData_partFn_eq_tsum_classes G.cycleBasis]
  rfl

/-- **Every basis action is a chart of the carrier** (partition
half): the basis-coordinate Boltzmann sum equals the carrier's. -/
theorem basisGramData_partFn_eq_classSectorAction {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) :
    (G.basisGramData B).toQuadraticAction.toSectorAction.partFn
      = (G.classSectorAction).partFn := by
  rw [G.basisGramData_partFn B, G.classSectorAction_partFn]


/-- **Uncertainty on the intrinsic carrier** (review #7): the Gibbs
variance of any observable of the matter classes, against the
carrier's Boltzmann weights, is nonnegative — Gibbs fluctuation
specialized from the generic `SectorAction` law to
`classSectorAction`. -/
theorem classSectorAction_gibbsVariance_nonneg
    (f : ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) → ℝ)
    (hsq : Summable (fun κ => f κ ^ 2 * (G.classSectorAction).gibbsMass κ))
    (hf : Summable (fun κ => f κ * (G.classSectorAction).gibbsMass κ)) :
    0 ≤ (G.classSectorAction).gibbsVariance f :=
  (G.classSectorAction).gibbsVariance_nonneg f hsq hf

end IncidenceGraph

end Meno
