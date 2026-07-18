import Meno.HarmonicClass
import Meno.LatticeAction
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

private lemma interaction_single {W : Type*} (H : HarmonicGramData W)
    (i j : Fin H.r) :
    H.interaction (Pi.single i 1) (Pi.single j 1) = H.gram i j := by
  show ∑ k, ∑ l, H.gram k l * ((Pi.single i 1 : Fin H.r → ℤ) k : ℝ)
      * ((Pi.single j 1 : Fin H.r → ℤ) l : ℝ) = H.gram i j
  rw [Finset.sum_eq_single i
    (fun k _ hk => by simp [Pi.single_eq_of_ne hk])
    (fun h => absurd (Finset.mem_univ i) h)]
  rw [Finset.sum_eq_single j
    (fun l _ hl => by simp [Pi.single_eq_of_ne hl])
    (fun h => absurd (Finset.mem_univ j) h)]
  simp

/-- The Gram entries of the intrinsic form at the induced `H¹` basis
are the basis's Gram data — `classForm_chart` at the standard basis
vectors. -/
theorem classForm_h1Basis {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) (i j : Fin n) :
    G.classForm (G.h1Basis B i) (G.h1Basis B j)
      = (G.basisGramData B).gram i j := by
  rw [← G.classForm_chart B, latticeQuotEquiv_h1Basis, latticeQuotEquiv_h1Basis]
  exact interaction_single (G.basisGramData B) i j

/-- **THE INTRINSIC QUADRATIC-LATTICE ACTION** (review #7): the
thesis's carrier as one bundled object — the lattice `H¹(G;ℤ)` with
the polarized form `classForm`, positive definite on the **real scalar
extension** (review #9): the field is discharged from the Gram chart
of the fundamental basis (`bilinBaseChange_posDef_of_gram`), and
integral positivity and summability are theorems of the bundle. Every
basis chart is a form-preserving linear equivalence
(`classForm_chart`, `chartAction_h1Basis`). -/
noncomputable def classQuadAction : QuadLatticeAction.{v} where
  Λ := (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)
  form := G.classForm
  form_comm := G.classForm_comm
  form_add_left := G.classForm_add_left
  posDef_baseChange := by
    refine bilinBaseChange_posDef_of_gram _ _ _ (G.h1Basis G.cycleBasis) ?_
    have hmat : (Matrix.of fun i j =>
          G.classForm (G.h1Basis G.cycleBasis i) (G.h1Basis G.cycleBasis j))
        = (G.basisGramData G.cycleBasis).gram := by
      ext i j
      rw [Matrix.of_apply]
      exact G.classForm_h1Basis G.cycleBasis i j
    rw [hmat]
    exact (G.basisGramData G.cycleBasis).gram_posDef

/-- **THE INTRINSIC CARRIER** (review #6, finding 1): the analytic
projection of the intrinsic quadratic-lattice action (review #7) —
the sector lattice `H¹(G;ℤ)` with the harmonic energy
`E κ = classForm κ κ`, as a `SectorAction`. -/
noncomputable def classSectorAction : SectorAction.{v} :=
  (G.classQuadAction).toSectorAction

/-- The carrier's energy is the harmonic energy — definitionally. -/
theorem classSectorAction_E :
    (G.classSectorAction).E = G.harmonicEnergy := rfl

/-- **The carrier's rank is `b₁`** (review #8): the intrinsic lattice
is finite free of exactly the graph's first Betti number. -/
theorem classQuadAction_rank : (G.classQuadAction).rank = G.b1 := by
  show Module.finrank ℤ ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) = G.b1
  rw [G.h1QuotEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin]

/-- **Every basis charts the carrier bundle** (review #9): the chart
of `classQuadAction` at the induced `H¹` basis is precisely the
basis's coordinate quadratic action. -/
theorem chartAction_h1Basis {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) :
    (G.classQuadAction).chartAction (G.h1Basis B)
      = (G.basisGramData B).toQuadraticAction :=
  QuadraticAction.eq_of_Q_eq (by
    ext i j
    rw [QuadLatticeAction.chartAction_Q, HarmonicGramData.toQuadraticAction_Q,
      QuadLatticeAction.gram_apply]
    exact G.classForm_h1Basis B i j)

/-- **The carrier's intrinsic Siegel–Poisson duality** (review #9):
the dual lattice of `H¹(G;ℤ)` against the carrier, prefactor
`√(disc / π^{b₁})` — no basis in the statement. -/
theorem classQuadAction_duality :
    (↑((G.classQuadAction).dual.toSectorAction.partFn) : ℂ)
      = ↑((G.classQuadAction).disc / Real.pi ^ G.b1 : ℝ) ^ ((1 : ℂ) / 2)
        * ↑((G.classQuadAction).toSectorAction.partFn) := by
  have h := (G.classQuadAction).duality
  rwa [G.classQuadAction_rank] at h

/-- **Every chart's coordinate action receives the Siegel–Poisson
duality — as a corollary of the intrinsic duality** (review #9): chart
the carrier and its dual at `B` (`chartAction_h1Basis`,
`chartAction_dual`), transport the partition functions
(`partFn_chartAction`), and read the discriminant through `disc_eq`.
The coordinate theorem `QuadraticAction.duality` is consumed once,
inside `QuadLatticeAction.duality` — not replayed per basis. -/
theorem basisGramData_duality {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) :
    (↑((G.basisGramData B).toQuadraticAction.dual.toSectorAction.partFn) : ℂ)
      = ↑(((G.basisGramData B).toQuadraticAction.Q.det) / Real.pi ^ n : ℝ)
          ^ ((1 : ℂ) / 2)
        * ↑((G.basisGramData B).toQuadraticAction.toSectorAction.partFn) := by
  have hchart := G.chartAction_h1Basis B
  have hdualpartFn :
      (G.basisGramData B).toQuadraticAction.dual.toSectorAction.partFn
        = (G.classQuadAction).dual.toSectorAction.partFn := by
    rw [← hchart, ← QuadLatticeAction.chartAction_dual]
    exact (G.classQuadAction).dual.partFn_chartAction (G.h1Basis B).dualBasis
  have hpartFn :
      (G.basisGramData B).toQuadraticAction.toSectorAction.partFn
        = (G.classQuadAction).toSectorAction.partFn := by
    rw [← hchart]
    exact (G.classQuadAction).partFn_chartAction (G.h1Basis B)
  have hdet : (G.basisGramData B).toQuadraticAction.Q.det
      = (G.classQuadAction).disc := by
    rw [← hchart, QuadLatticeAction.chartAction_Q]
    exact ((G.classQuadAction).disc_eq (G.h1Basis B)).symm
  have hrank : n = (G.classQuadAction).rank :=
    (G.classQuadAction).card_eq_rank (G.h1Basis B)
  rw [hdualpartFn, hpartFn, hdet, hrank]
  exact (G.classQuadAction).duality

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

/-! ## The intrinsic dual identified with graph homology (review #10)

The abstract dual lattice `Module.Dual ℤ H¹(G;ℤ)` *is* the cycle
lattice `H₁(G;ℤ)`, through the period-evaluation pairing
(`cyclesDualEquiv`, `Meno/GraphHomology.lean`). Transported across it,
the dual action's form is `π²` times the **unit-edge chain pairing**
of cycles (`dualForm_cyclesDualEquiv`), the priced cycle lattice is a
`QuadLatticeAction` in its own right (`cycleAction`), the pairing is a
form-preserving equivalence (`cycleActionEquivDual`), and the
Siegel–Poisson duality holds **directly between harmonic `H¹` sectors
and priced `H₁` cycles** (`cycle_harmonic_duality`) — the topological
meaning of the intrinsic dual. -/

/-- The Gram data of a basis is the inverse chain Gram —
definitionally. -/
theorem basisGramData_gram {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) :
    (G.basisGramData B).gram = (gramOf (G.cyclesR B))⁻¹ := rfl

/-- The carrier's Gram at the induced `H¹` basis is the basis's Gram
data, in matrix form. -/
theorem classQuadAction_gram_h1Basis {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) :
    (G.classQuadAction).gram (G.h1Basis B) = (G.basisGramData B).gram := by
  ext i j
  exact G.classForm_h1Basis B i j

private lemma cast_dot_cyclesB {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) (i j : Fin n) :
    ((G.cyclesZ B i ⬝ᵥ G.cyclesZ B j : ℤ) : ℝ)
      = gramOf (G.cyclesR B) i j :=
  (G.cast_periods B (G.cyclesZ B i) j).symm

private lemma cast_dot_cycles (i j : Fin G.b1) :
    ((G.cyclesZ G.cycleBasis i ⬝ᵥ G.cyclesZ G.cycleBasis j : ℤ) : ℝ)
      = gramOf (G.cyclesR G.cycleBasis) i j :=
  G.cast_dot_cyclesB G.cycleBasis i j

/-- **The priced cycle lattice**: `H₁(G;ℤ)` with `π²` times the
unit-edge chain pairing — the topological carrier of the intrinsic
dual (review #10). Real positivity discharges from the chain Gram of
the fundamental cycles. -/
noncomputable def cycleAction : QuadLatticeAction.{v} where
  Λ := ↥G.cycleLattice
  form := fun c c' =>
    Real.pi ^ 2 * (((c : G.E → ℤ) ⬝ᵥ (c' : G.E → ℤ) : ℤ) : ℝ)
  form_comm := fun c c' => by rw [dotProduct_comm]
  form_add_left := fun c₁ c₂ c' => by
    rw [Submodule.coe_add, add_dotProduct]
    push_cast
    ring
  posDef_baseChange := by
    refine bilinBaseChange_posDef_of_gram _ _ _ G.cycleBasis ?_
    have hmat : (Matrix.of fun i j => Real.pi ^ 2
          * (((G.cycleBasis i : G.E → ℤ) ⬝ᵥ (G.cycleBasis j : G.E → ℤ)
              : ℤ) : ℝ))
        = Real.pi ^ 2 • gramOf (G.cyclesR G.cycleBasis) := by
      ext i j
      rw [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      congr 1
      exact G.cast_dot_cycles i j
    rw [hmat]
    exact posDef_smul' (G.gramOf_cyclesR_posDef G.cycleBasis) (by positivity)

private lemma dualForm_dualBasis_cycles (i j : Fin G.b1) :
    (G.classQuadAction).dualForm ((G.h1Basis G.cycleBasis).dualBasis i)
        ((G.h1Basis G.cycleBasis).dualBasis j)
      = Real.pi ^ 2 * gramOf (G.cyclesR G.cycleBasis) i j := by
  have hunit : IsUnit (gramOf (G.cyclesR G.cycleBasis)).det :=
    isUnit_iff_ne_zero.mpr
      (ne_of_gt (G.gramOf_cyclesR_posDef G.cycleBasis).det_pos)
  refine ((G.classQuadAction).dualForm_dualBasis
    (G.h1Basis G.cycleBasis) i j).trans ?_
  congr 1
  rw [G.classQuadAction_gram_h1Basis, G.basisGramData_gram,
    Matrix.nonsing_inv_nonsing_inv _ hunit]

/-- **The dual's form on cycles is `π²` times the unit-edge chain
pairing** (review #10): transporting the intrinsic dual across
period evaluation lands on the priced cycle lattice. -/
theorem dualForm_cyclesDualEquiv (c c' : ↥G.cycleLattice) :
    (G.classQuadAction).dualForm (G.cyclesDualEquiv c) (G.cyclesDualEquiv c')
      = Real.pi ^ 2 * (((c : G.E → ℤ) ⬝ᵥ (c' : G.E → ℤ) : ℤ) : ℝ) := by
  have hL := (G.classQuadAction).dual.form_repr
    (G.h1Basis G.cycleBasis).dualBasis
    (G.cyclesDualEquiv c) (G.cyclesDualEquiv c')
  have hR := (G.cycleAction).form_repr G.cycleBasis c c'
  show (G.classQuadAction).dual.form (G.cyclesDualEquiv c)
      (G.cyclesDualEquiv c')
    = (G.cycleAction).form c c'
  rw [hL, hR]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  · congr 1
    · exact congrArg _ (G.cyclesDualEquiv_repr c i)
    · exact congrArg _ (G.cyclesDualEquiv_repr c' j)
  · show (G.classQuadAction).dualForm ((G.h1Basis G.cycleBasis).dualBasis i)
        ((G.h1Basis G.cycleBasis).dualBasis j)
      = (G.cycleAction).form (G.cycleBasis i) (G.cycleBasis j)
    rw [G.dualForm_dualBasis_cycles i j]
    show Real.pi ^ 2 * gramOf (G.cyclesR G.cycleBasis) i j
      = Real.pi ^ 2
        * (((G.cycleBasis i : G.E → ℤ) ⬝ᵥ (G.cycleBasis j : G.E → ℤ)
            : ℤ) : ℝ)
    congr 1
    exact (G.cast_dot_cycles i j).symm

/-- **The intrinsic dual IS priced graph homology** (review #10): the
period-evaluation equivalence is form-preserving from the priced cycle
lattice onto the carrier's dual action. -/
noncomputable def cycleActionEquivDual :
    (G.cycleAction).Equiv (G.classQuadAction).dual where
  toLinearEquiv := G.cyclesDualEquiv
  form_eq := fun c c' => G.dualForm_cyclesDualEquiv c c'

/-- **SIEGEL–POISSON BETWEEN HOMOLOGY AND COHOMOLOGY** (review #10):
the Boltzmann sum of the priced cycles — `H₁(G;ℤ)` with `π²` times
the unit-edge chain pairing — against the harmonic classes, with the
basis-independent prefactor. Cycles are the dual sectors of harmonic
cohomology: the topological meaning of the intrinsic dual. -/
theorem cycle_harmonic_duality :
    (↑((G.cycleAction).toSectorAction.partFn) : ℂ)
      = ↑((G.classQuadAction).disc / Real.pi ^ G.b1 : ℝ) ^ ((1 : ℂ) / 2)
        * ↑((G.classQuadAction).toSectorAction.partFn) := by
  rw [← (G.cycleActionEquivDual).partFn_eq]
  exact G.classQuadAction_duality

/-- **The symmetric topological statement** (review #11): the carrier
itself is form-equivalent to the dual of the priced cycle lattice —
harmonic cohomology *is* the dual of priced homology, derived in the
equivalence calculus: the involution's inverse composed with the
dualized period-evaluation equivalence. -/
noncomputable def classActionEquivCycleDual :
    (G.classQuadAction).Equiv (G.cycleAction).dual :=
  ((G.classQuadAction).dualDual.symm).trans (G.cycleActionEquivDual).dual

/-! ### Chart interfaces for concrete consumers (review #11)

The flagship graphs re-derive their coordinate dualities from
`cycle_harmonic_duality`; these lemmas read the intrinsic objects in
any basis's coordinates. -/

/-- The homology action's Gram at any basis is `π²` times the chain
Gram of the basis cycles. -/
theorem cycleAction_gram {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) :
    (G.cycleAction).gram B = Real.pi ^ 2 • gramOf (G.cyclesR B) := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  show Real.pi ^ 2 * (((B i : G.E → ℤ) ⬝ᵥ (B j : G.E → ℤ) : ℤ) : ℝ) = _
  congr 1
  exact G.cast_dot_cyclesB B i j

/-- The carrier's discriminant, in any basis's coordinates: the
determinant of the inverse chain Gram. -/
theorem classQuadAction_disc {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) :
    (G.classQuadAction).disc = ((gramOf (G.cyclesR B))⁻¹).det := by
  refine ((G.classQuadAction).disc_eq (G.h1Basis B)).trans ?_
  rw [G.classQuadAction_gram_h1Basis, G.basisGramData_gram]

/-- The carrier's partition function is the graph's. -/
theorem classQuadAction_partFn :
    (G.classQuadAction).toSectorAction.partFn = G.partFn :=
  G.classSectorAction_partFn

end IncidenceGraph

end Meno
