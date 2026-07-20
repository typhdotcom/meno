import Meno.GraphInstances
import Meno.Matter
import Meno.ResolutionCount
import Meno.Systole
import Meno.BindingSign

/-! # The Theta Graph: the First Non-Diagonal Harmonic Gram Form

The subdivided theta graph `K₂,₃` — two junction vertices joined by
three internal-vertex paths — is the smallest graph whose harmonic Gram
form is **not diagonal**: its two independent cycles share a path, so
the periods couple. This file derives that Gram form from the graph's
topology by variational minimization and feeds it to the general
Siegel–Poisson duality (`Meno/SiegelPoisson.lean`), giving Phase 15 its
first genuinely non-diagonal consumer.

The presentation is the lattice basis `thetaLatticeBasis`
(`Meno/GraphInstances.lean`, review #5) — everything priced here is
**derived** from it: the chain Gram `!![4, 2; 2, 4]` is the unit-edge
Gram of the basis (`basisGramData_theta_gram` ties the derived pricing
to the literal closed form), the period Gram is its inverse
`!![1/3, −1/6; −1/6, 1/3]`, and the sector physics (matter, mass,
binding, resolution counts) flows through the graph-level machinery. -/

namespace Meno

open scoped BigOperators
open Matrix

section Theta

/-! ### The chain Gram and its inverse, in closed form -/

/-- The cycle-chain Gram matrix of `K₂,₃`: paths have length two, and
distinct basis cycles share (only) the third path. -/
theorem gramOf_thetaCycles : gramOf thetaCycles = !![4, 2; 2, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [gramOf, dotProduct, thetaCycles, Fin.sum_univ_six] <;>
    norm_num

/-- The chain Gram matrix is positive definite. -/
theorem thetaChainGram_posDef :
    (!![4, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · show (!![4, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℝ)ᴴ = !![4, 2; 2, 4]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · have hcomp : star x ⬝ᵥ (!![4, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℝ).mulVec x
        = 4 * x 0 ^ 2 + 4 * (x 0 * x 1) + 4 * x 1 ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Pi.star_apply]
      ring
    rw [hcomp]
    have h01 : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hx (funext fun i => by fin_cases i <;> simp [hc.1, hc.2])
    rcases h01 with h0 | h1
    · nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 1),
        lt_of_le_of_ne (sq_nonneg (x 0)) (Ne.symm (pow_ne_zero 2 h0))]
    · nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0),
        lt_of_le_of_ne (sq_nonneg (x 1)) (Ne.symm (pow_ne_zero 2 h1))]

/-- The harmonic period Gram form: the inverse of the chain Gram. -/
theorem thetaChainGram_inv :
    (!![4, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
      = !![1/3, -(1/6); -(1/6), 1/3] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-! ### The derived pricing of the lattice basis -/

/-- The lattice basis's cast cycles are the theta cycles. -/
theorem cyclesR_thetaLatticeBasis :
    thetaGraph.cyclesR thetaLatticeBasis = thetaCycles := by
  funext i e
  show ((thetaGraph.cyclesZ thetaLatticeBasis i e : ℤ) : ℝ) = thetaCycles i e
  rw [cyclesZ_thetaLatticeBasis]
  exact (thetaCycles_eq_cast i e).symm

/-- **The derived pricing equals the closed form**: the Gram form of
the theta basis's priced Gram data — the inverse unit-edge chain Gram,
with nothing stored (review #5, finding 3) — is the literal
`!![1/3, −1/6; −1/6, 1/3]`. -/
theorem basisGramData_theta_gram :
    (thetaGraph.basisGramData thetaLatticeBasis).gram
      = !![1/3, -(1/6); -(1/6), 1/3] := by
  show (gramOf (thetaGraph.cyclesR thetaLatticeBasis))⁻¹ = _
  rw [cyclesR_thetaLatticeBasis, gramOf_thetaCycles, thetaChainGram_inv]

/-- C5's acceptance witness for theta: the hand-built basis is a
unimodular recombination of the fundamental one (C3's
`exists_unimodular_relating`; the cycle and wedge instances live in
`Meno/WedgePresentation.lean`). -/
theorem thetaLatticeBasis_unimodular_related :
    ∃ U : Matrix (Fin thetaGraph.b1) (Fin thetaGraph.b1) ℤ,
      IsUnit U.det ∧
      ∀ j, thetaGraph.cyclesZ
          (thetaLatticeBasis.reindex
            (finCongr (thetaGraph.card_eq_b1 thetaLatticeBasis))) j
        = fun e => ∑ i, U i j * thetaGraph.cyclesZ thetaGraph.cycleBasis i e :=
  thetaGraph.exists_unimodular_relating thetaGraph.cycleBasis
    (thetaLatticeBasis.reindex
      (finCongr (thetaGraph.card_eq_b1 thetaLatticeBasis)))

/-- The period Gram form is positive definite (inverse of a
positive-definite matrix). -/
theorem thetaGram_posDef :
    (!![1/3, -(1/6); -(1/6), 1/3] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  rw [← thetaChainGram_inv]
  exact posDef_inv thetaChainGram_posDef

/-- **The harmonic Gram data of the theta graph** — the first
non-diagonal instance in the spine. The Gram form is derived from the
graph (`basisGramData_theta_gram`), not asserted. -/
noncomputable def thetaHarmonicGramData : HarmonicGramData (Fin 5) where
  r := 2
  gram := !![1/3, -(1/6); -(1/6), 1/3]
  gram_posDef := thetaGram_posDef

/-- The Gram matrix of the theta data, in literal form. -/
theorem thetaHarmonicGramData_gram :
    thetaHarmonicGramData.gram = !![1/3, -(1/6); -(1/6), 1/3] := rfl

/-- The Gram form genuinely couples the two sectors: the off-diagonal
entry is `−1/6 ≠ 0`. No diagonal machinery could have produced this
instance. -/
theorem thetaGram_offDiag_ne_zero :
    (!![1/3, -(1/6); -(1/6), 1/3] : Matrix (Fin 2) (Fin 2) ℝ) 0 1 ≠ 0 := by
  norm_num


/-- The theta graph has matter: the intrinsic class of the single-edge
cochain with periods `(1, 0)` (C6). Mass, the variational identity,
no-potential, and annihilation all come from the intrinsic
`MatterSector` API. -/
noncomputable def thetaMatter : MatterSector thetaGraph :=
  ⟨Submodule.Quotient.mk ![1, 0, 0, 0, 0, 0], by
    intro h0
    have h := congrArg (thetaGraph.latticeQuotEquiv thetaLatticeBasis) h0
    rw [map_zero] at h
    have h1 : (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ)
        ⬝ᵥ thetaGraph.cyclesZ thetaLatticeBasis 0 = 0 := congrFun h 0
    rw [cyclesZ_thetaLatticeBasis] at h1
    rw [show (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ) ⬝ᵥ thetaCyclesZ 0
        = (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ) ⬝ᵥ ![1, 1, 0, 0, -1, -1]
      from rfl] at h1
    exact absurd h1 (by decide)⟩

/-- The theta matter's keystone coordinates against the theta basis
are `(1, 0)`. -/
theorem thetaMatter_coords :
    thetaGraph.latticeQuotEquiv thetaLatticeBasis thetaMatter.val
      = ![1, 0] := by
  funext j
  show (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ)
    ⬝ᵥ thetaGraph.cyclesZ thetaLatticeBasis j = ![1, 0] j
  rw [cyclesZ_thetaLatticeBasis]
  fin_cases j
  · show (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ) ⬝ᵥ ![1, 1, 0, 0, -1, -1] = 1
    decide
  · show (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ) ⬝ᵥ ![0, 0, 1, 1, -1, -1] = 0
    decide

/-- The theta matter's mass is `1/3` — the intrinsic harmonic energy,
computed through the theta basis's chart (C6). -/
theorem thetaMatter_mass : thetaMatter.mass = 1/3 := by
  rw [← thetaMatter.mass_chart thetaLatticeBasis, thetaMatter_coords]
  show ∑ i, ∑ j, (gramOf (thetaGraph.cyclesR thetaLatticeBasis))⁻¹ i j
      * ((![1, 0] : Fin 2 → ℤ) i : ℝ) * ((![1, 0] : Fin 2 → ℤ) j : ℝ) = 1/3
  rw [cyclesR_thetaLatticeBasis, gramOf_thetaCycles, thetaChainGram_inv]
  norm_num [Fin.sum_univ_two]

/-- **The first non-diagonal consumer of the general Siegel–Poisson
duality — now through the topology** (review #11): the theta duality
is `cycle_harmonic_duality` at the theta graph, read in the
`thetaLatticeBasis` chart. The dual side is the priced cycle lattice
(`cycleAction_gram`: `π²` times the chain Gram `!![4,2;2,4]`), the
harmonic side is the graph partition function, and the prefactor is
the carrier discriminant `det !![1/3,−1/6;−1/6,1/3] = 1/12`. The
coordinate `QuadraticAction.duality` is not called here — it is
consumed once, inside the intrinsic proof. -/
theorem theta_siegelPoisson_duality :
    (↑(thetaHarmonicGramData.toQuadraticAction.dual.toSectorAction.partFn) : ℂ)
      = ↑((1/12 : ℝ) / Real.pi ^ 2) ^ ((1 : ℂ) / 2)
        * ↑(thetaHarmonicGramData.toQuadraticAction.toSectorAction.partFn) := by
  have hb1 : thetaGraph.b1 = 2 :=
    (thetaGraph.card_eq_b1 thetaLatticeBasis).symm
  have hchain : IsUnit (!![4, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℝ).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt thetaChainGram_posDef.det_pos)
  have hdual :
      thetaHarmonicGramData.toQuadraticAction.dual.toSectorAction.partFn
        = (thetaGraph.cycleAction).toSectorAction.partFn := by
    rw [← (thetaGraph.cycleAction).partFn_chartAction thetaLatticeBasis]
    refine QuadraticAction.partFn_eq_of_Q_eq _ _ ?_
    rw [QuadraticAction.dual_Q, QuadLatticeAction.chartAction_Q,
      thetaGraph.cycleAction_gram thetaLatticeBasis,
      cyclesR_thetaLatticeBasis, gramOf_thetaCycles,
      HarmonicGramData.toQuadraticAction_Q, thetaHarmonicGramData_gram,
      ← thetaChainGram_inv, Matrix.nonsing_inv_nonsing_inv _ hchain]
  have hharm :
      thetaHarmonicGramData.toQuadraticAction.toSectorAction.partFn
        = (thetaGraph.classQuadAction).toSectorAction.partFn := by
    rw [thetaGraph.classQuadAction_partFn,
      ← thetaGraph.basisGramData_partFn thetaLatticeBasis]
    refine QuadraticAction.partFn_eq_of_Q_eq _ _ ?_
    rw [HarmonicGramData.toQuadraticAction_Q,
      HarmonicGramData.toQuadraticAction_Q, thetaHarmonicGramData_gram,
      basisGramData_theta_gram]
  have hdisc : (thetaGraph.classQuadAction).disc = (1/12 : ℝ) := by
    rw [thetaGraph.classQuadAction_disc thetaLatticeBasis,
      cyclesR_thetaLatticeBasis, gramOf_thetaCycles, thetaChainGram_inv]
    show (!![1/3, -(1/6); -(1/6), 1/3] : Matrix (Fin 2) (Fin 2) ℝ).det = 1/12
    rw [Matrix.det_fin_two]
    norm_num
  have h := thetaGraph.cycle_harmonic_duality
  rw [hb1, hdisc, ← hdual, ← hharm] at h
  exact h

end Theta

/-! ## Binding energy at the Gram level

From the Phase 19 time capsule: gravity re-enters at the Gram level.
The **binding energy** of two sectors is the energy released by joint
minimization, `E(a) + E(b) − E(a+b)`; by polarization it equals
`−2·B(a,b)` where `B` is the Gram bilinear form. Sharing edges makes
the *chain* overlap positive, hence the *period* cross-term negative,
hence the binding positive: **sectors that share roads attract**. For
two cycles of lengths `n₁, n₂` sharing `k` co-oriented edges the exact
value at unit sectors is `2k/(n₁n₂ − k²)` — the capsule's `2k/(n₁n₂)`
is the leading approximation. Theta (`n₁ = n₂ = 4`, `k = 2`) gives
`1/3`, confirmed against the derived Gram form. -/

section Binding

/- The generic binding algebra (`HarmonicGramData.interaction`,
`energy_add`, `bindingEnergy`, `bindingEnergy_eq`, annihilation) was
born here in Phase 19 and moved upstream to `Meno/HarmonicForm.lean`
in Phase 22 — it is pure Gram-data algebra with no theta dependence.
What stays here is theta's concrete numbers and the parametric
shared-cycle oracle. -/

/-- The theta interaction of the two unit sectors is the off-diagonal
`−1/6` — **the closed-form instance** (G6 demotion, PLAN rule 3):
`−⟨c₁,c₂⟩/det = −2/12` through `ofCycles_interaction_fin_two`
(`Meno/BindingSign.lean`), transported to the literal data along the
derived-Gram identification (`basisGramData_theta_gram`). The
independent literal-matrix arithmetic is retired. -/
theorem theta_interaction :
    thetaHarmonicGramData.interaction ![1, 0] ![0, 1] = -(1/6) := by
  have h : (thetaGraph.basisGramData thetaLatticeBasis).interaction
      ![1, 0] ![0, 1]
      = -(thetaGraph.cyclesR thetaLatticeBasis 0
          ⬝ᵥ thetaGraph.cyclesR thetaLatticeBasis 1)
        / (gramOf (thetaGraph.cyclesR thetaLatticeBasis)).det :=
    ofCycles_interaction_fin_two _ _
  have hval : -(thetaGraph.cyclesR thetaLatticeBasis 0
        ⬝ᵥ thetaGraph.cyclesR thetaLatticeBasis 1)
      / (gramOf (thetaGraph.cyclesR thetaLatticeBasis)).det = -(1/6) := by
    rw [cyclesR_thetaLatticeBasis,
      show thetaCycles 0 ⬝ᵥ thetaCycles 1 = gramOf thetaCycles 0 1 from rfl,
      gramOf_thetaCycles]
    norm_num [Matrix.det_fin_two_of]
  have hd := h.trans hval
  show ∑ i, ∑ j, (!![1/3, -(1/6); -(1/6), 1/3] : Matrix (Fin 2) (Fin 2) ℝ) i j
      * ((![1, 0] : Fin 2 → ℤ) i : ℝ) * ((![0, 1] : Fin 2 → ℤ) j : ℝ) = -(1/6)
  rw [← basisGramData_theta_gram]
  exact hd

/-- **Theta sectors bind with energy `1/3`** — positive: the sectors
attract. Confirms the exact shared-cycle formula `2k/(n₁n₂ − k²)` at
`(4, 4, 2)`. -/
theorem theta_bindingEnergy :
    thetaHarmonicGramData.bindingEnergy ![1, 0] ![0, 1] = 1/3 := by
  rw [HarmonicGramData.bindingEnergy_eq, theta_interaction]
  norm_num

/-- Attraction, stated as an inequality: the joint sector is strictly
cheaper than its parts — **the closed form's instance at the
Gram-data level** (demoted at G6, transitively through
`theta_interaction`). The criterion's own strictness witness is
`theta_binding_attractive_class`. -/
theorem theta_binding_attractive :
    thetaHarmonicGramData.energy (![1, 0] + ![0, 1])
      < thetaHarmonicGramData.energy ![1, 0]
        + thetaHarmonicGramData.energy ![0, 1] := by
  have h := theta_bindingEnergy
  unfold HarmonicGramData.bindingEnergy at h
  linarith

/-- **THE CRITERION'S STRICTNESS WITNESS** (G6): the intrinsic
binding energy of the theta classes is positive — the cycles overlap
with `⟨c₁,c₂⟩ = 2 > 0`, and the sign criterion forces attraction.
Proved through the iff's constructive direction
(`binding_attractive_iff`), load-testing the criterion, the chart
identity, and the intrinsic definition in one statement. -/
theorem theta_binding_attractive_class :
    0 < thetaGraph.bindingEnergyClass
        (thetaGraph.h1Basis thetaLatticeBasis 0)
        (thetaGraph.h1Basis thetaLatticeBasis 1) := by
  refine (thetaGraph.binding_attractive_iff thetaLatticeBasis).mpr ?_
  rw [cyclesR_thetaLatticeBasis,
    show thetaCycles 0 ⬝ᵥ thetaCycles 1 = gramOf thetaCycles 0 1 from rfl,
    gramOf_thetaCycles]
  norm_num


end Binding

/-! ## Exactness: matter as trapped inconsistency

The time capsule's third idea, formalized at theta. A 1-cochain is a
system of local constraints ("the potential difference across `e` is
`ω e`"). A **global potential** solves them all; going around a cycle
shows a solution can exist only if the periods vanish. The converse
holds too — zero periods ⟺ a potential exists, the every-graph
theorem `period_eq_zero_iff_exists_grad`. So a
nonzero sector is a constraint system that is locally consistent
everywhere and globally unsatisfiable — and its minimum-energy
representative (`periodRep`) carries positive energy precisely because
no potential can flatten it. Matter is trapped paradox.

This pair (period map surjective — `periodRep_periods`; kernel exactly
the gradients — `period_eq_zero_iff_exists_grad`) is the rank-2 case of the capsule's
keystone: the incompressible residue of local re-description is `b₁`
period coordinates. The description-cost half was completed in C8
(`log_card_sections`, `theta_residue_count`, `theta_gauge_count`):
the keystone is a coding theorem now, not a design problem. -/

section Gauge


end Gauge

/-! ## Theta at every resolution (consumer of `ResolutionCount`) -/

/-- At any resolution `q`, the theta graph's incompressible residue is
exactly `q²` classes — two digits of resolution, one per independent
cycle, at every scale. Direct specialization of the generic keystone
count `card_quotient` (K1); lives here, not in `ResolutionCount.lean`,
so the generic layer never imports a concrete graph. -/
theorem theta_residue_count (q : ℕ) [NeZero q] :
    Nat.card ((Fin 6 → ZMod q)
        ⧸ LinearMap.range (thetaGraph.gradLin (ZMod q)))
      = q ^ 2 :=
  thetaGraph.card_quotient thetaLatticeBasis q

/-- At any resolution `q`, the theta graph's gauge group is `q⁴` — one
`q`-digit per non-cycle edge (`6 − 2` of them). K1's `q²` classes and
this `q⁴` of gauge multiply to `q⁶ = |descriptions|`. -/
theorem theta_gauge_count (q : ℕ) [NeZero q] :
    Nat.card (LinearMap.range (thetaGraph.gradLin (ZMod q))) = q ^ 4 := by
  have hexp : Fintype.card thetaGraph.E - 2 = 4 := by
    show Fintype.card (Fin 6) - 2 = 4
    simp
  rw [thetaGraph.card_gauge thetaLatticeBasis q, hexp]

/-- **The deficit, concretely positive** (review #12): at resolution
`q = 2` the theta graph's Gibbs residue law is strictly below maximal
ignorance — the quadratic action genuinely prices the four finite
sectors, through the strict modal bound of the shifted Gaussian
Fourier expansion (`residueDefect_pos`). -/
theorem theta_residueDefect_pos : 0 < thetaGraph.residueDefect 2 := by
  refine thetaGraph.residueDefect_pos 2 ?_ (by norm_num)
  rw [← thetaGraph.card_eq_b1 thetaLatticeBasis]
  norm_num

/-- The finite reduction's `Fintype` instance, pinned at the theta
graph: `thetaGraph` is reducible, so its projections reduce to
concrete types in instance goals and the generic instance's graph
metavariable cannot be solved by unification — apply it by name. -/
noncomputable local instance :
    Fintype (IncidenceGraph.H1Reduction thetaGraph 2) :=
  thetaGraph.h1ReductionFintype 2

local instance : Nonempty (IncidenceGraph.H1Reduction thetaGraph 2) :=
  thetaGraph.h1ReductionNonempty 2

/-- **The complete positive decomposition, concretely** (review #13):
at resolution `q = 2` the theta graph's uniform complexity decomposes
into the residue action's complexity, its expected energy, and the
deficit — all three strictly positive. The pricing–counting bridge,
fully cashed on an explicit graph. -/
theorem theta_residue_bridge_pos :
    (uniformAction (IncidenceGraph.H1Reduction thetaGraph 2)).complexity
        = (thetaGraph.residueAction 2).complexity
          + (thetaGraph.residueAction 2).gibbsExpect
              (thetaGraph.residueAction 2).E
          + thetaGraph.residueDefect 2
      ∧ 0 < (thetaGraph.residueAction 2).complexity
      ∧ 0 < (thetaGraph.residueAction 2).gibbsExpect
          (thetaGraph.residueAction 2).E
      ∧ 0 < thetaGraph.residueDefect 2 := by
  refine thetaGraph.uniformComplexity_residue_bridge_pos 2 ?_ (by norm_num)
  rw [← thetaGraph.card_eq_b1 thetaLatticeBasis]
  norm_num

noncomputable local instance :
    Fintype (IncidenceGraph.H1Reduction thetaGraph 4) :=
  thetaGraph.h1ReductionFintype 4

/-- **The resolution tower, concretely** (review #14): reducing the
theta graph from resolution `4` to resolution `2` — the coarse
residue action **is** the coarse-graining of the finer one along the
canonical tower map. -/
theorem theta_residueAction_tower :
    (thetaGraph.residueAction 4).coarseGrain
        (⇑(thetaGraph.h1TowerMap 2 4 (by norm_num)))
        0
        (thetaGraph.residueAction_tower_weight_pos 2 4 (by norm_num))
        (thetaGraph.residueAction_tower_weight_le 2 4 (by norm_num))
      = thetaGraph.residueAction 2 :=
  thetaGraph.residueAction_tower 2 4 (by norm_num)

noncomputable local instance :
    DecidableEq (IncidenceGraph.H1Reduction thetaGraph 2) :=
  thetaGraph.h1ReductionDecEq 2

noncomputable local instance :
    Fintype (SGD.Pullback (thetaGraph.carrierCompression 2)
      (thetaGraph.carrierCompression 2)) :=
  thetaGraph.carrierPullbackFintype 2

local instance :
    Nonempty (SGD.Pullback (thetaGraph.carrierCompression 2)
      (thetaGraph.carrierCompression 2)) :=
  thetaGraph.carrierPullbackNonempty 2

/-- **The priced faces on the theta graph at `q = 2`** (reviews #14,
#15): the priced partition-function and complexity gravity
identities, the priced time identity, the **complete residue,
description, and pair bridge packages** — each bridge equality with
its three strictly positive terms — and all **three transported
strict energy variances**. Every face of the program, priced and
strict, on one explicit graph. -/
theorem theta_priced_faces :
    ((thetaGraph.pairAction 2).partFn * (thetaGraph.residueAction 2).partFn
        = (thetaGraph.descriptionAction 2).partFn
          * (thetaGraph.descriptionAction 2).partFn)
      ∧ ((thetaGraph.pairAction 2).complexity
            + (thetaGraph.residueAction 2).complexity
          = (thetaGraph.descriptionAction 2).complexity
            + (thetaGraph.descriptionAction 2).complexity)
      ∧ (sectionCost (thetaGraph.carrierCompression 2)
            / Nat.card (IncidenceGraph.H1Reduction thetaGraph 2)
          = (thetaGraph.descriptionAction 2).complexity
            - (thetaGraph.residueAction 2).complexity)
      ∧ ((uniformAction (IncidenceGraph.H1Reduction thetaGraph 2)).complexity
            = (thetaGraph.residueAction 2).complexity
              + (thetaGraph.residueAction 2).gibbsExpect
                  (thetaGraph.residueAction 2).E
              + thetaGraph.residueDefect 2
          ∧ 0 < (thetaGraph.residueAction 2).complexity
          ∧ 0 < (thetaGraph.residueAction 2).gibbsExpect
              (thetaGraph.residueAction 2).E
          ∧ 0 < thetaGraph.residueDefect 2)
      ∧ ((uniformAction (thetaGraph.E → ZMod 2)).complexity
            = (thetaGraph.descriptionAction 2).complexity
              + (thetaGraph.descriptionAction 2).gibbsExpect
                  (thetaGraph.descriptionAction 2).E
              + thetaGraph.residueDefect 2
          ∧ 0 < (thetaGraph.descriptionAction 2).complexity
          ∧ 0 < (thetaGraph.descriptionAction 2).gibbsExpect
              (thetaGraph.descriptionAction 2).E
          ∧ 0 < thetaGraph.residueDefect 2)
      ∧ ((uniformAction (SGD.Pullback (thetaGraph.carrierCompression 2)
              (thetaGraph.carrierCompression 2))).complexity
            = (thetaGraph.pairAction 2).complexity
              + (thetaGraph.pairAction 2).gibbsExpect
                  (thetaGraph.pairAction 2).E
              + thetaGraph.residueDefect 2
          ∧ 0 < (thetaGraph.pairAction 2).complexity
          ∧ 0 < (thetaGraph.pairAction 2).gibbsExpect
              (thetaGraph.pairAction 2).E
          ∧ 0 < thetaGraph.residueDefect 2)
      ∧ 0 < (thetaGraph.residueAction 2).gibbsVariance
          (thetaGraph.residueAction 2).E
      ∧ 0 < (thetaGraph.descriptionAction 2).gibbsVariance
          (thetaGraph.descriptionAction 2).E
      ∧ 0 < (thetaGraph.pairAction 2).gibbsVariance
          (thetaGraph.pairAction 2).E := by
  have hb : 0 < thetaGraph.b1 := by
    rw [← thetaGraph.card_eq_b1 thetaLatticeBasis]
    norm_num
  exact ⟨thetaGraph.carrier_gravity_partFn 2,
    thetaGraph.carrier_gravity_action 2,
    thetaGraph.sectionCost_carrierCompression_action 2,
    thetaGraph.uniformComplexity_residue_bridge_pos 2 hb (by norm_num),
    thetaGraph.uniformComplexity_description_bridge_pos 2 hb (by norm_num),
    thetaGraph.uniformComplexity_pair_bridge_pos 2 hb (by norm_num),
    thetaGraph.residueAction_gibbsVariance_E_pos 2 hb (by norm_num),
    thetaGraph.descriptionAction_gibbsVariance_E_pos 2 hb (by norm_num),
    thetaGraph.pairAction_gibbsVariance_E_pos 2 hb (by norm_num)⟩

/-! ### The tower on theta (review #15) -/

noncomputable local instance :
    Fintype (IncidenceGraph.H1Reduction thetaGraph 8) :=
  thetaGraph.h1ReductionFintype 8

/-- **The commuting tower triangle on theta** (review #15):
`8 → 4 → 2` composes to `8 → 2`. -/
theorem theta_towerMap_triangle :
    (thetaGraph.h1TowerMap 2 4 (by norm_num)).comp
        (thetaGraph.h1TowerMap 4 8 (by norm_num))
      = thetaGraph.h1TowerMap 2 8 (by norm_num) :=
  thetaGraph.h1TowerMap_comp 2 4 8 (by norm_num) (by norm_num)


/-- **The two prices identified on theta** (review #16): at `4 → 2`,
the Gibbs price equals the ratchet cost minus the deficit gained —
`H(4|2) = 2·log 2 − (Δ(4) − Δ(2))` — with the strict package:
`0 < H(4|2) < 2·log 2` and `Δ(2) < Δ(4)`. -/
theorem theta_tower_price :
    ((thetaGraph.residueDist 4).condEntropy
          (⇑(thetaGraph.h1TowerMap 2 4 (by norm_num)))
        = 2 * Real.log 2
          - (thetaGraph.residueDefect 4 - thetaGraph.residueDefect 2))
      ∧ 0 < (thetaGraph.residueDist 4).condEntropy
          (⇑(thetaGraph.h1TowerMap 2 4 (by norm_num)))
      ∧ (thetaGraph.residueDist 4).condEntropy
          (⇑(thetaGraph.h1TowerMap 2 4 (by norm_num)))
          < 2 * Real.log 2
      ∧ thetaGraph.residueDefect 2 < thetaGraph.residueDefect 4 := by
  have hb : 0 < thetaGraph.b1 := by
    rw [← thetaGraph.card_eq_b1 thetaLatticeBasis]
    norm_num
  have hb2 : ((thetaGraph.b1 : ℕ) : ℝ) = 2 := by
    rw [← thetaGraph.card_eq_b1 thetaLatticeBasis]
    norm_num
  have hid := thetaGraph.residue_tower_condEntropy_eq_defect 2 4 2
    (by norm_num) (by norm_num)
  have hstrict := thetaGraph.residue_tower_price_strict 2 4 2 hb
    (by norm_num) (by norm_num) (by norm_num)
  rw [hb2] at hid
  obtain ⟨h1, h2, h3⟩ := hstrict
  rw [hb2] at h2
  exact ⟨hid, h1, h2, h3⟩

noncomputable local instance :
    DecidableEq (IncidenceGraph.H1Reduction thetaGraph 4) :=
  thetaGraph.h1ReductionDecEq 4

/-- **The complete priced composition law on theta** (review #17):
along `8 → 4 → 2` the conditional entropies add
(`H(8|2) = H(8|4) + H(4|2)`), the section costs add, and the
telescoped two-step price identity holds —
`H(8|2) = 2·log 4 − (Δ(8) − Δ(2))`. -/
theorem theta_tower_price_triangle :
    ((thetaGraph.residueDist 8).condEntropy
          (⇑(thetaGraph.h1TowerMap 2 8 (by norm_num)))
        = (thetaGraph.residueDist 8).condEntropy
              (⇑(thetaGraph.h1TowerMap 4 8 (by norm_num)))
          + (thetaGraph.residueDist 4).condEntropy
              (⇑(thetaGraph.h1TowerMap 2 4 (by norm_num))))
      ∧ sectionCost (⇑(thetaGraph.h1TowerMap 2 8 (by norm_num)))
            / Nat.card (IncidenceGraph.H1Reduction thetaGraph 2)
          = sectionCost (⇑(thetaGraph.h1TowerMap 4 8 (by norm_num)))
                / Nat.card (IncidenceGraph.H1Reduction thetaGraph 4)
            + sectionCost (⇑(thetaGraph.h1TowerMap 2 4 (by norm_num)))
                / Nat.card (IncidenceGraph.H1Reduction thetaGraph 2)
      ∧ (thetaGraph.residueDist 8).condEntropy
            (⇑(thetaGraph.h1TowerMap 2 8 (by norm_num)))
          = 2 * Real.log 4
            - (thetaGraph.residueDefect 8 - thetaGraph.residueDefect 2) := by
  have hb2 : ((thetaGraph.b1 : ℕ) : ℝ) = 2 := by
    rw [← thetaGraph.card_eq_b1 thetaLatticeBasis]
    norm_num
  have hchain := thetaGraph.residue_tower_condEntropy_trans 2 4 8
    (by norm_num) (by norm_num)
  have hcost := thetaGraph.sectionCost_h1TowerMap_trans 2 4 8
    (by norm_num) (by norm_num)
  have hprice := thetaGraph.residue_tower_price_trans 2 4 8 2 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [hb2] at hprice
  refine ⟨hchain, hcost, ?_⟩
  rw [hprice]
  norm_num

/-! ### Fluctuation–dissipation on theta (review #16)

The theta graph's harmonic Gram is genuinely **non-diagonal** — its
two cycles share a path — so these are the first consumers of the
intrinsic derivative and strict-dissipation theorems beyond the
diagonal/scalar family. -/

/-- **The intrinsic derivative on a non-diagonal carrier**
(review #16): fluctuation–dissipation on the theta graph. -/
theorem theta_hasDerivAt_classMeanEnergy (β : ℝ) (hβ : 0 < β) :
    HasDerivAt thetaGraph.classMeanEnergy
      (-((thetaGraph.classSectorActionβ β hβ).gibbsVariance
          thetaGraph.harmonicEnergy)) β :=
  thetaGraph.hasDerivAt_classMeanEnergy_eq_neg_gibbsVariance β hβ

/-- **Strict dissipation on a non-diagonal carrier** (review #16):
the theta graph's Gibbs mean energy strictly decreases in the
inverse temperature. -/
theorem theta_classMeanEnergy_strictAntiOn :
    StrictAntiOn thetaGraph.classMeanEnergy (Set.Ioi 0) := by
  refine thetaGraph.classMeanEnergy_strictAntiOn ?_
  rw [← thetaGraph.card_eq_b1 thetaLatticeBasis]
  norm_num

/-- **Temperature–duality on a non-diagonal carrier** (review #17):
theta's harmonic `H¹` mean energy and its priced `H₁` cycle mean
energy at reciprocal temperatures —
`⟨E⟩_{H¹}(β) + β⁻²·⟨E⟩_{H₁}(β⁻¹) = 1/β`, with `b₁ = 2`. -/
theorem theta_classMeanEnergy_T_dual (β : ℝ) (hβ : 0 < β) :
    thetaGraph.classMeanEnergy β
        + β⁻¹ ^ 2 * (thetaGraph.cycleAction).meanEnergy β⁻¹
      = 1 / β := by
  have h := thetaGraph.classMeanEnergy_T_dual β hβ
  rw [show ((thetaGraph.b1 : ℕ) : ℝ) = 2 from by
      rw [← thetaGraph.card_eq_b1 thetaLatticeBasis]
      norm_num] at h
  rw [h, div_eq_div_iff (by positivity) hβ.ne']
  ring

/-- **The variance transformation law on theta** (review #18):
`Var_{H¹}(β) + 2β⁻³·⟨E⟩_{H₁}(β⁻¹) − β⁻⁴·Var_{H₁}(β⁻¹) = 1/β²`, with
`b₁ = 2` — fluctuation–dissipation and temperature–duality closed
into one circle on a genuinely non-diagonal carrier. -/
theorem theta_gibbsVariance_T_dual (β : ℝ) (hβ : 0 < β) :
    (thetaGraph.classSectorActionβ β hβ).gibbsVariance
        thetaGraph.harmonicEnergy
      + 2 * β⁻¹ ^ 3 * (thetaGraph.cycleAction).meanEnergy β⁻¹
      - β⁻¹ ^ 4 * (((thetaGraph.cycleAction).scaledSector β⁻¹
          (inv_pos.mpr hβ)).gibbsVariance
          (fun c => (thetaGraph.cycleAction).form c c))
      = 1 / β ^ 2 := by
  have h := thetaGraph.classGibbsVariance_T_dual β hβ
  rw [show ((thetaGraph.b1 : ℕ) : ℝ) = 2 from by
      rw [← thetaGraph.card_eq_b1 thetaLatticeBasis]
      norm_num] at h
  rw [h, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-! ## The systole at the theta graph (G1 strictness)

Every integral cycle pairing nontrivially with `thetaMatter` has
chain norm at least `4`: in the theta basis's coordinates `(a, b)`
the chain norm is `4(a² + ab + b²)` (the chain Gram is
`!![4, 2; 2, 4]`), and the integer form `a² + ab + b²` is at least
`1` off the origin. The systole bound therefore reads `1/4 ≤ mass`,
and the mass is `1/3` — **strict**: the harmonic representative of
the theta class is supported on no single cycle, and no integral
cycle attains the dual norm. -/

/-- Nonzero integer pairs give `1 ≤ a² + ab + b²` — integer
positivity of the theta chain form. -/
private lemma one_le_theta_intForm {a b : ℤ} (h : ¬(a = 0 ∧ b = 0)) :
    1 ≤ a ^ 2 + a * b + b ^ 2 := by
  rcases eq_or_ne b 0 with hb | hb
  · subst hb
    have ha : a ≠ 0 := fun ha => h ⟨ha, rfl⟩
    have h4 : 0 < a ^ 2 :=
      lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 ha))
    have h5 := Int.add_one_le_iff.mpr h4
    nlinarith
  · have hb2 : 1 ≤ b ^ 2 := by
      have h4 : 0 < b ^ 2 :=
        lt_of_le_of_ne (sq_nonneg b) (Ne.symm (pow_ne_zero 2 hb))
      have h5 := Int.add_one_le_iff.mpr h4
      linarith
    have key : 3 ≤ 4 * (a ^ 2 + a * b + b ^ 2) := by
      nlinarith [sq_nonneg (2 * a + b)]
    set f := a ^ 2 + a * b + b ^ 2
    omega

/-- **The theta systole**: every integral cycle pairing nontrivially
with the theta matter has chain norm at least `4` — the chain-Gram
form `4(a² + ab + b²)` at nonzero integer coordinates. -/
theorem theta_pairing_normSq_ge_four (c : ↥thetaGraph.cycleLattice)
    (h : thetaGraph.cyclePairing c thetaMatter.val ≠ 0) :
    (4 : ℝ) ≤ (fun e => ((c : thetaGraph.E → ℤ) e : ℝ))
      ⬝ᵥ (fun e => ((c : thetaGraph.E → ℤ) e : ℝ)) := by
  have hc : c ≠ 0 := by
    intro h0
    apply h
    rw [h0, map_zero]
    rfl
  have hab : ¬(thetaLatticeBasis.repr c 0 = 0
      ∧ thetaLatticeBasis.repr c 1 = 0) := by
    rintro ⟨ha0, hb0⟩
    apply hc
    have hrepr : thetaLatticeBasis.repr c = 0 := by
      ext j
      fin_cases j
      · simpa using ha0
      · simpa using hb0
    rw [← thetaLatticeBasis.repr.symm_apply_apply c, hrepr, map_zero]
  have hquad :=
    thetaGraph.castCycle_normSq_eq_repr_quadForm thetaLatticeBasis c
  rw [cyclesR_thetaLatticeBasis, gramOf_thetaCycles] at hquad
  rw [hquad]
  have hexpand : (fun i => ((thetaLatticeBasis.repr c i : ℤ) : ℝ))
      ⬝ᵥ ((!![4, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℝ)
          *ᵥ fun i => ((thetaLatticeBasis.repr c i : ℤ) : ℝ))
      = 4 * (((thetaLatticeBasis.repr c 0 : ℤ) : ℝ) ^ 2
          + ((thetaLatticeBasis.repr c 0 : ℤ) : ℝ)
            * ((thetaLatticeBasis.repr c 1 : ℤ) : ℝ)
          + ((thetaLatticeBasis.repr c 1 : ℤ) : ℝ) ^ 2) := by
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  rw [hexpand]
  have h1R : (1 : ℝ) ≤ ((thetaLatticeBasis.repr c 0 : ℤ) : ℝ) ^ 2
      + ((thetaLatticeBasis.repr c 0 : ℤ) : ℝ)
        * ((thetaLatticeBasis.repr c 1 : ℤ) : ℝ)
      + ((thetaLatticeBasis.repr c 1 : ℤ) : ℝ) ^ 2 := by
    exact_mod_cast one_le_theta_intForm hab
  linarith

/-- **THE STRICTNESS** (G1): the theta systole bound `1/4` is
strictly below the mass `1/3` — the systole inequality is strict on
the theta graph. -/
theorem theta_mass_gt_systole : (1 : ℝ) / 4 < thetaMatter.mass := by
  rw [thetaMatter_mass]
  norm_num

end Meno
