import Meno.GraphInstances
import Meno.Matter
import Meno.ResolutionCount

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

/-- **The variational identity at the theta graph**: the Gram-data
energy of the sector `k ∈ ℤ²` is the least energy among 1-cochains
with periods `k` against the basis cycles — attained. The Gram form
`[[1/3,−1/6],[−1/6,1/3]]` is *derived* from `K₂,₃`'s topology by
minimization, fulfilling the honesty note in `HarmonicForm`. -/
theorem thetaGramData_energy_isLeast (k : Fin 2 → ℤ) :
    IsLeast {E : ℝ | ∃ ω : Fin 6 → ℝ,
        (∀ j, ω ⬝ᵥ thetaCycles j = (k j : ℝ)) ∧ E = ω ⬝ᵥ ω}
      (thetaHarmonicGramData.energy k) := by
  have hdet : IsUnit (gramOf thetaCycles).det := by
    rw [gramOf_thetaCycles]
    exact isUnit_iff_ne_zero.mpr (ne_of_gt thetaChainGram_posDef.det_pos)
  have h := isLeast_energy_periods thetaCycles hdet (fun j => (k j : ℝ))
  have hval : thetaHarmonicGramData.energy k
      = (fun j => (k j : ℝ)) ⬝ᵥ
          ((gramOf thetaCycles)⁻¹.mulVec (fun j => (k j : ℝ))) := by
    show ∑ i, ∑ j, (!![1/3, -(1/6); -(1/6), 1/3] : Matrix (Fin 2) (Fin 2) ℝ) i j
        * (k i : ℝ) * (k j : ℝ) = _
    rw [quadForm_dotProduct, gramOf_thetaCycles, thetaChainGram_inv]
  rw [hval]
  exact h

/-- The canonical matter sector of the theta graph: winding `(1, 0)`
(once around the first-and-third-path cycle), with harmonic minimum
action `1/3`. -/
theorem thetaGramData_energy_one_zero :
    thetaHarmonicGramData.energy ![1, 0] = 1/3 := by
  show ∑ i, ∑ j, (!![1/3, -(1/6); -(1/6), 1/3] : Matrix (Fin 2) (Fin 2) ℝ) i j
      * ((![1, 0] : Fin 2 → ℤ) i : ℝ) * ((![1, 0] : Fin 2 → ℤ) j : ℝ) = 1/3
  norm_num [Fin.sum_univ_two]

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
`−1/6`. -/
theorem theta_interaction :
    thetaHarmonicGramData.interaction ![1, 0] ![0, 1] = -(1/6) := by
  show ∑ i, ∑ j, (!![1/3, -(1/6); -(1/6), 1/3] : Matrix (Fin 2) (Fin 2) ℝ) i j
      * ((![1, 0] : Fin 2 → ℤ) i : ℝ) * ((![0, 1] : Fin 2 → ℤ) j : ℝ) = -(1/6)
  norm_num [Fin.sum_univ_two]

/-- **Theta sectors bind with energy `1/3`** — positive: the sectors
attract. Confirms the exact shared-cycle formula `2k/(n₁n₂ − k²)` at
`(4, 4, 2)`. -/
theorem theta_bindingEnergy :
    thetaHarmonicGramData.bindingEnergy ![1, 0] ![0, 1] = 1/3 := by
  rw [HarmonicGramData.bindingEnergy_eq, theta_interaction]
  norm_num

/-- Attraction, stated as an inequality: the joint sector is strictly
cheaper than its parts. -/
theorem theta_binding_attractive :
    thetaHarmonicGramData.energy (![1, 0] + ![0, 1])
      < thetaHarmonicGramData.energy ![1, 0]
        + thetaHarmonicGramData.energy ![0, 1] := by
  have h := theta_bindingEnergy
  unfold HarmonicGramData.bindingEnergy at h
  linarith

/-- Inverse of the parametric shared-cycle chain Gram. -/
theorem sharedCycles_chainGram_inv (n₁ n₂ k : ℝ) (hD : n₁ * n₂ - k ^ 2 ≠ 0) :
    (!![n₁, k; k, n₂] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
      = (n₁ * n₂ - k ^ 2)⁻¹ • !![n₂, -k; -k, n₁] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring

/-- **The exact binding oracle**: two cycles of lengths `n₁, n₂`
sharing `k` co-oriented edges bind (at unit sectors) with energy
`2k/(n₁n₂ − k²)` — minus twice the period-Gram off-diagonal. The
time-capsule's `2k/(n₁n₂)` is this to leading order in `k²/(n₁n₂)`.
Theta: `2·2/(4·4 − 2²) = 1/3 = theta_bindingEnergy`. -/
theorem sharedCycles_binding (n₁ n₂ k : ℝ) (hD : 0 < n₁ * n₂ - k ^ 2) :
    -2 * ((!![n₁, k; k, n₂] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ 0 1)
      = 2 * k / (n₁ * n₂ - k ^ 2) := by
  rw [sharedCycles_chainGram_inv n₁ n₂ k (ne_of_gt hD)]
  simp [Matrix.smul_apply]
  field_simp

end Binding

/-! ## Exactness: matter as trapped inconsistency

The time capsule's third idea, formalized at theta. A 1-cochain is a
system of local constraints ("the potential difference across `e` is
`ω e`"). A **global potential** solves them all; going around a cycle
shows a solution can exist only if the periods vanish. The converse
holds too: `thetaExactness` — zero periods ⟺ a potential exists. So a
nonzero sector is a constraint system that is locally consistent
everywhere and globally unsatisfiable — and its minimum-energy
representative (`periodRep`) carries positive energy precisely because
no potential can flatten it. Matter is trapped paradox.

This pair (period map surjective — `periodRep_periods`; kernel exactly
the gradients — `thetaExactness`) is the rank-2 case of the capsule's
keystone: the incompressible residue of local re-description is `b₁`
period coordinates. The description-cost half was completed in C8
(`log_card_sections`, `theta_residue_count`, `theta_gauge_count`):
the keystone is a coding theorem now, not a design problem. -/

section Gauge

/-- Gradients — the substrate's `IncidenceGraph.grad`, not a
specialized copy (review #3, finding 4) — have vanishing periods:
local re-description is invisible to the sectors. -/
theorem thetaGrad_period (f : Fin 5 → ℝ) (i : Fin 2) :
    thetaGraph.grad f ⬝ᵥ thetaCycles i = 0 := by
  fin_cases i <;>
    simp +decide [IncidenceGraph.grad, dotProduct, thetaSrc, thetaTgt,
      thetaCycles, Fin.sum_univ_six]

/-- **Exactness at the theta graph**: a cochain has vanishing periods
iff it is a gradient. The forward direction constructs the potential
explicitly by integrating along the first path and using the two period
conditions to certify consistency across the others. -/
theorem thetaExactness (ω : Fin 6 → ℝ) :
    (∀ i, ω ⬝ᵥ thetaCycles i = 0) ↔ ∃ f : Fin 5 → ℝ, thetaGraph.grad f = ω := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    simp +decide [dotProduct, thetaCycles, Fin.sum_univ_six] at h0 h1
    refine ⟨![0, ω 4 + ω 5, ω 0, ω 2, ω 4], ?_⟩
    funext e
    fin_cases e <;>
      simp +decide [IncidenceGraph.grad, thetaSrc, thetaTgt] <;> linarith
  · rintro ⟨f, rfl⟩ i
    exact thetaGrad_period f i

/-- **Matter admits no potential**: the minimum-energy representative
of a nonzero sector is not a gradient. The constraint system it
encodes is locally consistent and globally unsatisfiable. -/
theorem matter_no_potential (k : Fin 2 → ℤ) (hk : k ≠ 0) :
    ¬ ∃ f : Fin 5 → ℝ,
      thetaGraph.grad f = periodRep thetaCycles (fun i => (k i : ℝ)) := by
  intro hpot
  have hdet : IsUnit (gramOf thetaCycles).det := by
    rw [gramOf_thetaCycles]
    exact isUnit_iff_ne_zero.mpr (ne_of_gt thetaChainGram_posDef.det_pos)
  have hzero := (thetaExactness _).mpr hpot
  apply hk
  funext i
  have hper := periodRep_periods thetaCycles hdet (fun i => (k i : ℝ)) i
  rw [hzero i] at hper
  exact_mod_cast hper.symm

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

end Meno
