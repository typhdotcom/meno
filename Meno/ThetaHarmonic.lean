import Meno.ThetaGraph
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

Following the Phase 17 review:

* **Sectors are cohomological.** The variational problem is posed on
  *periods*: minimize `‖ω‖²` over 1-cochains `ω` with prescribed
  integrals `⟨ω, cᵢ⟩ = kᵢ` against the basis cycles. The resulting
  Gram form is the inverse `C⁻¹` of the cycle-chain Gram matrix `C` —
  the norm on the dual (period / integral cohomology) lattice. For the
  cycle graph this reproduces `1/n`; here it produces
  `C = [[4,2],[2,4]]`, `Q = C⁻¹ = [[1/3,−1/6],[−1/6,1/3]]`.
* **Concrete first.** The general least-norm lemma
  (`isLeast_energy_periods`) is proved for an arbitrary finite edge
  type and arbitrary period vectors — it is the seed of the general
  finite-graph API — but the graph-level work is done concretely for
  `K₂,₃`, not through a universal graph-Hodge framework.

## The variational lemma

In `ℝ^E` with the standard dot product, given period vectors
`c₁, …, c_r` with invertible Gram matrix `C`, the minimum of `‖ω‖²`
over `{ω | ⟨ω, cᵢ⟩ = kᵢ}` is `kᵀC⁻¹k`, attained at the combination
`ω* = ∑ᵢ (C⁻¹k)ᵢ cᵢ`. Pythagoras: any feasible `ω` is `ω* + δ` with
`δ ⊥ span(cᵢ) ∋ ω*`. No boundary operators, no Hodge decomposition —
the period constraint *is* the cohomology. -/

namespace Meno

open scoped BigOperators
open Matrix

section Theta

/-- The period Gram form is positive definite (inverse of a
positive-definite matrix). -/
theorem thetaGram_posDef :
    (!![1/3, -(1/6); -(1/6), 1/3] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  rw [← thetaChainGram_inv]
  exact posDef_inv thetaChainGram_posDef

/-- **The harmonic Gram data of the theta graph** — the first
non-diagonal instance in the spine. The Gram form is derived from the
graph (`gramOf_thetaCycles` + `thetaChainGram_inv`), not asserted. -/
noncomputable def thetaHarmonicGramData : HarmonicGramData (Fin 5) where
  r := 2
  gram := !![1/3, -(1/6); -(1/6), 1/3]
  gram_symm := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  gram_posDef := thetaGram_posDef
  summable := summable_exp_neg_quadForm thetaGram_posDef

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
    have h := congrArg thetaIntegralPresentation.latticeQuotEquiv h0
    rw [map_zero] at h
    have h1 : (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ)
        ⬝ᵥ thetaIntegralPresentation.cyclesZ 0 = 0 := congrFun h 0
    rw [show (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ)
        ⬝ᵥ thetaIntegralPresentation.cyclesZ 0
        = (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ) ⬝ᵥ ![1, 1, 0, 0, -1, -1]
      from rfl] at h1
    exact absurd h1 (by decide)⟩

/-- The theta matter's intrinsic coordinates against the theta
presentation are `(1, 0)`. -/
theorem thetaMatter_coords :
    thetaIntegralPresentation.latticeQuotEquiv thetaMatter.val
      = ![1, 0] := by
  funext j
  show (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ)
    ⬝ᵥ thetaIntegralPresentation.cyclesZ j = ![1, 0] j
  fin_cases j
  · show (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ) ⬝ᵥ ![1, 1, 0, 0, -1, -1] = 1
    decide
  · show (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ) ⬝ᵥ ![0, 0, 1, 1, -1, -1] = 0
    decide

/-- The theta matter's mass is `1/3` — the intrinsic harmonic energy,
computed through the theta presentation's chart (C6). -/
theorem thetaMatter_mass : thetaMatter.mass = 1/3 := by
  rw [← thetaMatter.mass_chart thetaIntegralPresentation, thetaMatter_coords]
  show ∑ i, ∑ j, (gramOf thetaCycles)⁻¹ i j
      * ((![1, 0] : Fin 2 → ℤ) i : ℝ) * ((![1, 0] : Fin 2 → ℤ) j : ℝ) = 1/3
  rw [gramOf_thetaCycles, thetaChainGram_inv]
  norm_num [Fin.sum_univ_two]

/-- **The first non-diagonal consumer of the general Siegel–Poisson
duality**: the theta graph's quadratic action, with its topologically
derived coupled Gram form of determinant `1/12`, obeys
`Z(π²·Q⁻¹) = √((1/12)/π²)·Z(Q)`. Phases 15 and 17 meet. -/
theorem theta_siegelPoisson_duality :
    (↑(thetaHarmonicGramData.toQuadraticAction.dual.toSectorAction.partFn) : ℂ)
      = ↑((1/12 : ℝ) / Real.pi ^ 2) ^ ((1 : ℂ) / 2)
        * ↑(thetaHarmonicGramData.toQuadraticAction.toSectorAction.partFn) := by
  have h := (thetaHarmonicGramData.toQuadraticAction).duality
  have hdet : (thetaHarmonicGramData.toQuadraticAction).Q.det = 1/12 := by
    show (!![1/3, -(1/6); -(1/6), 1/3] : Matrix (Fin 2) (Fin 2) ℝ).det = 1/12
    rw [Matrix.det_fin_two]
    norm_num
  rw [hdet] at h
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

/-- The gradient (coboundary) of a vertex potential. -/
noncomputable def thetaGrad (f : Fin 5 → ℝ) : Fin 6 → ℝ :=
  fun e => f (thetaTgt e) - f (thetaSrc e)

/-- Gradients have vanishing periods: local re-description is invisible
to the sectors. -/
theorem thetaGrad_period (f : Fin 5 → ℝ) (i : Fin 2) :
    thetaGrad f ⬝ᵥ thetaCycles i = 0 := by
  fin_cases i <;>
    simp +decide [thetaGrad, dotProduct, thetaSrc, thetaTgt, thetaCycles,
      Fin.sum_univ_six]

/-- **Exactness at the theta graph**: a cochain has vanishing periods
iff it is a gradient. The forward direction constructs the potential
explicitly by integrating along the first path and using the two period
conditions to certify consistency across the others. -/
theorem thetaExactness (ω : Fin 6 → ℝ) :
    (∀ i, ω ⬝ᵥ thetaCycles i = 0) ↔ ∃ f : Fin 5 → ℝ, thetaGrad f = ω := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    simp +decide [dotProduct, thetaCycles, Fin.sum_univ_six] at h0 h1
    refine ⟨![0, ω 4 + ω 5, ω 0, ω 2, ω 4], ?_⟩
    funext e
    fin_cases e <;>
      simp +decide [thetaGrad, thetaSrc, thetaTgt] <;> linarith
  · rintro ⟨f, rfl⟩ i
    exact thetaGrad_period f i

/-- **Matter admits no potential**: the minimum-energy representative
of a nonzero sector is not a gradient. The constraint system it
encodes is locally consistent and globally unsatisfiable. -/
theorem matter_no_potential (k : Fin 2 → ℤ) (hk : k ≠ 0) :
    ¬ ∃ f : Fin 5 → ℝ,
      thetaGrad f = periodRep thetaCycles (fun i => (k i : ℝ)) := by
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
  thetaIntegralPresentation.card_quotient q

/-- At any resolution `q`, the theta graph's gauge group is `q⁴` — one
`q`-digit per non-cycle edge (`6 − 2` of them). K1's `q²` classes and
this `q⁴` of gauge multiply to `q⁶ = |descriptions|`. -/
theorem theta_gauge_count (q : ℕ) [NeZero q] :
    Nat.card (LinearMap.range (thetaGraph.gradLin (ZMod q))) = q ^ 4 := by
  have hexp : Fintype.card thetaGraph.E - thetaIntegralPresentation.r = 4 := by
    show Fintype.card (Fin 6) - 2 = 4
    simp
  rw [thetaIntegralPresentation.card_gauge q, hexp]

end Meno
