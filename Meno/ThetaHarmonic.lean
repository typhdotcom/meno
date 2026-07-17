import Meno.PeriodHarmonic
import Meno.Matter

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

/-! ## The subdivided theta graph `K₂,₃`

Vertices: `0 = u`, `1 = v` (junctions), `2, 3, 4` (path interiors).
Edges (all oriented junction-to-junction): `e₀ : u→a₁`, `e₁ : a₁→v`,
`e₂ : u→a₂`, `e₃ : a₂→v`, `e₄ : u→a₃`, `e₅ : a₃→v`. Cycle basis
`c₁ = p₁ − p₃`, `c₂ = p₂ − p₃`. -/

section Theta

/-- Edge sources in `K₂,₃`. -/
def thetaSrc : Fin 6 → Fin 5 := ![0, 2, 0, 3, 0, 4]

/-- Edge targets in `K₂,₃`. -/
def thetaTgt : Fin 6 → Fin 5 := ![2, 1, 3, 1, 4, 1]

/-- The boundary of a 1-cochain: net flow into each vertex. -/
noncomputable def thetaBoundary (ω : Fin 6 → ℝ) (w : Fin 5) : ℝ :=
  ∑ e, ((if thetaTgt e = w then (1 : ℝ) else 0)
    - (if thetaSrc e = w then (1 : ℝ) else 0)) * ω e

/-- The basis cycles: `c₁ = p₁ − p₃` and `c₂ = p₂ − p₃`. -/
noncomputable def thetaCycles : Fin 2 → Fin 6 → ℝ :=
  ![![1, 1, 0, 0, -1, -1], ![0, 0, 1, 1, -1, -1]]

/-- The basis vectors are cycles: their boundary vanishes at every
vertex. -/
theorem thetaBoundary_cycles (i : Fin 2) (w : Fin 5) :
    thetaBoundary (thetaCycles i) w = 0 := by
  fin_cases i <;> fin_cases w <;>
    simp +decide [thetaBoundary, thetaSrc, thetaTgt, thetaCycles,
      Fin.sum_univ_six]

/-- **The cycle space is exactly the span of the basis** (`b₁ = 2`):
a cochain with vanishing boundary is determined by its flows on the
first and second paths, as a combination of `c₁` and `c₂`. Flow
conservation at each interior vertex equalizes the two edges of each
path; conservation at the junction forces the third path's flow to be
minus the sum of the first two. -/
theorem eq_comb_of_thetaBoundary_eq_zero (ω : Fin 6 → ℝ)
    (h : ∀ w, thetaBoundary ω w = 0) :
    ω = fun e => ω 0 * thetaCycles 0 e + ω 2 * thetaCycles 1 e := by
  have h0 := h 0
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  simp +decide [thetaBoundary, thetaSrc, thetaTgt, Fin.sum_univ_six]
    at h0 h2 h3 h4
  funext e
  fin_cases e <;> simp +decide [thetaCycles] <;> linarith

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

/-- The theta graph as a cycle presentation: `K₂,₃` with its chosen
basis `c₁ = p₁ − p₃`, `c₂ = p₂ − p₃`. -/
noncomputable def thetaPresentation : CyclePresentation (Fin 5) (Fin 6) where
  src := thetaSrc
  tgt := thetaTgt
  r := 2
  cycles := thetaCycles
  cycles_closed := fun i w => thetaBoundary_cycles i w
  spanning := fun ω hω => by
    refine ⟨![ω 0, ω 2], ?_⟩
    have h := eq_comb_of_thetaBoundary_eq_zero ω (fun w => hω w)
    funext e
    rw [congrFun h e, Fin.sum_univ_two]
    rfl
  gram_posDef := by
    rw [gramOf_thetaCycles]
    exact thetaChainGram_posDef

/-- The theta graph has matter: the `(1, 0)` period class, anchored to
the presentation (Phase 22). Mass, the variational identity,
no-potential, and annihilation all come from the general
`MatterSector` API. -/
noncomputable def thetaMatter : MatterSector thetaPresentation :=
  ⟨![1, 0], by
    intro hc
    have h0 := congrFun hc 0
    norm_num at h0⟩

/-- The theta matter's mass is `1/3` — the same number the Gram data
assigns, reached through the presentation-level API. -/
theorem thetaMatter_mass : thetaMatter.mass = 1/3 := by
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
period coordinates. The description-cost (InfoRatchet) half of that
keystone remains a design problem, recorded in PLAN. -/

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

/-- The theta basis `c₁ = p₁ − p₃`, `c₂ = p₂ − p₃` is integrally
primitive: an integer cochain with zero boundary is an *integer*
combination of the basis. Completes the primitivity trio (cycle and
wedge in `Meno/CyclePresentation.lean`). -/
theorem theta_integral_spanning (ω : Fin 6 → ℤ)
    (h : ∀ w, thetaBoundary (fun e => (ω e : ℝ)) w = 0) :
    ∃ a : Fin 2 → ℤ, ∀ e, (ω e : ℝ) = ∑ i, (a i : ℝ) * thetaCycles i e := by
  refine ⟨![ω 0, ω 2], fun e => ?_⟩
  have hr := eq_comb_of_thetaBoundary_eq_zero (fun e => (ω e : ℝ)) h
  calc (ω e : ℝ)
      = (ω 0 : ℝ) * thetaCycles 0 e + (ω 2 : ℝ) * thetaCycles 1 e :=
        congrFun hr e
    _ = ∑ i, ((![ω 0, ω 2] : Fin 2 → ℤ) i : ℝ) * thetaCycles i e := by
        rw [Fin.sum_univ_two]
        rfl

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



end Meno
