import Meno.Groupoid
import Meno.Fluctuation
import Meno.PeriodHarmonic
import Mathlib.Analysis.Real.Pi.Bounds

/-! # The Scalar Quadratic Family, Identified with the Spine

The legacy scalar partition function `quadraticPartFn` **is** the
spine's `scalarPartFn` (`quadraticPartFn_eq_scalarPartFn`, `rfl`), and
every groupoid object with quadratic winding energy reads as it
(`partFn_eq_quadraticPartFn`). What this file keeps is the consumed
scalar theory: the canonical one-object quadratic family
(`quadraticObj`), its Gibbs wrappers, the scalar mean energy with its
fluctuation–dissipation and T-duality functional equations — derived
from the spine's bundle engine, not differentiated locally — and the
Cauchy–Schwarz corroboration `M2_sq_lt_Z_mul_M4`. (Reviews #25–#28:
the `GroupoidObj.dual` construction, the product law, the rank-bound
and decomposition chains, and the local differentiation cluster were
consumerless mirrors of spine theorems and are deleted.) -/

namespace Simplicial

open UpperHalfPlane CategoryTheory

/-! ## Generalized quadratic partition function -/

noncomputable def quadraticPartFn (α : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp (-α * (k : ℝ) ^ 2)


/-! ## Generalized T-duality, inherited from the spine

The modular S-transformation proof lives in **one** place:
`Meno.QuadraticAction.scalarPartFn_duality`. `quadraticPartFn` is
definitionally the spine's scalar partition function, so the duality
here is a name-transport, not an independent analytic theorem. -/

/-- `quadraticPartFn` *is* the spine's scalar partition function. One
analytic object, two historical names. -/
theorem quadraticPartFn_eq_scalarPartFn (α : ℝ) :
    quadraticPartFn α = Meno.QuadraticAction.scalarPartFn α := rfl


/-! ## The winding bridge -/

/-- Partition function of any `GroupoidObj` with quadratic energy `α·(wind g)²` over a
    `ℤ`-valued winding equivalence equals the canonical `quadraticPartFn α`. This is the
    generic bridge between the abstract groupoid invariant and the analytic series. -/
theorem partFn_eq_quadraticPartFn
    (E : GroupoidObj) (wind : End E.base ≃ ℤ) (α : ℝ)
    (hK : ∀ g, E.energy g = α * (wind g : ℝ) ^ 2) :
    E.partFn = quadraticPartFn α := by
  unfold GroupoidObj.partFn groupoidPartitionFn quadraticPartFn
  conv_lhs =>
    rw [show (fun g => Real.exp (-E.energy g)) =
        (fun k : ℤ => Real.exp (-α * (k : ℝ) ^ 2)) ∘ wind from by
      ext g; simp only [Function.comp_apply]; rw [hK g]; ring_nf]
  exact Equiv.tsum_eq wind (fun k : ℤ => Real.exp (-α * (k : ℝ) ^ 2))


/-! ## Canonical quadratic family

For each coupling `α > 0`, `quadraticObj α hα` is the canonical `GroupoidObj` whose
underlying groupoid is `SingleObj (Multiplicative ℤ)` — one object with endomorphism
group ℤ — equipped with energy `α · k²` where `k` is the winding. Its partition
function is exactly `quadraticPartFn α`. This is the ℤ-modal family on which
the scalar functional equations act. -/

/-- Canonical winding equivalence on the one-object groupoid `SingleObj (Multiplicative ℤ)`:
    endomorphisms of the unique object correspond to integers. -/
noncomputable def quadraticWind :
    End (CategoryTheory.SingleObj.star (Multiplicative ℤ)) ≃ ℤ :=
  (CategoryTheory.SingleObj.toEnd (Multiplicative ℤ)).symm.toEquiv.trans Multiplicative.toAdd

/-- Canonical quadratic groupoid object at coupling `α`: the one-object groupoid whose
    endomorphism group is ℤ, with energy `α · (winding)²`. -/
noncomputable def quadraticObj (α : ℝ) (hα : 0 < α) : GroupoidObj where
  G := CategoryTheory.SingleObj (Multiplicative ℤ)
  base := CategoryTheory.SingleObj.star (Multiplicative ℤ)
  energy g := α * (quadraticWind g : ℝ) ^ 2
  summable := by
    have h := Meno.QuadraticAction.summable_scalarPartFn α hα
    exact (quadraticWind.summable_iff.mpr h).congr fun g => by
      simp only [Function.comp_apply, neg_mul]

/-- Energy of `quadraticObj α` is `α · (winding)²` — definitionally. -/
theorem quadraticObj_energy (α : ℝ) (hα : 0 < α)
    (g : End (quadraticObj α hα).base) :
    (quadraticObj α hα).energy g = α * (quadraticWind g : ℝ) ^ 2 :=
  rfl

/-- Partition function of `quadraticObj α` is `quadraticPartFn α`. -/
theorem quadraticObj_partFn (α : ℝ) (hα : 0 < α) :
    (quadraticObj α hα).partFn = quadraticPartFn α :=
  partFn_eq_quadraticPartFn (quadraticObj α hα) quadraticWind α (quadraticObj_energy α hα)


/-! ## Gibbs Measure on GroupoidObj

For a groupoid object `E`, the Gibbs density on automorphisms is
`gibbsMass E g = exp(-E.energy g) / E.partFn`.  It is nonnegative, summable,
and sums to `1` — a probability density on `End E.base`.  The Gibbs expectation
of an observable `f : End E.base → ℝ` is `gibbsExpect E f = ∑' g, f g * gibbsMass E g`;
the Gibbs variance is `⟨f²⟩ − ⟨f⟩²`.  All three depend only on the groupoid-level
data `(E.base, E.energy, E.summable)` plus the strict positivity `E.partFn > 0`. -/

/-- Gibbs probability density on automorphisms: `exp(-E.energy g) / E.partFn`. -/
noncomputable def GroupoidObj.gibbsMass (E : GroupoidObj) (g : End E.base) : ℝ :=
  Real.exp (-E.energy g) / E.partFn

/-- Gibbs expectation of `f : End E.base → ℝ` against the Gibbs density. -/
noncomputable def GroupoidObj.gibbsExpect (E : GroupoidObj) (f : End E.base → ℝ) : ℝ :=
  ∑' g, f g * E.gibbsMass g

/-- Gibbs variance of `f` under the Gibbs density: `⟨f²⟩ − ⟨f⟩²`. -/
noncomputable def GroupoidObj.gibbsVariance (E : GroupoidObj) (f : End E.base → ℝ) : ℝ :=
  E.gibbsExpect (fun g => f g ^ 2) - (E.gibbsExpect f) ^ 2

/-- **Audit identification (C12)**: the groupoid Gibbs machinery *is*
the sector action's, through the loop-kernel bridge — definitionally.
Retained as groupoid-facing wrappers; the analytic source of truth is
`SectorAction`. -/
theorem GroupoidObj.gibbsMass_eq_sector (E : GroupoidObj)
    (h_id : E.energy (𝟙 E.base) = 0) (h_nonneg : ∀ g, 0 ≤ E.energy g)
    (g : End E.base) :
    E.gibbsMass g
      = (E.toLoopKernelObj h_id h_nonneg).toSectorAction.gibbsMass g := rfl


/-- Partition function positivity packaged at the `GroupoidObj` level. -/
theorem GroupoidObj.partFn_pos (E : GroupoidObj) : 0 < E.partFn :=
  groupoidPartitionFn_pos (x := E.base) (K := E.energy) (hsum := E.summable)

/-- The Gibbs density is nonnegative. -/
theorem GroupoidObj.gibbsMass_nonneg (E : GroupoidObj) (g : End E.base) :
    0 ≤ E.gibbsMass g :=
  div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt E.partFn_pos)

/-- The Gibbs density is summable (division of `E.summable` by a constant). -/
theorem GroupoidObj.summable_gibbsMass (E : GroupoidObj) :
    Summable E.gibbsMass := by
  unfold GroupoidObj.gibbsMass
  exact E.summable.div_const _


/-! ## The vacuum bound -/

theorem quadraticPartFn_gt_one (α : ℝ) (hα : 0 < α) : quadraticPartFn α > 1 := by
  rw [quadraticPartFn_eq_scalarPartFn]
  exact Meno.QuadraticAction.scalarPartFn_gt_one α hα


/-! ### The scalar family as the rank-one chart (review #15)

The scalar quadratic family `β ↦ ∑' k : ℤ, exp(−β·k²)` is the
rank-one instance of the rank-generic inverse-temperature engine
(`Meno/Fluctuation.lean`): the unit quadratic action `k ↦ k²` scales
to it, and the differentiation lemmas below are the general
`Z′ = −M₁`, `M₁′ = −M₂` read through the chart `(Fin 1 → ℤ) ≃ ℤ` —
the analytic engine exists once, at every rank. -/

/-- The rank-one unit quadratic action `k ↦ k²`. -/
noncomputable def unitQuadAction : Meno.QuadraticAction 1 where
  Q := !![1]
  Q_posDef := Meno.posDef_fin_one 1 one_pos

private def zEquiv : (Fin 1 → ℤ) ≃ ℤ := Equiv.funUnique (Fin 1) ℤ

private lemma unitQuadAction_energy (k : Fin 1 → ℤ) :
    unitQuadAction.energy k = ((k 0 : ℝ)) ^ 2 := by
  show ∑ i, ∑ j, (!![(1 : ℝ)]) i j * (k i : ℝ) * (k j : ℝ) = _
  have h : (!![(1 : ℝ)]) 0 0 = 1 := rfl
  rw [Fin.sum_univ_one, Fin.sum_univ_one, h]
  ring

private lemma scaledPartFn_unit (β : ℝ) :
    unitQuadAction.scaledPartFn β = quadraticPartFn β := by
  refine (Equiv.tsum_eq zEquiv.symm
    (fun k : Fin 1 → ℤ =>
      Real.exp (-(β * unitQuadAction.energy k)))).symm.trans ?_
  refine tsum_congr fun n => ?_
  rw [unitQuadAction_energy]
  show Real.exp (-(β * (n : ℝ) ^ 2)) = Real.exp (-β * (n : ℝ) ^ 2)
  rw [show -(β * (n : ℝ) ^ 2) = -β * (n : ℝ) ^ 2 from by ring]

private lemma scaledMoment_unit (β : ℝ) :
    unitQuadAction.scaledMoment β
      = ∑' k : ℤ, (k : ℝ) ^ 2 * Real.exp (-β * (k : ℝ) ^ 2) := by
  refine (Equiv.tsum_eq zEquiv.symm
    (fun k : Fin 1 → ℤ => unitQuadAction.energy k
      * Real.exp (-(β * unitQuadAction.energy k)))).symm.trans ?_
  refine tsum_congr fun n => ?_
  rw [unitQuadAction_energy]
  show (n : ℝ) ^ 2 * Real.exp (-(β * (n : ℝ) ^ 2)) = _
  rw [show -(β * (n : ℝ) ^ 2) = -β * (n : ℝ) ^ 2 from by ring]

private lemma scaledMoment2_unit (β : ℝ) :
    unitQuadAction.scaledMoment2 β
      = ∑' k : ℤ, (k : ℝ) ^ 4 * Real.exp (-β * (k : ℝ) ^ 2) := by
  refine (Equiv.tsum_eq zEquiv.symm
    (fun k : Fin 1 → ℤ => unitQuadAction.energy k ^ 2
      * Real.exp (-(β * unitQuadAction.energy k)))).symm.trans ?_
  refine tsum_congr fun n => ?_
  rw [unitQuadAction_energy]
  show ((n : ℝ) ^ 2) ^ 2 * Real.exp (-(β * (n : ℝ) ^ 2)) = _
  rw [show -(β * (n : ℝ) ^ 2) = -β * (n : ℝ) ^ 2 from by ring,
    show ((n : ℝ) ^ 2) ^ 2 = (n : ℝ) ^ 4 from by ring]

private lemma summable_sq_mul_exp (β : ℝ) (hβ : 0 < β) :
    Summable (fun k : ℤ => (k : ℝ) ^ 2 * Real.exp (-β * (k : ℝ) ^ 2)) := by
  have h := (Equiv.summable_iff zEquiv.symm).mpr
    (unitQuadAction.summable_energy_mul_scaledWeight hβ)
  refine h.congr fun n => ?_
  show unitQuadAction.energy (zEquiv.symm n)
      * Real.exp (-(β * unitQuadAction.energy (zEquiv.symm n))) = _
  rw [unitQuadAction_energy]
  show (n : ℝ) ^ 2 * Real.exp (-(β * (n : ℝ) ^ 2)) = _
  rw [show -(β * (n : ℝ) ^ 2) = -β * (n : ℝ) ^ 2 from by ring]

private lemma summable_pow4_mul_exp (β : ℝ) (hβ : 0 < β) :
    Summable (fun k : ℤ => (k : ℝ) ^ 4 * Real.exp (-β * (k : ℝ) ^ 2)) := by
  have h := (Equiv.summable_iff zEquiv.symm).mpr
    (unitQuadAction.summable_energy_sq_mul_scaledWeight hβ)
  refine h.congr fun n => ?_
  show unitQuadAction.energy (zEquiv.symm n) ^ 2
      * Real.exp (-(β * unitQuadAction.energy (zEquiv.symm n))) = _
  rw [unitQuadAction_energy]
  show ((n : ℝ) ^ 2) ^ 2 * Real.exp (-(β * (n : ℝ) ^ 2)) = _
  rw [show -(β * (n : ℝ) ^ 2) = -β * (n : ℝ) ^ 2 from by ring,
    show ((n : ℝ) ^ 2) ^ 2 = (n : ℝ) ^ 4 from by ring]


/-! ## Gibbs second moment at the self-dual coupling

The Gibbs expectation `⟨k²⟩_α := (∑ k²·e^{-αk²})/Z(α)` of winding-squared at
coupling α.  At the self-dual coupling α = π this equals exactly `1/(4π)` —
the T-duality relation pins the second moment at its fixed point. -/

/-- Gibbs expectation of `k²` in the quadratic partition function at coupling α:
    `⟨k²⟩_α := (∑ k² · e^{-α k²}) / Z(α)`. -/
noncomputable def quadraticMeanEnergy (α : ℝ) : ℝ :=
  (∑' k : ℤ, (k : ℝ) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2)) / quadraticPartFn α

/-- **Bridge to the Gibbs density.** `quadraticMeanEnergy α` is the Gibbs
    expectation of the squared canonical winding on the canonical quadratic
    `GroupoidObj` at coupling `α`.  So the analytic mean energy *is* the second
    moment of a probability density on `End (quadraticObj α hα).base`. -/
theorem quadraticMeanEnergy_eq_gibbsExpect (α : ℝ) (hα : 0 < α) :
    (quadraticObj α hα).gibbsExpect (fun g => (quadraticWind g : ℝ) ^ 2) =
      quadraticMeanEnergy α := by
  unfold GroupoidObj.gibbsExpect GroupoidObj.gibbsMass quadraticMeanEnergy
  rw [quadraticObj_partFn α hα]
  have h_term : ∀ g : End (quadraticObj α hα).base,
      (quadraticWind g : ℝ) ^ 2 *
        (Real.exp (-(quadraticObj α hα).energy g) / quadraticPartFn α) =
      ((quadraticWind g : ℝ) ^ 2 * Real.exp (-α * (quadraticWind g : ℝ) ^ 2)) /
        quadraticPartFn α := by
    intro g
    show (quadraticWind g : ℝ) ^ 2 *
      (Real.exp (-(α * (quadraticWind g : ℝ) ^ 2)) / quadraticPartFn α) = _
    rw [mul_div_assoc, neg_mul]
  rw [tsum_congr h_term, tsum_div_const]
  congr 1


/-- **The Cauchy–Schwarz corroboration** (review #16): `M₂² < Z·M₄`
    for all `α > 0` — an independent, self-contained route to the
    strict positivity of the squared-winding variance, retained as
    named corroboration of the generic strict-fluctuation engine
    (`Meno/Fluctuation.lean`).

    Consider the "affine variance" summand `(Z·k² - M₂)²·exp(-αk²)`.
    Its tsum equals `Z²·M₄ - Z·M₂² = Z·(Z·M₄ - M₂²)`.
    Each term is non-negative, and the `k=0` term is `M₂² > 0`, so the
    tsum is strictly positive, forcing `Z·M₄ > M₂²`. This is the Gibbs
    Cauchy–Schwarz for the observable `k²`: the squared mean is strictly
    less than the mean of the square, because `k²` is not constant. -/
theorem M2_sq_lt_Z_mul_M4 (α : ℝ) (hα : 0 < α) :
    (∑' k : ℤ, (k : ℝ) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2)) ^ 2 <
      quadraticPartFn α *
        ∑' k : ℤ, (k : ℝ) ^ 4 * Real.exp (-α * (k : ℝ) ^ 2) := by
  set M2 := ∑' k : ℤ, (k : ℝ) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2) with hM2_def
  set M4 := ∑' k : ℤ, (k : ℝ) ^ 4 * Real.exp (-α * (k : ℝ) ^ 2) with hM4_def
  set Z := quadraticPartFn α with hZ_def
  have hZ_pos : 0 < Z := lt_trans one_pos (quadraticPartFn_gt_one α hα)
  have hM2_pos : 0 < M2 := by
    refine Summable.tsum_pos (summable_sq_mul_exp α hα) ?_ 1 ?_
    · intro k; exact mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _))
    · show (0 : ℝ) < ((1 : ℤ) : ℝ) ^ 2 * Real.exp (-α * ((1 : ℤ) : ℝ) ^ 2)
      rw [Int.cast_one, one_pow, one_mul]
      exact Real.exp_pos _
  have h_expand : ∀ k : ℤ, (Z * (k : ℝ) ^ 2 - M2) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2) =
      Z ^ 2 * ((k : ℝ) ^ 4 * Real.exp (-α * (k : ℝ) ^ 2)) +
        (-(2 * Z * M2)) * ((k : ℝ) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2)) +
        M2 ^ 2 * Real.exp (-α * (k : ℝ) ^ 2) := by
    intro k; ring
  have s1 : Summable (fun k : ℤ => Z ^ 2 * ((k : ℝ) ^ 4 * Real.exp (-α * (k : ℝ) ^ 2))) :=
    (summable_pow4_mul_exp α hα).mul_left _
  have s2 : Summable (fun k : ℤ =>
      (-(2 * Z * M2)) * ((k : ℝ) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2))) :=
    (summable_sq_mul_exp α hα).mul_left _
  have s3 : Summable (fun k : ℤ => M2 ^ 2 * Real.exp (-α * (k : ℝ) ^ 2)) :=
    (Meno.QuadraticAction.summable_scalarPartFn α hα).mul_left _
  have h_summable : Summable (fun k : ℤ =>
      (Z * (k : ℝ) ^ 2 - M2) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2)) :=
    ((s1.add s2).add s3).congr (fun k => (h_expand k).symm)
  have h_tsum_eq : ∑' k : ℤ, (Z * (k : ℝ) ^ 2 - M2) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2) =
      Z ^ 2 * M4 - Z * M2 ^ 2 := by
    rw [tsum_congr h_expand,
        (s1.add s2).tsum_add s3, s1.tsum_add s2,
        tsum_mul_left, tsum_mul_left, tsum_mul_left]
    show Z ^ 2 * M4 + -(2 * Z * M2) * M2 + M2 ^ 2 * Z = Z ^ 2 * M4 - Z * M2 ^ 2
    ring
  have h_tsum_pos : 0 < ∑' k : ℤ, (Z * (k : ℝ) ^ 2 - M2) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2) := by
    refine Summable.tsum_pos h_summable ?_ 0 ?_
    · intro k; exact mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _))
    · show (0 : ℝ) < (Z * ((0 : ℤ) : ℝ) ^ 2 - M2) ^ 2 * Real.exp (-α * ((0 : ℤ) : ℝ) ^ 2)
      rw [Int.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_sub,
          neg_sq, mul_zero, Real.exp_zero, mul_one]
      exact pow_pos hM2_pos 2
  rw [h_tsum_eq] at h_tsum_pos
  have hfact : Z ^ 2 * M4 - Z * M2 ^ 2 = Z * (Z * M4 - M2 ^ 2) := by ring
  rw [hfact] at h_tsum_pos
  have hposZM : 0 < Z * M4 - M2 ^ 2 := (mul_pos_iff_of_pos_left hZ_pos).mp h_tsum_pos
  linarith

private lemma unit_energy_one_ne :
    unitQuadAction.energy (fun _ => (1 : ℤ)) ≠ 0 := by
  rw [unitQuadAction_energy]
  norm_num

private lemma meanEnergy_unit :
    unitQuadAction.meanEnergy = quadraticMeanEnergy := by
  funext β
  show unitQuadAction.scaledMoment β / unitQuadAction.scaledPartFn β = _
  rw [scaledMoment_unit β, scaledPartFn_unit β]
  rfl

/-- `quadraticMeanEnergy` is strictly decreasing on `(0, ∞)` — the
    generic strict-dissipation theorem (`Meno/Fluctuation.lean`) at
    the rank-one unit action (review #16). The Cauchy–Schwarz route
    stands as named corroboration (`M2_sq_lt_Z_mul_M4`). -/
theorem quadraticMeanEnergy_strictAntiOn :
    StrictAntiOn quadraticMeanEnergy (Set.Ioi 0) := by
  rw [← meanEnergy_unit]
  exact unitQuadAction.meanEnergy_strictAntiOn ⟨fun _ => 1, unit_energy_one_ne⟩


private lemma quadraticObj_gibbsVariance_expr (α : ℝ) (hα : 0 < α) :
    (quadraticObj α hα).gibbsVariance
        (fun g => (quadraticWind g : ℝ) ^ 2) =
      (∑' k : ℤ, (k : ℝ) ^ 4 * Real.exp (-α * (k : ℝ) ^ 2)) / quadraticPartFn α -
        (quadraticMeanEnergy α) ^ 2 := by
  unfold GroupoidObj.gibbsVariance
  rw [quadraticMeanEnergy_eq_gibbsExpect α hα]
  have h_pow4 : (quadraticObj α hα).gibbsExpect
        (fun g => ((quadraticWind g : ℝ) ^ 2) ^ 2) =
      (∑' k : ℤ, (k : ℝ) ^ 4 * Real.exp (-α * (k : ℝ) ^ 2)) / quadraticPartFn α := by
    unfold GroupoidObj.gibbsExpect GroupoidObj.gibbsMass
    rw [quadraticObj_partFn α hα]
    have h_term : ∀ g : End (quadraticObj α hα).base,
        ((quadraticWind g : ℝ) ^ 2) ^ 2 *
          (Real.exp (-(quadraticObj α hα).energy g) / quadraticPartFn α) =
        ((quadraticWind g : ℝ) ^ 4 * Real.exp (-α * (quadraticWind g : ℝ) ^ 2)) /
          quadraticPartFn α := by
      intro g
      show ((quadraticWind g : ℝ) ^ 2) ^ 2 *
        (Real.exp (-(α * (quadraticWind g : ℝ) ^ 2)) / quadraticPartFn α) = _
      rw [mul_div_assoc, neg_mul]
      congr 1
      ring
    rw [tsum_congr h_term, tsum_div_const]
    congr 1
  rw [h_pow4]

private lemma quadraticObj_gibbsVariance_eq_unit (α : ℝ) (hα : 0 < α) :
    (quadraticObj α hα).gibbsVariance (fun g => (quadraticWind g : ℝ) ^ 2)
      = (unitQuadAction.scaledSector α hα).gibbsVariance
          unitQuadAction.energy := by
  rw [quadraticObj_gibbsVariance_expr α hα,
    unitQuadAction.scaledSector_gibbsVariance_energy α hα,
    scaledMoment2_unit α, scaledPartFn_unit α,
    show unitQuadAction.meanEnergy α = quadraticMeanEnergy α from
      congrFun meanEnergy_unit α]

/-- **Fluctuation-dissipation identity** at the `GroupoidObj` level:
    `d⟨k²⟩/dα = -gibbsVariance((wind)²)` on the canonical quadratic family.

    The derivative of the Gibbs mean of squared winding under coupling `α` is
    the negative Gibbs variance of squared winding, a probabilistic identity
    about the Gibbs density on `End (quadraticObj α).base`.  Strict positivity
    of the variance (Cauchy–Schwarz: `(wind)²` is not constant) is the reason
    `quadraticMeanEnergy` is strictly decreasing. -/
theorem hasDerivAt_quadraticMeanEnergy_eq_neg_gibbsVariance
    (α : ℝ) (hα : 0 < α) :
    HasDerivAt quadraticMeanEnergy
      (-((quadraticObj α hα).gibbsVariance
            (fun g => (quadraticWind g : ℝ) ^ 2))) α := by
  rw [← meanEnergy_unit, quadraticObj_gibbsVariance_eq_unit α hα]
  exact unitQuadAction.hasDerivAt_meanEnergy_eq_neg_gibbsVariance α hα

/-- The Gibbs variance of squared winding is strictly positive on
    `(0, ∞)` — the generic strict-fluctuation theorem at the unit
    action (review #16); Cauchy–Schwarz (`M2_sq_lt_Z_mul_M4`) stands
    as named corroboration. -/
theorem quadraticObj_gibbsVariance_pos (α : ℝ) (hα : 0 < α) :
    0 < (quadraticObj α hα).gibbsVariance (fun g => (quadraticWind g : ℝ) ^ 2) := by
  rw [quadraticObj_gibbsVariance_eq_unit α hα]
  exact unitQuadAction.scaledSector_gibbsVariance_energy_pos α hα
    (k₀ := fun _ => 1) unit_energy_one_ne


private lemma unitDual_energy (k : Fin 1 → ℤ) :
    unitQuadAction.dual.energy k = Real.pi ^ 2 * ((k 0 : ℝ)) ^ 2 := by
  have hinv : (!![(1 : ℝ)])⁻¹ = !![(1 : ℝ)] :=
    Matrix.inv_eq_right_inv (by
      ext i j
      fin_cases i
      fin_cases j
      simp [Matrix.mul_apply])
  have h : unitQuadAction.dual.Q 0 0 = Real.pi ^ 2 := by
    rw [show unitQuadAction.dual.Q = Real.pi ^ 2 • (!![(1 : ℝ)])⁻¹ from
        Meno.QuadraticAction.dual_Q unitQuadAction,
      hinv, Matrix.smul_apply, show (!![(1 : ℝ)]) 0 0 = 1 from rfl,
      smul_eq_mul, mul_one]
  show ∑ i, ∑ j, unitQuadAction.dual.Q i j * (k i : ℝ) * (k j : ℝ) = _
  rw [Fin.sum_univ_one, Fin.sum_univ_one, h]
  ring

private lemma unitDual_scaledPartFn (γ : ℝ) :
    unitQuadAction.dual.scaledPartFn γ
      = quadraticPartFn (Real.pi ^ 2 * γ) := by
  refine (Equiv.tsum_eq zEquiv.symm
    (fun k : Fin 1 → ℤ =>
      Real.exp (-(γ * unitQuadAction.dual.energy k)))).symm.trans ?_
  refine tsum_congr fun n => ?_
  rw [unitDual_energy]
  show Real.exp (-(γ * (Real.pi ^ 2 * (n : ℝ) ^ 2)))
    = Real.exp (-(Real.pi ^ 2 * γ) * (n : ℝ) ^ 2)
  rw [show -(γ * (Real.pi ^ 2 * (n : ℝ) ^ 2))
      = -(Real.pi ^ 2 * γ) * (n : ℝ) ^ 2 from by ring]

/-- The unit dual's mean energy is `π²` times the canonical mean
energy at the `π²`-rescaled coupling (review #17). -/
private lemma unitDual_meanEnergy (γ : ℝ) :
    unitQuadAction.dual.meanEnergy γ
      = Real.pi ^ 2 * quadraticMeanEnergy (Real.pi ^ 2 * γ) := by
  have hmom : unitQuadAction.dual.scaledMoment γ
      = Real.pi ^ 2 * ∑' k : ℤ, (k : ℝ) ^ 2
          * Real.exp (-(Real.pi ^ 2 * γ) * (k : ℝ) ^ 2) := by
    rw [← tsum_mul_left]
    refine (Equiv.tsum_eq zEquiv.symm
      (fun k : Fin 1 → ℤ => unitQuadAction.dual.energy k
        * Real.exp (-(γ * unitQuadAction.dual.energy k)))).symm.trans ?_
    refine tsum_congr fun n => ?_
    rw [unitDual_energy]
    show Real.pi ^ 2 * (n : ℝ) ^ 2
        * Real.exp (-(γ * (Real.pi ^ 2 * (n : ℝ) ^ 2)))
      = Real.pi ^ 2 * ((n : ℝ) ^ 2
          * Real.exp (-(Real.pi ^ 2 * γ) * (n : ℝ) ^ 2))
    rw [show -(γ * (Real.pi ^ 2 * (n : ℝ) ^ 2))
        = -(Real.pi ^ 2 * γ) * (n : ℝ) ^ 2 from by ring]
    ring
  show unitQuadAction.dual.scaledMoment γ
      / unitQuadAction.dual.scaledPartFn γ = _
  rw [hmom, unitDual_scaledPartFn γ, mul_div_assoc]
  rfl

/-- T-duality functional equation for mean energy:
    `(π²/α²)·⟨k²⟩_{π²/α} + ⟨k²⟩_α = 1/(2α)`.

    **The bundle temperature–duality functional equation**
    (`QuadLatticeAction.meanEnergy_T_dual`, review #17) **at the unit
    action**: `⟨E⟩(α) + α⁻²·⟨E⟩∨(α⁻¹) = 1/(2α)`, with the unit dual's
    mean energy identified as `π²·⟨k²⟩_{π²·α⁻¹}`
    (`unitDual_meanEnergy`). The scalar theorem no longer
    differentiates its own functional equation — the differentiation
    happens once, on the bundle. At α = π the two mean-energy terms
    coalesce into `2·⟨k²⟩_π = 1/(2π)`, giving
    `quadraticMeanEnergy_self_dual`. -/
theorem quadraticMeanEnergy_T_dual (α : ℝ) (hα : 0 < α) :
    (Real.pi ^ 2 / α ^ 2) * quadraticMeanEnergy (Real.pi ^ 2 / α) +
      quadraticMeanEnergy α = 1 / (2 * α) := by
  have h := unitQuadAction.meanEnergy_T_dual α hα
  rw [show unitQuadAction.meanEnergy α = quadraticMeanEnergy α from
      congrFun meanEnergy_unit α,
    unitDual_meanEnergy α⁻¹,
    show Real.pi ^ 2 * α⁻¹ = Real.pi ^ 2 / α from by
      rw [div_eq_mul_inv],
    Nat.cast_one] at h
  have heq : α⁻¹ ^ 2 * (Real.pi ^ 2 * quadraticMeanEnergy (Real.pi ^ 2 / α))
      = (Real.pi ^ 2 / α ^ 2) * quadraticMeanEnergy (Real.pi ^ 2 / α) := by
    rw [inv_pow, div_eq_mul_inv]
    ring
  rw [heq] at h
  linarith

/-- At the self-dual coupling α = π, the mean of `k²` is `1/(4π)` —
    **from the functional equation** (review #17): at `α = π` the two
    mean-energy terms of `quadraticMeanEnergy_T_dual` coalesce into
    `2·⟨k²⟩_π = 1/(2π)`. -/
theorem quadraticMeanEnergy_self_dual :
    quadraticMeanEnergy Real.pi = 1 / (4 * Real.pi) := by
  have hπ := Real.pi_pos
  have h := quadraticMeanEnergy_T_dual Real.pi hπ
  rw [show Real.pi ^ 2 / Real.pi = Real.pi from by
      rw [pow_two, mul_div_assoc, div_self hπ.ne', mul_one],
    show Real.pi ^ 2 / Real.pi ^ 2 = (1 : ℝ) from
      div_self (by positivity), one_mul] at h
  have h2 : (1 : ℝ) / (2 * Real.pi) = 2 * (1 / (4 * Real.pi)) := by
    rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [h2] at h
  linarith



end Simplicial
