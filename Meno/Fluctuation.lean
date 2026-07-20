import Meno.QuadraticAction
import Mathlib.Analysis.Calculus.SmoothSeries

/-! # Fluctuation–Dissipation at Every Rank (review #15)

The inverse-temperature scaling of a quadratic action: for
`A : QuadraticAction d` and `β > 0`, the Boltzmann family
`exp(−β·E_A)` has partition function `Z(β)` (`scaledPartFn`), energy
moments `M₁(β)`, `M₂(β)` (`scaledMoment`, `scaledMoment2`), and Gibbs
mean energy `⟨E⟩(β) = M₁/Z` (`meanEnergy`). This file proves, at
**every rank**:

* the moments are summable for every `β > 0` — the polynomial-times-
  Gaussian bounds `x·e⁻ˣ ≤ 2e^{−x/2}`, `x²·e⁻ˣ ≤ 16e^{−x/2}` against
  the half-temperature weight (`summable_scaledWeight`,
  `summable_energy_mul_scaledWeight`,
  `summable_energy_sq_mul_scaledWeight`);
* `Z' = −M₁` and `M₁' = −M₂` (`hasDerivAt_scaledPartFn`,
  `hasDerivAt_scaledMoment`) — differentiation under the lattice sum,
  by `hasDerivAt_tsum_of_isPreconnected` with the half-temperature
  domination;
* **fluctuation–dissipation**: `d⟨E⟩/dβ = −Var_β(E)`
  (`hasDerivAt_meanEnergy_eq_neg_gibbsVariance`), where `Var_β` is
  the genuine Gibbs variance of the energy under the β-scaled sector
  action (`scaledSector`);
* strict variance from any sector of nonzero energy
  (`scaledSector_gibbsVariance_energy_pos`) and hence **strict
  dissipation**: the mean energy strictly decreases in `β`
  (`meanEnergy_strictAntiOn`).

The scalar family of `Meno/Duality.lean` is the rank-one instance;
the intrinsic carrier consumes this engine through its cycle-basis
chart (`Meno/BasisIndependence.lean`). -/

namespace Meno

/-- `x·e⁻ˣ ≤ 2·e^{−x/2}`: one power of `x` is absorbed by half the
decay. -/
theorem mul_exp_neg_le (x : ℝ) :
    x * Real.exp (-x) ≤ 2 * Real.exp (-(x / 2)) := by
  have h1 : x ≤ 2 * Real.exp (x / 2) := by
    have h := Real.add_one_le_exp (x / 2)
    nlinarith [Real.exp_pos (x / 2)]
  calc x * Real.exp (-x) ≤ 2 * Real.exp (x / 2) * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 2 * Real.exp (-(x / 2)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- `x²·e⁻ˣ ≤ 16·e^{−x/2}`: two powers of `x` are absorbed by half
the decay. -/
theorem sq_mul_exp_neg_le {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-x) ≤ 16 * Real.exp (-(x / 2)) := by
  have h1 : x ≤ 4 * Real.exp (x / 4) := by
    have h := Real.add_one_le_exp (x / 4)
    nlinarith [Real.exp_pos (x / 4)]
  have h2 : x ^ 2 ≤ 16 * Real.exp (x / 2) := by
    have h3 := mul_le_mul h1 h1 hx (by positivity)
    calc x ^ 2 = x * x := sq x
      _ ≤ 4 * Real.exp (x / 4) * (4 * Real.exp (x / 4)) := h3
      _ = 16 * Real.exp (x / 2) := by
          rw [show (4 : ℝ) * Real.exp (x / 4) * (4 * Real.exp (x / 4))
              = 16 * (Real.exp (x / 4) * Real.exp (x / 4)) from by ring,
            ← Real.exp_add]
          congr 2
          ring
  calc x ^ 2 * Real.exp (-x) ≤ 16 * Real.exp (x / 2) * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = 16 * Real.exp (-(x / 2)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

namespace QuadraticAction

variable {d : ℕ} (A : QuadraticAction d)

/-- The β-scaled partition function `Z(β) = ∑ exp(−β·E)`. -/
noncomputable def scaledPartFn (β : ℝ) : ℝ :=
  ∑' k : Fin d → ℤ, Real.exp (-(β * A.energy k))

/-- The first energy moment `M₁(β) = ∑ E·exp(−β·E)`. -/
noncomputable def scaledMoment (β : ℝ) : ℝ :=
  ∑' k : Fin d → ℤ, A.energy k * Real.exp (-(β * A.energy k))

/-- The second energy moment `M₂(β) = ∑ E²·exp(−β·E)`. -/
noncomputable def scaledMoment2 (β : ℝ) : ℝ :=
  ∑' k : Fin d → ℤ, A.energy k ^ 2 * Real.exp (-(β * A.energy k))

/-- The Gibbs mean energy `⟨E⟩(β) = M₁(β)/Z(β)`. -/
noncomputable def meanEnergy (β : ℝ) : ℝ :=
  A.scaledMoment β / A.scaledPartFn β

/-- The β-scaled Boltzmann weight is summable — `β·Q` is still
positive definite. -/
theorem summable_scaledWeight {β : ℝ} (hβ : 0 < β) :
    Summable (fun k : Fin d → ℤ => Real.exp (-(β * A.energy k))) := by
  have hpos : (β • A.Q).PosDef := posDef_smul' A.Q_posDef hβ
  refine (summable_exp_neg_quadForm hpos).congr fun k => ?_
  congr 1
  show -(∑ i, ∑ j, (β • A.Q) i j * (k i : ℝ) * (k j : ℝ))
    = -(β * (∑ i, ∑ j, A.Q i j * (k i : ℝ) * (k j : ℝ)))
  rw [neg_inj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  ring

/-- The first energy moment converges for every `β > 0`. -/
theorem summable_energy_mul_scaledWeight {β : ℝ} (hβ : 0 < β) :
    Summable (fun k : Fin d → ℤ =>
      A.energy k * Real.exp (-(β * A.energy k))) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (A.energy_nonneg k) (Real.exp_pos _).le)
    (fun k => ?_)
    ((A.summable_scaledWeight (show (0 : ℝ) < β / 2 by linarith)).mul_left
      (2 / β))
  have hb := mul_exp_neg_le (β * A.energy k)
  have harg : β * A.energy k / 2 = β / 2 * A.energy k := by ring
  rw [harg] at hb
  calc A.energy k * Real.exp (-(β * A.energy k))
      = (1 / β) * (β * A.energy k * Real.exp (-(β * A.energy k))) := by
        field_simp
    _ ≤ (1 / β) * (2 * Real.exp (-(β / 2 * A.energy k))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 2 / β * Real.exp (-(β / 2 * A.energy k)) := by ring

/-- The second energy moment converges for every `β > 0`. -/
theorem summable_energy_sq_mul_scaledWeight {β : ℝ} (hβ : 0 < β) :
    Summable (fun k : Fin d → ℤ =>
      A.energy k ^ 2 * Real.exp (-(β * A.energy k))) := by
  refine Summable.of_nonneg_of_le
    (fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (fun k => ?_)
    ((A.summable_scaledWeight (show (0 : ℝ) < β / 2 by linarith)).mul_left
      (16 / β ^ 2))
  have hb := sq_mul_exp_neg_le
    (mul_nonneg hβ.le (A.energy_nonneg k))
  have harg : β * A.energy k / 2 = β / 2 * A.energy k := by ring
  rw [harg] at hb
  have hβne : β ≠ 0 := hβ.ne'
  calc A.energy k ^ 2 * Real.exp (-(β * A.energy k))
      = (1 / β ^ 2) * ((β * A.energy k) ^ 2
          * Real.exp (-(β * A.energy k))) := by
        field_simp
    _ ≤ (1 / β ^ 2) * (16 * Real.exp (-(β / 2 * A.energy k))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 16 / β ^ 2 * Real.exp (-(β / 2 * A.energy k)) := by ring

/-- The β-scaled partition function is positive. -/
theorem scaledPartFn_pos {β : ℝ} (hβ : 0 < β) : 0 < A.scaledPartFn β :=
  (A.summable_scaledWeight hβ).tsum_pos
    (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)

/-- **`Z′ = −M₁`** (review #15): differentiation under the lattice
sum, dominated at half temperature. -/
theorem hasDerivAt_scaledPartFn {β : ℝ} (hβ : 0 < β) :
    HasDerivAt A.scaledPartFn (-A.scaledMoment β) β := by
  have hval : -A.scaledMoment β
      = ∑' k : Fin d → ℤ,
          -(A.energy k * Real.exp (-(β * A.energy k))) := by
    rw [tsum_neg]
    rfl
  rw [hval]
  show HasDerivAt
    (fun γ : ℝ => ∑' k : Fin d → ℤ, Real.exp (-(γ * A.energy k)))
    (∑' k : Fin d → ℤ, -(A.energy k * Real.exp (-(β * A.energy k)))) β
  exact hasDerivAt_tsum_of_isPreconnected
    (g := fun (k : Fin d → ℤ) (γ : ℝ) => Real.exp (-(γ * A.energy k)))
    (g' := fun (k : Fin d → ℤ) (γ : ℝ) =>
      -(A.energy k * Real.exp (-(γ * A.energy k))))
    (u := fun k => A.energy k * Real.exp (-(β / 2 * A.energy k)))
    (t := Set.Ioi (β / 2))
    (y₀ := β)
    (A.summable_energy_mul_scaledWeight
      (show (0 : ℝ) < β / 2 by linarith))
    isOpen_Ioi
    isPreconnected_Ioi
    (fun k y _ => by
      have hlin : HasDerivAt (fun γ : ℝ => -(γ * A.energy k))
          (-(1 * A.energy k)) y :=
        ((hasDerivAt_id y).mul_const _).neg
      have hexp := hlin.exp
      convert hexp using 1
      ring)
    (fun k y (hy : β / 2 < y) => by
      show |-(A.energy k * Real.exp (-(y * A.energy k)))|
        ≤ A.energy k * Real.exp (-(β / 2 * A.energy k))
      rw [abs_neg, abs_of_nonneg
        (mul_nonneg (A.energy_nonneg k) (Real.exp_pos _).le)]
      refine mul_le_mul_of_nonneg_left ?_ (A.energy_nonneg k)
      refine Real.exp_le_exp_of_le ?_
      have hE := A.energy_nonneg k
      nlinarith)
    (Set.mem_Ioi.mpr (by linarith))
    (A.summable_scaledWeight hβ)
    (Set.mem_Ioi.mpr (by linarith))

/-- **`M₁′ = −M₂`** (review #15). -/
theorem hasDerivAt_scaledMoment {β : ℝ} (hβ : 0 < β) :
    HasDerivAt A.scaledMoment (-A.scaledMoment2 β) β := by
  have hval : -A.scaledMoment2 β
      = ∑' k : Fin d → ℤ,
          -(A.energy k ^ 2 * Real.exp (-(β * A.energy k))) := by
    rw [tsum_neg]
    rfl
  rw [hval]
  show HasDerivAt
    (fun γ : ℝ => ∑' k : Fin d → ℤ,
      A.energy k * Real.exp (-(γ * A.energy k)))
    (∑' k : Fin d → ℤ,
      -(A.energy k ^ 2 * Real.exp (-(β * A.energy k)))) β
  exact hasDerivAt_tsum_of_isPreconnected
    (g := fun (k : Fin d → ℤ) (γ : ℝ) =>
      A.energy k * Real.exp (-(γ * A.energy k)))
    (g' := fun (k : Fin d → ℤ) (γ : ℝ) =>
      -(A.energy k ^ 2 * Real.exp (-(γ * A.energy k))))
    (u := fun k => A.energy k ^ 2 * Real.exp (-(β / 2 * A.energy k)))
    (t := Set.Ioi (β / 2))
    (y₀ := β)
    (A.summable_energy_sq_mul_scaledWeight
      (show (0 : ℝ) < β / 2 by linarith))
    isOpen_Ioi
    isPreconnected_Ioi
    (fun k y _ => by
      have hlin : HasDerivAt (fun γ : ℝ => -(γ * A.energy k))
          (-(1 * A.energy k)) y :=
        ((hasDerivAt_id y).mul_const _).neg
      have hexp := (hlin.exp).const_mul (A.energy k)
      convert hexp using 1
      ring)
    (fun k y (hy : β / 2 < y) => by
      show |-(A.energy k ^ 2 * Real.exp (-(y * A.energy k)))|
        ≤ A.energy k ^ 2 * Real.exp (-(β / 2 * A.energy k))
      rw [abs_neg, abs_of_nonneg
        (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      refine Real.exp_le_exp_of_le ?_
      have hE := A.energy_nonneg k
      nlinarith)
    (Set.mem_Ioi.mpr (by linarith))
    (A.summable_energy_mul_scaledWeight hβ)
    (Set.mem_Ioi.mpr (by linarith))

/-- The derivative of the mean energy, in moment form:
`⟨E⟩′ = −(M₂/Z − ⟨E⟩²)`. -/
theorem hasDerivAt_meanEnergy {β : ℝ} (hβ : 0 < β) :
    HasDerivAt A.meanEnergy
      (-(A.scaledMoment2 β / A.scaledPartFn β - A.meanEnergy β ^ 2)) β := by
  have hZne := (A.scaledPartFn_pos hβ).ne'
  have h := (A.hasDerivAt_scaledMoment hβ).div
    (A.hasDerivAt_scaledPartFn hβ) hZne
  convert h using 1
  show -(A.scaledMoment2 β / A.scaledPartFn β
      - (A.scaledMoment β / A.scaledPartFn β) ^ 2)
    = (-A.scaledMoment2 β * A.scaledPartFn β
        - A.scaledMoment β * -A.scaledMoment β) / A.scaledPartFn β ^ 2
  field_simp
  ring

/-! ## The β-scaled sector action and the genuine Gibbs variance -/

/-- **The β-scaled sector action** (review #15): energy `β·E_A`,
ground state the zero sector. -/
noncomputable def scaledSector (β : ℝ) (hβ : 0 < β) : SectorAction.{0} where
  Λ := Fin d → ℤ
  E k := β * A.energy k
  E_zero := ⟨0, by rw [A.energy_zero, mul_zero]⟩
  E_nonneg k := mul_nonneg hβ.le (A.energy_nonneg k)
  summable := A.summable_scaledWeight hβ


/-- The scaled sector's Gibbs mean of the energy is `⟨E⟩(β)`. -/
theorem scaledSector_gibbsExpect_energy (β : ℝ) (hβ : 0 < β) :
    (A.scaledSector β hβ).gibbsExpect A.energy = A.meanEnergy β := by
  have hterm : ∀ k : Fin d → ℤ,
      A.energy k * (A.scaledSector β hβ).gibbsMass k
        = A.energy k * Real.exp (-(β * A.energy k)) / A.scaledPartFn β := by
    intro k
    show A.energy k * ((A.scaledSector β hβ).weight k
      / (A.scaledSector β hβ).partFn) = _
    rw [mul_div_assoc]
    rfl
  show (∑' k, A.energy k * (A.scaledSector β hβ).gibbsMass k) = _
  rw [tsum_congr hterm, tsum_div_const]
  rfl

/-- The scaled sector's Gibbs mean of the squared energy is
`M₂(β)/Z(β)`. -/
theorem scaledSector_gibbsExpect_energy_sq (β : ℝ) (hβ : 0 < β) :
    (A.scaledSector β hβ).gibbsExpect (fun k => A.energy k ^ 2)
      = A.scaledMoment2 β / A.scaledPartFn β := by
  have hterm : ∀ k : Fin d → ℤ,
      A.energy k ^ 2 * (A.scaledSector β hβ).gibbsMass k
        = A.energy k ^ 2 * Real.exp (-(β * A.energy k))
          / A.scaledPartFn β := by
    intro k
    show A.energy k ^ 2 * ((A.scaledSector β hβ).weight k
      / (A.scaledSector β hβ).partFn) = _
    rw [mul_div_assoc]
    rfl
  show (∑' k, A.energy k ^ 2 * (A.scaledSector β hβ).gibbsMass k) = _
  rw [tsum_congr hterm, tsum_div_const]
  rfl

/-- The scaled sector's Gibbs variance of the energy, in moment
form. -/
theorem scaledSector_gibbsVariance_energy (β : ℝ) (hβ : 0 < β) :
    (A.scaledSector β hβ).gibbsVariance A.energy
      = A.scaledMoment2 β / A.scaledPartFn β - A.meanEnergy β ^ 2 := by
  show (A.scaledSector β hβ).gibbsExpect (fun k => A.energy k ^ 2)
      - (A.scaledSector β hβ).gibbsExpect A.energy ^ 2 = _
  rw [A.scaledSector_gibbsExpect_energy_sq β hβ,
    A.scaledSector_gibbsExpect_energy β hβ]

/-- **FLUCTUATION–DISSIPATION AT EVERY RANK** (review #15): the
derivative of the Gibbs mean energy in the inverse temperature is
minus the Gibbs variance of the energy — response equals
fluctuation, for every positive-definite Gram at every rank. -/
theorem hasDerivAt_meanEnergy_eq_neg_gibbsVariance (β : ℝ) (hβ : 0 < β) :
    HasDerivAt A.meanEnergy
      (-((A.scaledSector β hβ).gibbsVariance A.energy)) β := by
  have h := A.hasDerivAt_meanEnergy hβ
  rwa [← A.scaledSector_gibbsVariance_energy β hβ] at h

/-- The first energy moment of the scaled Gibbs law is summable. -/
theorem summable_energy_gibbs (β : ℝ) (hβ : 0 < β) :
    Summable (fun k => A.energy k * (A.scaledSector β hβ).gibbsMass k) := by
  refine ((A.summable_energy_mul_scaledWeight hβ).div_const
    (A.scaledPartFn β)).congr fun k => ?_
  show A.energy k * Real.exp (-(β * A.energy k)) / A.scaledPartFn β = _
  rw [mul_div_assoc]
  rfl

/-- The second energy moment of the scaled Gibbs law is summable. -/
theorem summable_energy_sq_gibbs (β : ℝ) (hβ : 0 < β) :
    Summable (fun k =>
      A.energy k ^ 2 * (A.scaledSector β hβ).gibbsMass k) := by
  refine ((A.summable_energy_sq_mul_scaledWeight hβ).div_const
    (A.scaledPartFn β)).congr fun k => ?_
  show A.energy k ^ 2 * Real.exp (-(β * A.energy k)) / A.scaledPartFn β = _
  rw [mul_div_assoc]
  rfl

/-- **Strict Gibbs fluctuation of the energy** (review #15): a single
sector of nonzero energy makes the variance strictly positive at
every inverse temperature. -/
theorem scaledSector_gibbsVariance_energy_pos (β : ℝ) (hβ : 0 < β)
    {k₀ : Fin d → ℤ} (hk₀ : A.energy k₀ ≠ 0) :
    0 < (A.scaledSector β hβ).gibbsVariance A.energy := by
  have hE₀ : 0 < A.energy k₀ :=
    lt_of_le_of_ne (A.energy_nonneg k₀) (Ne.symm hk₀)
  by_cases hc : (A.scaledSector β hβ).gibbsExpect A.energy = 0
  · refine (A.scaledSector β hβ).gibbsVariance_pos _
      (A.summable_energy_sq_gibbs β hβ) (A.summable_energy_gibbs β hβ)
      (k₀ := k₀) ?_
    rw [hc]
    exact ne_of_gt hE₀
  · refine (A.scaledSector β hβ).gibbsVariance_pos _
      (A.summable_energy_sq_gibbs β hβ) (A.summable_energy_gibbs β hβ)
      (k₀ := (0 : Fin d → ℤ)) ?_
    rw [A.energy_zero]
    exact fun h => hc h.symm

/-- **STRICT DISSIPATION** (review #15): with any sector of nonzero
energy, the Gibbs mean energy strictly decreases in the inverse
temperature — `d⟨E⟩/dβ = −Var < 0`. -/
theorem meanEnergy_strictAntiOn (h : ∃ k, A.energy k ≠ 0) :
    StrictAntiOn A.meanEnergy (Set.Ioi 0) := by
  obtain ⟨k₀, hk₀⟩ := h
  apply strictAntiOn_of_deriv_neg (convex_Ioi _)
  · intro β hβ
    exact (A.hasDerivAt_meanEnergy (Set.mem_Ioi.mp hβ)).continuousAt.continuousWithinAt
  · intro β hβ
    rw [interior_Ioi] at hβ
    rw [(A.hasDerivAt_meanEnergy (Set.mem_Ioi.mp hβ)).deriv]
    have hV := A.scaledSector_gibbsVariance_energy_pos β
      (Set.mem_Ioi.mp hβ) (k₀ := k₀) hk₀
    rw [A.scaledSector_gibbsVariance_energy β (Set.mem_Ioi.mp hβ)] at hV
    linarith

end QuadraticAction

end Meno
