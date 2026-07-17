import Meno.QuadraticAction
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Matrix.PosDef

/-! # Multivariate Poisson Summation and the General Siegel–Poisson Duality

This file closes falsification clause #3 of PLAN.md at full generality:
the Siegel–Poisson duality `Z(π²·Q⁻¹) = √(det Q / π^r) · Z(Q)` for an
**arbitrary** symmetric positive-definite Gram form `Q`, not merely a
diagonal one.

The missing ingredient was Poisson summation over the integer lattice
`ℤ^d`. Mathlib (at this pin) has the multivariate torus Fourier machinery
(`UnitAddTorus`, `mFourierCoeff`, `hasSum_mFourier_series_apply_of_summable`)
and the one-dimensional bridge (`Real.fourierCoeff_tsum_comp_add`) but not
the multivariate bridge connecting periodization over `ℤ^d` to Euclidean
Fourier samples. We build that bridge here, **scope-cut to the Gaussian
family** `x ↦ exp(-π xᵀMx)`: continuity of the periodization and
summability of its Fourier coefficients — the analytically delicate steps
of the general theorem — are elementary for Gaussians.

Spectral diagonalization cannot substitute for the bridge: orthogonal
maps do not preserve `ℤ^d` (the Phase 14 record documents this). The
correct division of labor, implemented here, is that diagonalization is
legitimate on the *integral* side (Lebesgue measure is linear-map
covariant) and the periodization bridge handles the *sum* side.

## Contents

* `Matrix.PosDef.exists_coercivity` — eigenvalue-free coercivity: a
  positive-definite form dominates `c · ∑ xᵢ²` for some `c > 0`,
  by minimizing on the compact sum-of-squares sphere.
* `summable_exp_neg_quadForm` — Boltzmann weights of a positive-definite
  quadratic action are summable on `ℤ^d`. Retires the Session-1
  deferral: `summable` no longer needs to be a field of
  `QuadraticAction` (we keep the field but provide the constructor).
* `QuadraticAction.of_posDef` — constructor deriving summability.
* the multivariate periodization bridge and Gaussian Poisson summation.
* `QuadraticAction.dual` (general) and `QuadraticAction.duality`.
-/

namespace Meno

open scoped BigOperators
open Matrix

/-! ## Coercivity of positive-definite forms, eigenvalue-free

The plan sketched `E_Q(k) ≥ λ_min ‖k‖²` via `Matrix.PosDef.eigenvalues_pos`.
We avoid eigenvalue bookkeeping entirely: the form attains a positive
minimum `c` on the compact sphere `{x | ∑ xᵢ² = 1}`, and degree-2
homogeneity scales that bound to all of `ℝ^d`. -/

/-- The quadratic form of a matrix is continuous. -/
private lemma continuous_quadForm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    Continuous (fun x : Fin d → ℝ => x ⬝ᵥ M.mulVec x) := by
  unfold dotProduct Matrix.mulVec
  fun_prop

/-- **Coercivity**: a positive-definite form dominates a positive multiple
of the sum of squares. Eigenvalue-free: minimize on the compact unit
sphere of `∑ xᵢ²`, then scale by homogeneity. -/
theorem _root_.Matrix.PosDef.exists_coercivity {d : ℕ}
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin d → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ M.mulVec x := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- rank 0: both sides are empty sums
    subst hd
    refine ⟨1, one_pos, fun x => ?_⟩
    simp [dotProduct]
  · -- the sphere S = {x | ∑ xᵢ² = 1} is compact and nonempty
    set S : Set (Fin d → ℝ) := {x | ∑ i, x i ^ 2 = 1} with hS
    have hcont_sq : Continuous (fun x : Fin d → ℝ => ∑ i, x i ^ 2) := by fun_prop
    have hclosed : IsClosed S := isClosed_eq hcont_sq continuous_const
    have hbdd : Bornology.IsBounded S := by
      rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨1, fun x hx => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      have h1 : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      rw [hx] at h1
      rw [Real.norm_eq_abs]
      nlinarith [abs_nonneg (x i), sq_abs (x i)]
    have hcompact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
    have hne : S.Nonempty := by
      refine ⟨Pi.single ⟨0, hd⟩ 1, ?_⟩
      simp [hS, Pi.single_apply]
    obtain ⟨x₀, hx₀S, hx₀min⟩ :=
      hcompact.exists_isMinOn hne (continuous_quadForm M).continuousOn
    have hx₀ne : x₀ ≠ 0 := by
      intro h0
      rw [hS] at hx₀S
      simp only [Set.mem_setOf_eq, h0, Pi.zero_apply] at hx₀S
      simp at hx₀S
    have hx₀pos : 0 < x₀ ⬝ᵥ M.mulVec x₀ := by
      have h := (posDef_iff_dotProduct_mulVec.mp hM).2 hx₀ne
      have hstar : star x₀ = x₀ := funext fun i => star_trivial _
      rwa [hstar] at h
    refine ⟨x₀ ⬝ᵥ M.mulVec x₀, hx₀pos, fun x => ?_⟩
    rcases eq_or_ne x 0 with hx | hx
    · simp [hx, Matrix.mulVec_zero, dotProduct_zero]
    · -- scale x to the sphere
      have hsum_pos : 0 < ∑ i, x i ^ 2 := by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
        exact Finset.sum_pos' (fun j _ => sq_nonneg (x j))
          ⟨i, Finset.mem_univ i,
            lt_of_le_of_ne (sq_nonneg (x i)) (Ne.symm (pow_ne_zero 2 hi))⟩
      set t : ℝ := Real.sqrt (∑ i, x i ^ 2) with ht
      have ht_pos : 0 < t := Real.sqrt_pos.mpr hsum_pos
      have ht_sq : t ^ 2 = ∑ i, x i ^ 2 := Real.sq_sqrt hsum_pos.le
      have hy : (t⁻¹ • x) ∈ S := by
        rw [hS]
        simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, mul_pow]
        rw [← Finset.mul_sum, ← ht_sq]
        field_simp
      have hval : (t⁻¹ • x) ⬝ᵥ M.mulVec (t⁻¹ • x) = t⁻¹ ^ 2 * (x ⬝ᵥ M.mulVec x) := by
        rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct]
        simp [smul_eq_mul, sq]
        ring
      have := isMinOn_iff.mp hx₀min _ hy
      rw [hval] at this
      have h2 : (x₀ ⬝ᵥ M.mulVec x₀) * t ^ 2 ≤ x ⬝ᵥ M.mulVec x := by
        have htne : t ≠ 0 := ne_of_gt ht_pos
        calc (x₀ ⬝ᵥ M.mulVec x₀) * t ^ 2
            ≤ (t⁻¹ ^ 2 * (x ⬝ᵥ M.mulVec x)) * t ^ 2 := by
              apply mul_le_mul_of_nonneg_right this (by positivity)
          _ = x ⬝ᵥ M.mulVec x := by field_simp
      calc (x₀ ⬝ᵥ M.mulVec x₀) * (∑ i, x i ^ 2)
          = (x₀ ⬝ᵥ M.mulVec x₀) * t ^ 2 := by rw [ht_sq]
        _ ≤ x ⬝ᵥ M.mulVec x := h2

/-! ## Summability of positive-definite Boltzmann weights on `ℤ^d`

`exp(-kᵀMk) ≤ ∏ᵢ exp(-c kᵢ²)` by coercivity, and the right side is
summable by the rank-r factorization machinery already in the spine
(`summable_finPi_prod` with the scalar Gaussian sums). This retires
Session-1 architectural decision 1: summability of a `QuadraticAction`
is derivable from `Q.PosDef`, not merely package-able as a field. -/

/-- Boltzmann weights of a positive-definite quadratic form are summable
over the integer lattice. -/
theorem summable_exp_neg_quadForm {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosDef) :
    Summable (fun k : Fin d → ℤ =>
      Real.exp (-(∑ i, ∑ j, M i j * (k i : ℝ) * (k j : ℝ)))) := by
  obtain ⟨c, hc, hcoer⟩ := hM.exists_coercivity
  have hquad : ∀ k : Fin d → ℤ,
      ∑ i, ∑ j, M i j * (k i : ℝ) * (k j : ℝ)
        = (fun i => (k i : ℝ)) ⬝ᵥ M.mulVec (fun i => (k i : ℝ)) := by
    intro k
    show ∑ i, ∑ j, M i j * (k i : ℝ) * (k j : ℝ)
      = ∑ i, (k i : ℝ) * ∑ j, M i j * (k j : ℝ)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  refine Summable.of_nonneg_of_le (fun k => (Real.exp_pos _).le) (fun k => ?_)
    (QuadraticAction.summable_finPi_prod d (fun _ z => Real.exp (-c * (z : ℝ) ^ 2))
      (fun _ z => (Real.exp_pos _).le)
      (fun _ => QuadraticAction.summable_scalarPartFn c hc))
  calc Real.exp (-(∑ i, ∑ j, M i j * (k i : ℝ) * (k j : ℝ)))
      ≤ Real.exp (-(c * ∑ i, (k i : ℝ) ^ 2)) := by
        apply Real.exp_le_exp.mpr
        rw [neg_le_neg_iff, hquad k]
        exact hcoer _
    _ = ∏ i, Real.exp (-c * (k i : ℝ) ^ 2) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)

/-- Constructor for `QuadraticAction` deriving summability from positive
definiteness. Retires the Session-1 deferral of this derivation. -/
noncomputable def QuadraticAction.of_posDef {r : ℕ}
    (Q : Matrix (Fin r) (Fin r) ℝ) (hsymm : Q.IsSymm) (hpos : Q.PosDef) :
    QuadraticAction r where
  Q := Q
  Q_symm := hsymm
  Q_posDef := hpos
  summable := summable_exp_neg_quadForm hpos

/-! ## The Gaussian family and its periodization

`gaussian M x = exp(-π · xᵀMx)` is the function to which Poisson
summation will be applied. Its periodization over `ℤ^d` is shown
continuous via a box-uniform bound: on `{x | ∀ i, |x i| ≤ B}` each
translate is dominated coordinatewise using `(t + z)² ≥ z²/2 - B²`
for `|t| ≤ B`, so the sup-norms form a product of scalar Gaussian
tails — summable by the spine's factorization machinery. -/

variable {d : ℕ}

/-- The Gaussian of a quadratic form: `x ↦ exp(-π · xᵀMx)`. -/
noncomputable def gaussian (M : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) : ℝ :=
  Real.exp (-Real.pi * (x ⬝ᵥ M.mulVec x))

theorem gaussian_pos (M : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    0 < gaussian M x := Real.exp_pos _

theorem continuous_gaussian (M : Matrix (Fin d) (Fin d) ℝ) :
    Continuous (gaussian M) :=
  Real.continuous_exp.comp ((continuous_const.mul (continuous_quadForm M)))

/-- Coordinatewise shift bound: for `|t| ≤ B`, `(t + z)² ≥ z²/2 - B²`. -/
private lemma sq_add_ge_of_abs_le {B t z : ℝ} (ht : |t| ≤ B) :
    z ^ 2 / 2 - B ^ 2 ≤ (t + z) ^ 2 := by
  obtain ⟨h1, h2⟩ := abs_le.mp ht
  nlinarith [sq_nonneg (2 * t + z), mul_nonneg (by linarith : (0:ℝ) ≤ B - t)
    (by linarith : (0:ℝ) ≤ B + t)]

/-- The dominating weights for Gaussian translates over a box of
half-width `B`: `w(n) = exp(π·c·d·B²) · ∏ᵢ exp(-(π·c/2)·nᵢ²)`. -/
private lemma summable_translate_weights (c B : ℝ) (hc : 0 < c) :
    Summable (fun n : Fin d → ℤ =>
      Real.exp (Real.pi * c * d * B ^ 2) *
        ∏ i, Real.exp (-(Real.pi * c / 2) * (n i : ℝ) ^ 2)) :=
  ((QuadraticAction.summable_finPi_prod d
      (fun _ z => Real.exp (-(Real.pi * c / 2) * (z : ℝ) ^ 2))
      (fun _ z => (Real.exp_pos _).le)
      (fun _ => QuadraticAction.summable_scalarPartFn _
        (by positivity))).mul_left _)

/-- Box-uniform domination of Gaussian translates: for `‖x‖ ≤ B` (sup
norm) the translate by `n` is at most the `n`-th dominating weight. -/
private lemma gaussian_translate_le {M : Matrix (Fin d) (Fin d) ℝ}
    {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ y : Fin d → ℝ, c * (∑ i, y i ^ 2) ≤ y ⬝ᵥ M.mulVec y)
    {B : ℝ} {x : Fin d → ℝ} (hx : ∀ i, |x i| ≤ B) (n : Fin d → ℤ) :
    gaussian M (x + fun i => (n i : ℝ)) ≤
      Real.exp (Real.pi * c * d * B ^ 2) *
        ∏ i, Real.exp (-(Real.pi * c / 2) * (n i : ℝ) ^ 2) := by
  set y : Fin d → ℝ := x + fun i => (n i : ℝ) with hy
  have step1 : gaussian M y ≤ Real.exp (-Real.pi * (c * ∑ i, y i ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have := hcoer y
    nlinarith [Real.pi_pos]
  have step2 : ∑ i, ((n i : ℝ) ^ 2 / 2 - B ^ 2) ≤ ∑ i, y i ^ 2 := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    have : y i = x i + (n i : ℝ) := rfl
    rw [this]
    exact sq_add_ge_of_abs_le (hx i)
  refine step1.trans ?_
  have hexp : Real.exp (Real.pi * c * d * B ^ 2) *
      ∏ i, Real.exp (-(Real.pi * c / 2) * (n i : ℝ) ^ 2)
      = Real.exp (Real.pi * c * d * B ^ 2
          + ∑ i, -(Real.pi * c / 2) * (n i : ℝ) ^ 2) := by
    rw [Real.exp_add, Real.exp_sum]
  rw [hexp]
  apply Real.exp_le_exp.mpr
  have hsum : ∑ i, ((n i : ℝ) ^ 2 / 2 - B ^ 2)
      = (∑ i, (n i : ℝ) ^ 2) / 2 - d * B ^ 2 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum2 : ∑ i, -(Real.pi * c / 2) * (n i : ℝ) ^ 2
      = -(Real.pi * c / 2) * ∑ i, (n i : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
  rw [hsum2]
  rw [hsum] at step2
  have hπc : (0 : ℝ) < Real.pi * c := mul_pos Real.pi_pos hc
  nlinarith [mul_le_mul_of_nonneg_left step2 hπc.le]

/-- Pointwise summability of Gaussian translates over the lattice. -/
theorem summable_gaussian_translates {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosDef) (x : Fin d → ℝ) :
    Summable (fun n : Fin d → ℤ => gaussian M (x + fun i => (n i : ℝ))) := by
  obtain ⟨c, hc, hcoer⟩ := hM.exists_coercivity
  refine Summable.of_nonneg_of_le (fun n => (gaussian_pos M _).le)
    (fun n => gaussian_translate_le hc hcoer
      (B := ‖x‖) (fun i => by
        rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x i) n)
    (summable_translate_weights c ‖x‖ hc)

/-- The periodization of the Gaussian over the integer lattice `ℤ^d`. -/
noncomputable def periodization (M : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) : ℝ :=
  ∑' n : Fin d → ℤ, gaussian M (x + fun i => (n i : ℝ))

/-- The periodization is invariant under integer translation: the defining
property that lets it descend to the torus. -/
theorem periodization_add_int (M : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) (m : Fin d → ℤ) :
    periodization M (x + fun i => (m i : ℝ)) = periodization M x := by
  unfold periodization
  calc ∑' n : Fin d → ℤ, gaussian M ((x + fun i => (m i : ℝ)) + fun i => (n i : ℝ))
      = ∑' n : Fin d → ℤ, gaussian M (x + fun i => (((n + m) i : ℤ) : ℝ)) := by
        refine tsum_congr (fun n => ?_)
        congr 1
        funext i
        simp only [Pi.add_apply]
        push_cast
        ring
    _ = ∑' n : Fin d → ℤ, gaussian M (x + fun i => (n i : ℝ)) :=
        (Equiv.addRight m).tsum_eq
          (fun n : Fin d → ℤ => gaussian M (x + fun i => (n i : ℝ)))

/-- Continuity of the periodization: locally, the translate family is
uniformly dominated by summable weights. -/
theorem continuous_periodization {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosDef) : Continuous (periodization M) := by
  obtain ⟨c, hc, hcoer⟩ := hM.exists_coercivity
  rw [continuous_iff_continuousAt]
  intro x₀
  set B : ℝ := ‖x₀‖ + 1 with hB
  refine ContinuousOn.continuousAt (s := Metric.closedBall 0 B) ?_ ?_
  · refine continuousOn_tsum
      (fun n => ((continuous_gaussian M).comp
        (continuous_id.add continuous_const)).continuousOn)
      (summable_translate_weights c B hc) (fun n x hxmem => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (gaussian_pos M _)]
    refine gaussian_translate_le hc hcoer (fun i => ?_) n
    rw [Metric.mem_closedBall, dist_zero_right] at hxmem
    calc |x i| = ‖x i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x‖ := norm_le_pi_norm x i
      _ ≤ B := hxmem
  · refine Filter.mem_of_superset
      (Metric.isOpen_ball.mem_nhds ?_) Metric.ball_subset_closedBall
    rw [Metric.mem_ball, dist_zero_right, hB]
    exact lt_add_one _

/-! ## Descent to the torus

The periodization is `ℤ^d`-invariant, so it descends to a function on
`UnitAddTorus d = (Fin d) → ℝ/ℤ`. The torus is a product of quotients
(not a quotient of the product), so there is no single `Quotient.lift`;
we define the descent by choosing the canonical `Ico`-representative in
each coordinate and prove it agrees with the periodization on every
lift. Continuity comes from the compact-quotient argument: the closed
unit cube is compact, the torus is Hausdorff, and a continuous
surjection from a compact space to a Hausdorff space is a quotient
map. -/

section Torus

open UnitAddTorus Topology

attribute [local instance] Real.fact_zero_lt_one

/-- The coordinatewise quotient map from `ℝ^d` to the unit torus. -/
def torusMk (x : Fin d → ℝ) : UnitAddTorus (Fin d) :=
  fun i => (x i : UnitAddCircle)

theorem continuous_torusMk : Continuous (torusMk (d := d)) :=
  continuous_pi (fun i => continuous_quotient_mk'.comp (continuous_apply i))

/-- Coordinatewise equality in the torus is integer-vector difference of
lifts. -/
theorem torusMk_eq_iff {x y : Fin d → ℝ} :
    torusMk x = torusMk y ↔ ∀ i, ∃ k : ℤ, x i = y i + k := by
  constructor
  · intro h i
    have hi : (x i : UnitAddCircle) = (y i : UnitAddCircle) := congrFun h i
    have hsub : x i - y i ∈ AddSubgroup.zmultiples (1 : ℝ) :=
      (QuotientAddGroup.eq_iff_sub_mem).mp hi
    obtain ⟨k, hk⟩ := hsub
    simp only [zsmul_eq_mul, mul_one] at hk
    exact ⟨k, by linarith⟩
  · intro h
    funext i
    obtain ⟨k, hk⟩ := h i
    refine (QuotientAddGroup.eq_iff_sub_mem).mpr ?_
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one]
    rw [hk]
    ring

/-- Every torus point has a lift in the closed unit cube (via `Int.fract`
of an arbitrary lift). -/
theorem torusMk_surjOn_cube (z : UnitAddTorus (Fin d)) :
    ∃ x : Fin d → ℝ, x ∈ Set.Icc (0 : Fin d → ℝ) 1 ∧ torusMk x = z := by
  have hrep : ∀ i, ∃ a : ℝ, (a : UnitAddCircle) = z i := fun i =>
    Quotient.exists_rep (z i) |>.imp (fun a ha => ha)
  choose a ha using hrep
  refine ⟨fun i => Int.fract (a i), ⟨fun i => Int.fract_nonneg _,
    fun i => (Int.fract_lt_one _).le⟩, ?_⟩
  funext i
  rw [← ha i]
  refine (QuotientAddGroup.eq_iff_sub_mem).mpr ⟨-⌊a i⌋, ?_⟩
  simp only [zsmul_eq_mul, mul_one]
  rw [Int.fract]
  push_cast
  ring

theorem torusMk_surjective : Function.Surjective (torusMk (d := d)) :=
  fun z => (torusMk_surjOn_cube z).imp (fun _ h => h.2)

/-- The descent of the Gaussian periodization to the torus, via a choice
of lift. Well-definedness is `torusPeriodization_mk`. -/
noncomputable def torusPeriodization (M : Matrix (Fin d) (Fin d) ℝ) :
    UnitAddTorus (Fin d) → ℝ :=
  periodization M ∘ Function.surjInv torusMk_surjective

/-- The descent property: `torusPeriodization ∘ torusMk = periodization`.
Any two lifts differ by an integer vector, and the periodization is
invariant under integer translation. -/
theorem torusPeriodization_mk (M : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) :
    torusPeriodization M (torusMk x) = periodization M x := by
  unfold torusPeriodization
  set x' : Fin d → ℝ := Function.surjInv torusMk_surjective (torusMk x) with hx'
  have hmk : torusMk x' = torusMk x :=
    Function.surjInv_eq torusMk_surjective (torusMk x)
  obtain hdiff := torusMk_eq_iff.mp hmk
  choose k hk using hdiff
  show periodization M x' = periodization M x
  have : x' = x + fun i => (k i : ℝ) := funext (fun i => hk i)
  rw [this, periodization_add_int]

/-- Continuity of the torus periodization, by the compact-quotient
argument: the closed unit cube is compact, the torus is Hausdorff, and
a continuous surjection compact → Hausdorff is a quotient map. -/
theorem continuous_torusPeriodization {M : Matrix (Fin d) (Fin d) ℝ}
    (hM : M.PosDef) : Continuous (torusPeriodization M) := by
  have hIcc : IsCompact (Set.Icc (0 : Fin d → ℝ) 1) := isCompact_Icc
  haveI : CompactSpace (Set.Icc (0 : Fin d → ℝ) 1) :=
    isCompact_iff_compactSpace.mp hIcc
  set q : Set.Icc (0 : Fin d → ℝ) 1 → UnitAddTorus (Fin d) :=
    (fun p => torusMk p.val) with hq
  have hq_cont : Continuous q := continuous_torusMk.comp continuous_subtype_val
  have hq_surj : Function.Surjective q := by
    intro z
    obtain ⟨x, hx_mem, hx_mk⟩ := torusMk_surjOn_cube z
    exact ⟨⟨x, hx_mem⟩, hx_mk⟩
  have hq_quot : IsQuotientMap q :=
    hq_cont.isClosedMap.isQuotientMap hq_cont hq_surj
  rw [hq_quot.continuous_iff]
  show Continuous ((torusPeriodization M) ∘ q)
  have : (torusPeriodization M) ∘ q
      = (periodization M) ∘ (Subtype.val : Set.Icc (0 : Fin d → ℝ) 1 → _) := by
    funext p
    exact torusPeriodization_mk M p.val
  rw [this]
  exact (continuous_periodization hM).comp continuous_subtype_val

end Torus

/-! ## The periodization bridge

The multivariate analogue of `Real.fourierCoeff_tsum_comp_add`: the
`m`-th torus Fourier coefficient of the periodized Gaussian equals the
Euclidean Fourier integral of the Gaussian at `m`. The proof tiles
`ℝ^d` by integer translates of the half-open unit cube, transfers the
torus integral to the cube through the coordinatewise quotient map
(measure-preserving by `measurePreserving_pi`), swaps sum and integral
by norm-summability, and reassembles the translated cube integrals into
the full Euclidean integral. -/

section Bridge

open MeasureTheory UnitAddTorus Topology

variable {M : Matrix (Fin d) (Fin d) ℝ}

/-- The half-open unit cube `(0, 1]^d`, a strict fundamental domain for
the `ℤ^d`-translation action. -/
def unitCubeIoc (d : ℕ) : Set (Fin d → ℝ) :=
  Set.univ.pi fun _ => Set.Ioc (0 : ℝ) 1

lemma measurableSet_unitCubeIoc :
    MeasurableSet (unitCubeIoc d) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

/-- The lattice cell at `n : ℤ^d`: the unit cube translated by `n`. -/
def latticeCell (n : Fin d → ℤ) : Set (Fin d → ℝ) :=
  Set.univ.pi fun i => Set.Ioc (n i : ℝ) ((n i : ℝ) + 1)

lemma measurableSet_latticeCell (n : Fin d → ℤ) :
    MeasurableSet (latticeCell n) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

lemma latticeCell_eq_image (n : Fin d → ℤ) :
    latticeCell n = (fun x => x + fun i => (n i : ℝ)) '' unitCubeIoc d := by
  ext x
  constructor
  · intro hx
    refine ⟨x - fun i => (n i : ℝ), fun i _ => ?_, by funext i; simp⟩
    have := hx i (Set.mem_univ i)
    simp only [Set.mem_Ioc] at this ⊢
    constructor
    · simpa [Pi.sub_apply] using sub_pos.mpr this.1
    · simp only [Pi.sub_apply]
      linarith [this.2]
  · rintro ⟨y, hy, rfl⟩
    intro i _
    have := hy i (Set.mem_univ i)
    simp only [Set.mem_Ioc] at this ⊢
    constructor
    · simp only [Pi.add_apply]
      linarith [this.1]
    · simp only [Pi.add_apply]
      linarith [this.2]

lemma pairwise_disjoint_latticeCell :
    Pairwise (Function.onFun Disjoint (latticeCell (d := d))) := by
  intro n n' hne
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  have h1 := hx i (Set.mem_univ i)
  have h2 := hx' i (Set.mem_univ i)
  simp only [Set.mem_Ioc] at h1 h2
  rcases lt_or_gt_of_ne hi with h | h
  · have : (n i : ℝ) + 1 ≤ (n' i : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr h
    linarith [h1.2, h2.1]
  · have : (n' i : ℝ) + 1 ≤ (n i : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr h
    linarith [h2.2, h1.1]

lemma iUnion_latticeCell : (⋃ n : Fin d → ℤ, latticeCell n) = Set.univ := by
  refine Set.eq_univ_of_forall (fun x => ?_)
  refine Set.mem_iUnion.mpr ⟨fun i => ⌈x i⌉ - 1, fun i _ => ?_⟩
  simp only [Set.mem_Ioc]
  constructor
  · push_cast
    linarith [Int.ceil_lt_add_one (x i)]
  · push_cast
    linarith [Int.le_ceil (x i)]

/-- The quotient map `torusMk` is measure preserving from the restricted
Lebesgue measure on the half-open cube to the (pi-Haar) volume on the
torus. -/
theorem measurePreserving_torusMk :
    MeasurePreserving (torusMk (d := d))
      ((volume : Measure (Fin d → ℝ)).restrict (unitCubeIoc d))
      (Measure.pi fun _ => AddCircle.haarAddCircle) := by
  have hone : ∀ i : Fin d, MeasurePreserving ((↑) : ℝ → UnitAddCircle)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) AddCircle.haarAddCircle := by
    intro i
    have h := AddCircle.measurePreserving_mk (T := 1) 0
    rw [show (0 : ℝ) + 1 = 1 by norm_num] at h
    have hvol : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
      rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
    rwa [hvol] at h
  have h := measurePreserving_pi (fun _ : Fin d => volume.restrict (Set.Ioc (0 : ℝ) 1))
    (fun _ => AddCircle.haarAddCircle) hone
  have hrestr : (Measure.pi fun _ : Fin d => volume.restrict (Set.Ioc (0 : ℝ) 1))
      = (volume : Measure (Fin d → ℝ)).restrict (unitCubeIoc d) := by
    rw [MeasureTheory.volume_pi, unitCubeIoc, Measure.restrict_pi_pi]
  rwa [hrestr] at h

/-- The full character-times-Gaussian integrand on `ℝ^d`. -/
private noncomputable def charGauss (M : Matrix (Fin d) (Fin d) ℝ) (m : Fin d → ℤ)
    (x : Fin d → ℝ) : ℂ :=
  mFourier (-m) (torusMk x) • (gaussian M x : ℂ)

private lemma continuous_charGauss (m : Fin d → ℤ) :
    Continuous (charGauss M m) :=
  ((mFourier (-m)).continuous.comp continuous_torusMk).smul
    (Complex.continuous_ofReal.comp (continuous_gaussian M))

/-- The character has pointwise norm at most 1. -/
private lemma norm_charGauss_le (m : Fin d → ℤ) (x : Fin d → ℝ) :
    ‖charGauss M m x‖ ≤ gaussian M x := by
  rw [charGauss, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (gaussian_pos M x)]
  calc ‖mFourier (-m) (torusMk x)‖ * gaussian M x
      ≤ ‖mFourier (-m)‖ * gaussian M x := by
        apply mul_le_mul_of_nonneg_right
          ((mFourier (-m)).norm_coe_le_norm (torusMk x)) (gaussian_pos M x).le
    _ = gaussian M x := by rw [mFourier_norm, one_mul]

/-- Integrability of the Gaussian (hence of `charGauss`) on `ℝ^d`, by
comparison with a product of scalar Gaussians. -/
private lemma integrable_charGauss (hM : M.PosDef) (m : Fin d → ℤ) :
    Integrable (charGauss M m) (volume : Measure (Fin d → ℝ)) := by
  obtain ⟨c, hc, hcoer⟩ := hM.exists_coercivity
  have hprod : Integrable
      (fun x : Fin d → ℝ => ∏ i, Real.exp (-(Real.pi * c) * (x i) ^ 2))
      (volume : Measure (Fin d → ℝ)) := by
    rw [MeasureTheory.volume_pi]
    exact Integrable.fintype_prod
      (f := fun _ (t : ℝ) => Real.exp (-(Real.pi * c) * t ^ 2))
      (fun i => integrable_exp_neg_mul_sq (mul_pos Real.pi_pos hc))
  refine hprod.mono' (continuous_charGauss m).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  refine (norm_charGauss_le m x).trans ?_
  calc gaussian M x
      ≤ Real.exp (-Real.pi * (c * ∑ i, (x i) ^ 2)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hcoer x, Real.pi_pos]
    _ = ∏ i, Real.exp (-(Real.pi * c) * (x i) ^ 2) := by
        rw [← Real.exp_sum]
        congr 1
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- The character is invariant under integer translation of the lift. -/
private lemma charGauss_shift (m n : Fin d → ℤ) (x : Fin d → ℝ) :
    mFourier (-m) (torusMk x) • (gaussian M (x + fun i => (n i : ℝ)) : ℂ)
      = charGauss M m (x + fun i => (n i : ℝ)) := by
  rw [charGauss]
  congr 2
  refine (torusMk_eq_iff.mpr fun i => ⟨n i, ?_⟩).symm
  simp

/-- **The periodization bridge**: the `m`-th torus Fourier coefficient
of the descended periodization is the Euclidean integral of the
character against the Gaussian. Multivariate analogue of
`Real.fourierCoeff_tsum_comp_add`, scope-cut to the Gaussian family. -/
theorem mFourierCoeff_torusPeriodization (hM : M.PosDef) (m : Fin d → ℤ) :
    mFourierCoeff (fun z => (torusPeriodization M z : ℂ)) m
      = ∫ x : Fin d → ℝ, charGauss M m x := by
  obtain ⟨c, hc, hcoer⟩ := hM.exists_coercivity
  -- the translate family over the cube, with uniform norm control
  set F : (Fin d → ℤ) → (Fin d → ℝ) → ℂ := fun n x =>
    mFourier (-m) (torusMk x) • (gaussian M (x + fun i => (n i : ℝ)) : ℂ)
    with hF
  have hcube_finite : IsFiniteMeasure
      ((volume : Measure (Fin d → ℝ)).restrict (unitCubeIoc d)) := by
    constructor
    rw [Measure.restrict_apply_univ, unitCubeIoc, volume_pi_pi]
    simp [Real.volume_Ioc]
  have hF_cont : ∀ n, Continuous (F n) := fun n =>
    ((mFourier (-m)).continuous.comp continuous_torusMk).smul
      (Complex.continuous_ofReal.comp
        ((continuous_gaussian M).comp (continuous_id.add continuous_const)))
  have hF_bound : ∀ n x, x ∈ unitCubeIoc d → ‖F n x‖ ≤
      Real.exp (Real.pi * c * d * 1 ^ 2) *
        ∏ i, Real.exp (-(Real.pi * c / 2) * (n i : ℝ) ^ 2) := by
    intro n x hx
    have hxB : ∀ i, |x i| ≤ 1 := by
      intro i
      have := hx i (Set.mem_univ i)
      simp only [Set.mem_Ioc] at this
      rw [abs_le]
      constructor <;> linarith [this.1, this.2]
    calc ‖F n x‖ = ‖mFourier (-m) (torusMk x)‖ * gaussian M (x + fun i => (n i : ℝ)) := by
          rw [hF, norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (gaussian_pos M _)]
      _ ≤ 1 * gaussian M (x + fun i => (n i : ℝ)) := by
          apply mul_le_mul_of_nonneg_right ?_ (gaussian_pos M _).le
          calc ‖mFourier (-m) (torusMk x)‖
              ≤ ‖mFourier (-m)‖ := (mFourier (-m)).norm_coe_le_norm (torusMk x)
            _ = 1 := mFourier_norm
      _ = gaussian M (x + fun i => (n i : ℝ)) := one_mul _
      _ ≤ _ := gaussian_translate_le hc hcoer hxB n
  have hF_int : ∀ n, Integrable (F n)
      ((volume : Measure (Fin d → ℝ)).restrict (unitCubeIoc d)) := by
    intro n
    refine Integrable.mono'
      (g := fun _ => Real.exp (Real.pi * c * d * 1 ^ 2) *
        ∏ i, Real.exp (-(Real.pi * c / 2) * (n i : ℝ) ^ 2))
      (integrable_const _) (hF_cont n).aestronglyMeasurable ?_
    exact (MeasureTheory.ae_restrict_iff' measurableSet_unitCubeIoc).mpr
      (Filter.Eventually.of_forall (fun x hx => hF_bound n x hx))
  have hF_norm_sum : Summable (fun n : Fin d → ℤ =>
      ∫ x, ‖F n x‖ ∂((volume : Measure (Fin d → ℝ)).restrict (unitCubeIoc d))) := by
    refine Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun x => norm_nonneg _) (fun n => ?_)
      ((summable_translate_weights c 1 hc).mul_left
        ((volume : Measure (Fin d → ℝ)).restrict (unitCubeIoc d) Set.univ).toReal)
    calc ∫ x, ‖F n x‖ ∂((volume : Measure (Fin d → ℝ)).restrict (unitCubeIoc d))
        ≤ ∫ _, (Real.exp (Real.pi * c * d * 1 ^ 2) *
            ∏ i, Real.exp (-(Real.pi * c / 2) * (n i : ℝ) ^ 2))
            ∂((volume : Measure (Fin d → ℝ)).restrict (unitCubeIoc d)) := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun x => norm_nonneg _)
            (integrable_const _) ?_
          exact (MeasureTheory.ae_restrict_iff' measurableSet_unitCubeIoc).mpr
            (Filter.Eventually.of_forall (fun x hx => hF_bound n x hx))
      _ = ((volume : Measure (Fin d → ℝ)).restrict (unitCubeIoc d) Set.univ).toReal
            * (Real.exp (Real.pi * c * d * 1 ^ 2) *
              ∏ i, Real.exp (-(Real.pi * c / 2) * (n i : ℝ) ^ 2)) := by
          rw [integral_const, smul_eq_mul]
          rfl
  -- Step 1: the coefficient as an integral over the cube.
  have step1 : mFourierCoeff (fun z => (torusPeriodization M z : ℂ)) m
      = ∫ x in unitCubeIoc d,
          mFourier (-m) (torusMk x) • ((periodization M x : ℝ) : ℂ) := by
    show ∫ z, mFourier (-m) z • ((torusPeriodization M z : ℝ) : ℂ)
          ∂(Measure.pi fun _ => AddCircle.haarAddCircle) = _
    have hcont2 : Continuous (fun z : UnitAddTorus (Fin d) =>
        mFourier (-m) z • ((torusPeriodization M z : ℝ) : ℂ)) :=
      (mFourier (-m)).continuous.smul
        (by exact Complex.continuous_ofReal.comp (continuous_torusPeriodization hM))
    rw [← measurePreserving_torusMk.map_eq,
      integral_map continuous_torusMk.aemeasurable hcont2.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [torusPeriodization_mk])
  -- Step 2: expand the periodization and swap sum and integral.
  have hintegrand : ∀ x : Fin d → ℝ,
      mFourier (-m) (torusMk x) • ((periodization M x : ℝ) : ℂ)
        = ∑' n : Fin d → ℤ, F n x := by
    intro x
    rw [periodization, Complex.ofReal_tsum, smul_eq_mul, ← tsum_mul_left]
    rfl
  have step2 : ∫ x in unitCubeIoc d,
        mFourier (-m) (torusMk x) • ((periodization M x : ℝ) : ℂ)
      = ∑' n : Fin d → ℤ, ∫ x in unitCubeIoc d, F n x :=
    calc ∫ x in unitCubeIoc d,
          mFourier (-m) (torusMk x) • ((periodization M x : ℝ) : ℂ)
        = ∫ x in unitCubeIoc d, ∑' n : Fin d → ℤ, F n x :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => hintegrand x)
      _ = ∑' n : Fin d → ℤ, ∫ x in unitCubeIoc d, F n x :=
          (integral_tsum_of_summable_integral_norm hF_int hF_norm_sum).symm
  -- Step 3: translate each term to its lattice cell and reassemble.
  have step3 : ∑' n : Fin d → ℤ, ∫ x in unitCubeIoc d, F n x
      = ∫ x : Fin d → ℝ, charGauss M m x := by
    have htrans : ∀ n : Fin d → ℤ, ∫ x in unitCubeIoc d, F n x
        = ∫ y in latticeCell n, charGauss M m y := by
      intro n
      rw [latticeCell_eq_image]
      rw [MeasurePreserving.setIntegral_image_emb
        (measurePreserving_add_right volume (fun i => (n i : ℝ)))
        (MeasurableEquiv.addRight (fun i => (n i : ℝ))).measurableEmbedding
        (charGauss M m) (unitCubeIoc d)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
        charGauss_shift m n x)
    simp_rw [htrans]
    have := (hasSum_integral_iUnion measurableSet_latticeCell
      pairwise_disjoint_latticeCell
      ((integrable_charGauss hM m).integrableOn.mono_set
        (Set.subset_univ _))).tsum_eq
    rw [this, iUnion_latticeCell, setIntegral_univ]
  rw [step1, step2, step3]

end Bridge

/-! ## The multivariate Gaussian Fourier transform

`∫ exp(-2πi⟨m,x⟩)·exp(-π xᵀMx) dx = (det M)^(-1/2)·exp(-π mᵀM⁻¹m)`,
by spectral rotation. Diagonalization is legitimate here — on the
*integral* side — because Lebesgue measure on `ℝ^d` transforms by
`|det|` under any invertible linear map, and the eigenvector rotation
has `|det| = 1`. The lattice sum never sees the rotation; that is the
bridge's job. -/

section GaussFT

open MeasureTheory Complex UnitAddTorus

variable {M : Matrix (Fin d) (Fin d) ℝ}

/-- Over `ℝ`, the star of a matrix is its transpose. -/
private lemma star_eq_transpose (U : Matrix (Fin d) (Fin d) ℝ) :
    star U = Uᵀ := by
  ext i j
  rw [Matrix.star_apply, Matrix.transpose_apply, star_trivial]

/-- Closed form of the character: the torus monomial at a lift is the
plane-wave exponential. -/
private lemma charGauss_closed (m : Fin d → ℤ) (x : Fin d → ℝ) :
    charGauss M m x
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I)
          * ((∑ i, (m i : ℝ) * x i : ℝ) : ℂ)) * ((gaussian M x : ℝ) : ℂ) := by
  rw [charGauss, smul_eq_mul]
  congr 1
  show (∏ i, fourier ((-m) i) (torusMk x i)) = _
  have hfac : ∀ i : Fin d, fourier ((-m) i) (torusMk x i)
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((m i : ℝ) * x i : ℝ)) := by
    intro i
    show fourier ((-m) i) ((x i : ℝ) : UnitAddCircle) = _
    rw [Pi.neg_apply, fourier_coe_apply]
    congr 1
    push_cast
    try ring
  rw [Finset.prod_congr rfl (fun i _ => hfac i), ← Complex.exp_sum]
  congr 1
  rw [Complex.ofReal_sum, Finset.mul_sum]

/-- One-dimensional building block, shaped for the product
factorization: `∫ e^(-2πi·v·t)·e^(-π·a·t²) dt = (a⁻¹)^(1/2)·e^(-π·v²/a)`
for `a > 0`. Instance of `fourierIntegral_gaussian`. -/
private lemma oneDim_gaussian_fourier (v a : ℝ) (ha : 0 < a) :
    ∫ t : ℝ, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((v * t : ℝ) : ℂ))
        * ((Real.exp (-Real.pi * a * t ^ 2) : ℝ) : ℂ)
      = ((a⁻¹ : ℝ) : ℂ) ^ ((1 : ℂ) / 2)
        * Complex.exp (((-Real.pi * v ^ 2 / a : ℝ) : ℂ)) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
  have hb : (0 : ℝ) < ((Real.pi * a : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    exact mul_pos Real.pi_pos ha
  have h := fourierIntegral_gaussian (b := ((Real.pi * a : ℝ) : ℂ)) hb
    (t := ((-2 * Real.pi * v : ℝ) : ℂ))
  calc ∫ t : ℝ, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((v * t : ℝ) : ℂ))
          * ((Real.exp (-Real.pi * a * t ^ 2) : ℝ) : ℂ)
      = ∫ x : ℝ, Complex.exp (Complex.I * ((-2 * Real.pi * v : ℝ) : ℂ) * (x : ℂ))
          * Complex.exp (-((Real.pi * a : ℝ) : ℂ) * (x : ℂ) ^ 2) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        have e1 : (-(2 * (Real.pi : ℂ) * Complex.I) * ((v * t : ℝ) : ℂ))
            = Complex.I * ((-2 * Real.pi * v : ℝ) : ℂ) * (t : ℂ) := by
          push_cast
          ring
        have e2 : (((-Real.pi * a * t ^ 2 : ℝ) : ℝ) : ℂ)
            = -((Real.pi * a : ℝ) : ℂ) * (t : ℂ) ^ 2 := by
          push_cast
          ring
        simp only [Complex.ofReal_exp, e1, e2]
    _ = ((Real.pi : ℂ) / ((Real.pi * a : ℝ) : ℂ)) ^ ((1 : ℂ) / 2)
          * Complex.exp (-((-2 * Real.pi * v : ℝ) : ℂ) ^ 2 / (4 * ((Real.pi * a : ℝ) : ℂ))) := h
    _ = ((a⁻¹ : ℝ) : ℂ) ^ ((1 : ℂ) / 2)
          * Complex.exp (((-Real.pi * v ^ 2 / a : ℝ) : ℂ)) := by
        have hbase : ((Real.pi : ℂ) / ((Real.pi * a : ℝ) : ℂ)) = ((a⁻¹ : ℝ) : ℂ) := by
          push_cast
          field_simp
        have hexp : -((-2 * Real.pi * v : ℝ) : ℂ) ^ 2 / (4 * ((Real.pi * a : ℝ) : ℂ))
            = (((-Real.pi * v ^ 2 / a : ℝ)) : ℂ) := by
          push_cast
          field_simp
          try ring
        rw [hbase, hexp]


/-- **The multivariate Gaussian Fourier transform**:
`∫ e^(-2πi⟨m,x⟩)·e^(-π·xᵀMx) dx = (det M)^(-1/2)·e^(-π·mᵀM⁻¹m)` for
`M` positive definite. Proved by rotating the integral into the
eigenbasis (measure-preserving, `|det| = 1`), factoring into
one-dimensional Gaussians, and reassembling. -/
theorem integral_charGauss_eq (hM : M.PosDef) (m : Fin d → ℤ) :
    ∫ x : Fin d → ℝ, charGauss M m x
      = ((M.det⁻¹ : ℝ) : ℂ) ^ ((1 : ℂ) / 2)
        * Complex.exp (((-Real.pi
            * (∑ i, ∑ j, M⁻¹ i j * (m i : ℝ) * (m j : ℝ)) : ℝ) : ℂ)) := by
  have hHerm : M.IsHermitian := hM.1
  set u := IsHermitian.eigenvectorUnitary hHerm with hu
  set U : Matrix (Fin d) (Fin d) ℝ := (u : Matrix (Fin d) (Fin d) ℝ) with hU
  set Dv : Fin d → ℝ := IsHermitian.eigenvalues hHerm with hDv
  have hDpos : ∀ i, 0 < Dv i := fun i => Matrix.PosDef.eigenvalues_pos hM i
  -- spectral decomposition in plain matrix form
  have hspec : M = U * Matrix.diagonal Dv * star U := by
    have h := IsHermitian.spectral_theorem hHerm
    rwa [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id,
      Function.id_comp] at h
  have hstarU : star U * U = 1 := by
    rw [hU, ← Unitary.coe_star]
    exact Unitary.coe_star_mul_self u
  have hUstar : U * star U = 1 := by
    rw [hU, ← Unitary.coe_star]
    exact Unitary.coe_mul_star_self u
  -- determinant of the rotation
  have hdet2 : U.det * U.det = 1 := by
    have h1 : (star U * U).det = 1 := by rw [hstarU, Matrix.det_one]
    rwa [Matrix.det_mul, star_eq_transpose, Matrix.det_transpose] at h1
  have hdetU_ne : U.det ≠ 0 := by
    intro h
    rw [h, mul_zero] at hdet2
    exact zero_ne_one hdet2
  have habs : |U.det| = 1 := by
    rcases mul_self_eq_one_iff.mp hdet2 with h | h <;> simp [h]
  -- the rotation is measure preserving
  have hcontU : Continuous (fun y : Fin d → ℝ => U.mulVec y) := by
    refine continuous_pi (fun i => ?_)
    show Continuous fun y : Fin d → ℝ => ∑ j, U i j * y j
    exact continuous_finset_sum _ (fun j _ => continuous_const.mul (continuous_apply j))
  have hmapU : Measure.map (fun y : Fin d → ℝ => U.mulVec y)
      (volume : Measure (Fin d → ℝ)) = volume := by
    have h := Real.map_matrix_volume_pi_eq_smul_volume_pi (M := U) hdetU_ne
    rw [show ⇑(Matrix.toLin' U) = fun y => U.mulVec y from
      funext fun y => Matrix.toLin'_apply U y] at h
    rw [h, abs_inv, habs]
    simp
  have hmpU : MeasureTheory.MeasurePreserving (fun y : Fin d → ℝ => U.mulVec y)
      volume volume := ⟨hcontU.measurable, hmapU⟩
  -- rotate the integral
  have hrot : ∫ x : Fin d → ℝ, charGauss M m x
      = ∫ y : Fin d → ℝ, charGauss M m (U.mulVec y) := by
    rw [← hmpU.map_eq,
      MeasureTheory.integral_map hmpU.measurable.aemeasurable
        (continuous_charGauss m).aestronglyMeasurable, hmpU.map_eq]
  -- the rotated frequency vector
  set mv : Fin d → ℝ := fun i => (m i : ℝ) with hmv
  set v : Fin d → ℝ := Matrix.vecMul mv U with hv
  -- rotated quadratic form is diagonal
  have hquadrot : ∀ y : Fin d → ℝ,
      (U.mulVec y) ⬝ᵥ M.mulVec (U.mulVec y) = ∑ i, Dv i * (y i) ^ 2 := by
    intro y
    calc (U.mulVec y) ⬝ᵥ M.mulVec (U.mulVec y)
        = (U.mulVec y) ⬝ᵥ (M * U).mulVec y := by rw [← Matrix.mulVec_mulVec]
      _ = (U.mulVec y) ⬝ᵥ (U * Matrix.diagonal Dv).mulVec y := by
          rw [hspec, Matrix.mul_assoc (U * Matrix.diagonal Dv) (star U) U,
            hstarU, Matrix.mul_one]
      _ = (Matrix.vecMul (U.mulVec y) (U * Matrix.diagonal Dv)) ⬝ᵥ y :=
          Matrix.dotProduct_mulVec _ _ _
      _ = (Matrix.vecMul (Matrix.vecMul y Uᵀ) (U * Matrix.diagonal Dv)) ⬝ᵥ y := by
          rw [Matrix.vecMul_transpose]
      _ = (Matrix.vecMul y (Uᵀ * (U * Matrix.diagonal Dv))) ⬝ᵥ y := by
          rw [Matrix.vecMul_vecMul]
      _ = (Matrix.vecMul y (Matrix.diagonal Dv)) ⬝ᵥ y := by
          rw [← Matrix.mul_assoc, ← star_eq_transpose, hstarU, Matrix.one_mul]
      _ = ∑ i, Dv i * (y i) ^ 2 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Matrix.vecMul_diagonal]
          ring
  -- rotated character is the rotated frequency pairing
  have hcharrot : ∀ y : Fin d → ℝ,
      (∑ i, (m i : ℝ) * (U.mulVec y) i) = ∑ i, v i * y i := by
    intro y
    show mv ⬝ᵥ (U.mulVec y) = v ⬝ᵥ y
    rw [Matrix.dotProduct_mulVec]
  -- pointwise product form of the rotated integrand
  have hpoint : ∀ y : Fin d → ℝ, charGauss M m (U.mulVec y)
      = ∏ i, (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((v i * y i : ℝ) : ℂ))
          * ((Real.exp (-Real.pi * Dv i * (y i) ^ 2) : ℝ) : ℂ)) := by
    intro y
    rw [charGauss_closed, hcharrot y]
    have hgauss : gaussian M (U.mulVec y)
        = ∏ i, Real.exp (-Real.pi * Dv i * (y i) ^ 2) := by
      show Real.exp (-Real.pi * ((U.mulVec y) ⬝ᵥ M.mulVec (U.mulVec y))) = _
      rw [hquadrot y, ← Real.exp_sum]
      congr 1
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hgauss, Finset.prod_mul_distrib]
    congr 1
    · rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
    · rw [Complex.ofReal_prod]
  -- factor the integral coordinatewise and evaluate each factor
  have hfactor : ∫ y : Fin d → ℝ, charGauss M m (U.mulVec y)
      = ∏ i, (((Dv i)⁻¹ : ℝ) : ℂ) ^ ((1 : ℂ) / 2)
          * Complex.exp (((-Real.pi * (v i) ^ 2 / Dv i : ℝ) : ℂ)) := by
    calc ∫ y : Fin d → ℝ, charGauss M m (U.mulVec y)
        = ∫ y : Fin d → ℝ, ∏ i,
            (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((v i * y i : ℝ) : ℂ))
              * ((Real.exp (-Real.pi * Dv i * (y i) ^ 2) : ℝ) : ℂ)) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = ∏ i, ∫ t : ℝ,
            (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((v i * t : ℝ) : ℂ))
              * ((Real.exp (-Real.pi * Dv i * t ^ 2) : ℝ) : ℂ)) :=
          MeasureTheory.integral_fintype_prod_volume_eq_prod
            (f := fun i (t : ℝ) =>
              Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((v i * t : ℝ) : ℂ))
                * ((Real.exp (-Real.pi * Dv i * t ^ 2) : ℝ) : ℂ))
      _ = ∏ i, (((Dv i)⁻¹ : ℝ) : ℂ) ^ ((1 : ℂ) / 2)
            * Complex.exp (((-Real.pi * (v i) ^ 2 / Dv i : ℝ) : ℂ)) :=
          Finset.prod_congr rfl (fun i _ =>
            oneDim_gaussian_fourier (v i) (Dv i) (hDpos i))
  -- the inverse Gram form in the eigenbasis
  have hMinv : M⁻¹ = U * Matrix.diagonal (fun i => (Dv i)⁻¹) * star U := by
    apply Matrix.inv_eq_right_inv
    calc M * (U * Matrix.diagonal (fun i => (Dv i)⁻¹) * star U)
        = (U * Matrix.diagonal Dv * star U)
            * (U * Matrix.diagonal (fun i => (Dv i)⁻¹) * star U) := by rw [← hspec]
      _ = U * Matrix.diagonal Dv * (star U * U)
            * Matrix.diagonal (fun i => (Dv i)⁻¹) * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal Dv * Matrix.diagonal (fun i => (Dv i)⁻¹)) * star U := by
          rw [hstarU]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = U * star U := by
          rw [Matrix.diagonal_mul_diagonal]
          have : (fun i => Dv i * (Dv i)⁻¹) = fun _ => (1 : ℝ) :=
            funext fun i => mul_inv_cancel₀ (ne_of_gt (hDpos i))
          rw [this, Matrix.diagonal_one, Matrix.mul_one]
      _ = 1 := hUstar
  -- the quadratic form of the inverse at the frequency vector
  have hquadinv : ∑ i, ∑ j, M⁻¹ i j * mv i * mv j = ∑ i, (v i) ^ 2 / Dv i := by
    have hdot : ∑ i, ∑ j, M⁻¹ i j * mv i * mv j = mv ⬝ᵥ M⁻¹.mulVec mv := by
      show ∑ i, ∑ j, M⁻¹ i j * mv i * mv j = ∑ i, mv i * ∑ j, M⁻¹ i j * mv j
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hdot, hMinv]
    calc mv ⬝ᵥ (U * Matrix.diagonal (fun i => (Dv i)⁻¹) * star U).mulVec mv
        = mv ⬝ᵥ (U * Matrix.diagonal (fun i => (Dv i)⁻¹)).mulVec ((star U).mulVec mv) := by
          rw [Matrix.mulVec_mulVec]
      _ = mv ⬝ᵥ (U * Matrix.diagonal (fun i => (Dv i)⁻¹)).mulVec v := by
          rw [star_eq_transpose, Matrix.mulVec_transpose]
      _ = (Matrix.vecMul mv (U * Matrix.diagonal (fun i => (Dv i)⁻¹))) ⬝ᵥ v :=
          Matrix.dotProduct_mulVec _ _ _
      _ = (Matrix.vecMul v (Matrix.diagonal (fun i => (Dv i)⁻¹))) ⬝ᵥ v := by
          rw [← Matrix.vecMul_vecMul]
      _ = ∑ i, (v i) ^ 2 / Dv i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Matrix.vecMul_diagonal]
          field_simp
          try ring
  -- determinant via the eigenvalues
  have hdet : M.det = ∏ i, Dv i := by
    have h := IsHermitian.det_eq_prod_eigenvalues hHerm
    simpa using h
  -- assemble
  rw [hrot, hfactor, Finset.prod_mul_distrib]
  congr 1
  · rw [QuadraticAction.prod_cpow_half d (fun i => (Dv i)⁻¹)
      (fun i => (inv_nonneg).mpr (hDpos i).le)]
    congr 2
    rw [hdet]
    simp [Finset.prod_inv_distrib]
  · rw [← Complex.exp_sum]
    congr 1
    rw [← Complex.ofReal_sum]
    congr 1
    rw [hquadinv, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)

end GaussFT

/-! ## Poisson summation and the general Siegel–Poisson duality -/

section Poisson

open MeasureTheory Complex UnitAddTorus

variable {M : Matrix (Fin d) (Fin d) ℝ}

/-- The double-sum quadratic form is the `dotProduct`/`mulVec` form. -/
lemma quadForm_dotProduct (Q : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    ∑ i, ∑ j, Q i j * x i * x j = x ⬝ᵥ Q.mulVec x := by
  show ∑ i, ∑ j, Q i j * x i * x j = ∑ i, x i * ∑ j, Q i j * x j
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- Positive scalar multiples of positive-definite matrices are positive
definite. Hand-rolled: `Matrix.PosDef.smul` needs `StarOrderedRing ℝ`
synthesis, which fails at this pin. -/
lemma posDef_smul' {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef)
    {c : ℝ} (hc : 0 < c) : (c • A).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · show (c • A)ᴴ = c • A
    rw [Matrix.conjTranspose_smul, star_trivial]
    congr 1
    exact (posDef_iff_dotProduct_mulVec.mp hA).1
  · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_pos hc ((posDef_iff_dotProduct_mulVec.mp hA).2 hx)

/-- The inverse of a positive-definite matrix is positive definite. -/
lemma posDef_inv {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef) :
    (A⁻¹).PosDef := by
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · show A⁻¹ᴴ = A⁻¹
    rw [Matrix.conjTranspose_nonsing_inv]
    congr 1
    exact (posDef_iff_dotProduct_mulVec.mp hA).1
  · set y : Fin d → ℝ := A⁻¹.mulVec x with hy
    have hAy : A.mulVec y = x := by
      rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    have hyne : y ≠ 0 := by
      intro h0
      apply hx
      rw [← hAy, h0, Matrix.mulVec_zero]
    have hstar : star x = x := funext fun i => star_trivial _
    rw [hstar, ← hAy, dotProduct_comm]
    have h := (posDef_iff_dotProduct_mulVec.mp hA).2 hyne
    have hstary : star y = y := funext fun i => star_trivial _
    rwa [hstary] at h

/-- **Multivariate Poisson summation for the Gaussian family**: the
lattice sum of `exp(-π·xᵀMx)` equals the lattice sum of its Fourier
transform. The theorem Mathlib does not yet have, at the generality
Meno needs. -/
theorem tsum_gaussian_eq (hM : M.PosDef) :
    (∑' n : Fin d → ℤ, ((gaussian M (fun i => (n i : ℝ)) : ℝ) : ℂ))
      = ∑' m : Fin d → ℤ,
          ((M.det⁻¹ : ℝ) : ℂ) ^ ((1 : ℂ) / 2)
            * Complex.exp (((-Real.pi
                * (∑ i, ∑ j, M⁻¹ i j * (m i : ℝ) * (m j : ℝ)) : ℝ) : ℂ)) := by
  set G : C(UnitAddTorus (Fin d), ℂ) :=
    ⟨fun z => ((torusPeriodization M z : ℝ) : ℂ),
      Complex.continuous_ofReal.comp (continuous_torusPeriodization hM)⟩ with hGdef
  have hcoeff : ∀ m : Fin d → ℤ, mFourierCoeff (⇑G) m
      = ((M.det⁻¹ : ℝ) : ℂ) ^ ((1 : ℂ) / 2)
          * Complex.exp (((-Real.pi
              * (∑ i, ∑ j, M⁻¹ i j * (m i : ℝ) * (m j : ℝ)) : ℝ) : ℂ)) := by
    intro m
    have h1 : mFourierCoeff (⇑G) m
        = mFourierCoeff (fun z => ((torusPeriodization M z : ℝ) : ℂ)) m := rfl
    rw [h1, mFourierCoeff_torusPeriodization hM m, integral_charGauss_eq hM m]
  have hMinv_pos : (Real.pi • M⁻¹).PosDef :=
    posDef_smul' (posDef_inv hM) Real.pi_pos
  have hsummable : Summable (mFourierCoeff (⇑G)) := by
    refine Summable.congr ?_ (fun m => (hcoeff m).symm)
    refine Summable.mul_left _ ?_
    refine Summable.of_norm ?_
    have hnorm : ∀ m : Fin d → ℤ,
        ‖Complex.exp (((-Real.pi
            * (∑ i, ∑ j, M⁻¹ i j * (m i : ℝ) * (m j : ℝ)) : ℝ) : ℂ))‖
          = Real.exp (-(∑ i, ∑ j, (Real.pi • M⁻¹) i j * (m i : ℝ) * (m j : ℝ))) := by
      intro m
      rw [← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      congr 1
      rw [neg_mul, neg_inj, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Matrix.smul_apply, smul_eq_mul]
      ring
    exact (summable_exp_neg_quadForm hMinv_pos).congr (fun m => (hnorm m).symm)
  have h0 := (hasSum_mFourier_series_apply_of_summable hsummable
    (torusMk (fun _ : Fin d => (0 : ℝ)))).tsum_eq
  have hone : ∀ m : Fin d → ℤ,
      mFourier m (torusMk (fun _ : Fin d => (0 : ℝ))) = 1 := by
    intro m
    show (∏ i, fourier (m i) (torusMk (fun _ : Fin d => (0 : ℝ)) i)) = 1
    have : ∀ i : Fin d, torusMk (fun _ : Fin d => (0 : ℝ)) i = 0 := by
      intro i
      show (((0 : ℝ)) : UnitAddCircle) = 0
      exact QuotientAddGroup.mk_zero _
    rw [Finset.prod_congr rfl (fun i _ => by rw [this i, fourier_eval_zero])]
    exact Finset.prod_const_one
  have hG0 : G (torusMk (fun _ : Fin d => (0 : ℝ)))
      = ∑' n : Fin d → ℤ, ((gaussian M (fun i => (n i : ℝ)) : ℝ) : ℂ) := by
    show ((torusPeriodization M (torusMk (fun _ : Fin d => (0 : ℝ))) : ℝ) : ℂ) = _
    rw [torusPeriodization_mk, periodization, Complex.ofReal_tsum]
    refine tsum_congr (fun n => ?_)
    congr 2
    funext i
    simp
  rw [← hG0]
  rw [← h0]
  refine tsum_congr (fun m => ?_)
  rw [hone m, smul_eq_mul, mul_one, hcoeff m]

end Poisson

/-! ## The general dual and the Siegel–Poisson duality -/

section Duality

open Complex

/-- The **general dual** of a quadratic action: `Q ↦ π²·Q⁻¹`.
Symmetry, positive-definiteness, and summability are all derived —
no fields need to be supplied. This is the plan's Phase 2 target
construction at full (non-diagonal) generality. -/
noncomputable def QuadraticAction.dual {r : ℕ} (A : QuadraticAction r) :
    QuadraticAction r :=
  QuadraticAction.of_posDef (Real.pi ^ 2 • A.Q⁻¹)
    (by
      show (Real.pi ^ 2 • A.Q⁻¹)ᵀ = Real.pi ^ 2 • A.Q⁻¹
      rw [Matrix.transpose_smul, Matrix.transpose_nonsing_inv,
        show A.Qᵀ = A.Q from A.Q_symm])
    (posDef_smul' (posDef_inv A.Q_posDef) (by positivity))

@[simp] theorem QuadraticAction.dual_Q {r : ℕ} (A : QuadraticAction r) :
    A.dual.Q = Real.pi ^ 2 • A.Q⁻¹ := rfl

/-- **The general Siegel–Poisson duality**:
`Z(π²·Q⁻¹) = √(det Q / π^r) · Z(Q)` for **every** symmetric
positive-definite Gram form `Q`, at every rank. Closes falsification
clause #3 of PLAN.md in full: the diagonal restriction is gone. -/
theorem QuadraticAction.duality {r : ℕ} (A : QuadraticAction r) :
    (↑(A.dual.toSectorAction.partFn) : ℂ)
      = ↑(A.Q.det / Real.pi ^ r : ℝ) ^ ((1 : ℂ) / 2)
        * ↑(A.toSectorAction.partFn) := by
  have hdet_pos : 0 < A.Q.det := A.Q_posDef.det_pos
  have hdetQ : IsUnit A.Q.det := isUnit_iff_ne_zero.mpr (ne_of_gt hdet_pos)
  -- the Gaussian matrix `M = Q/π` and its inverse `π·Q⁻¹`
  set M : Matrix (Fin r) (Fin r) ℝ := Real.pi⁻¹ • A.Q with hMdef
  have hMpos : M.PosDef := posDef_smul' A.Q_posDef (inv_pos.mpr Real.pi_pos)
  have hMinv : M⁻¹ = Real.pi • A.Q⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [hMdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      inv_mul_cancel₀ Real.pi_ne_zero, one_smul, Matrix.mul_nonsing_inv _ hdetQ]
  have hMdet : M.det⁻¹ = Real.pi ^ r / A.Q.det := by
    rw [hMdef, Matrix.det_smul, Fintype.card_fin, mul_inv, ← inv_pow, inv_inv,
      div_eq_mul_inv]
  -- Poisson summation at `M`
  have hpoisson := tsum_gaussian_eq (d := r) hMpos
  -- left side is `Z(Q)`
  have hL : (∑' n : Fin r → ℤ, ((gaussian M (fun i => (n i : ℝ)) : ℝ) : ℂ))
      = ↑(A.toSectorAction.partFn) := by
    rw [A.partFn_eq, Complex.ofReal_tsum]
    refine tsum_congr (fun n => ?_)
    congr 1
    show Real.exp (-Real.pi * ((fun i => (n i : ℝ)) ⬝ᵥ M.mulVec (fun i => (n i : ℝ)))) = _
    congr 1
    rw [hMdef, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      ← quadForm_dotProduct]
    field_simp
  -- right side is the prefactor times `Z(π²·Q⁻¹)`
  have hR : (∑' m : Fin r → ℤ,
        ((M.det⁻¹ : ℝ) : ℂ) ^ ((1 : ℂ) / 2)
          * Complex.exp (((-Real.pi
              * (∑ i, ∑ j, M⁻¹ i j * (m i : ℝ) * (m j : ℝ)) : ℝ) : ℂ)))
      = ↑(Real.pi ^ r / A.Q.det : ℝ) ^ ((1 : ℂ) / 2)
          * ↑(A.dual.toSectorAction.partFn) := by
    rw [tsum_mul_left, hMdet]
    congr 1
    rw [A.dual.partFn_eq, Complex.ofReal_tsum]
    refine tsum_congr (fun m => ?_)
    rw [← Complex.ofReal_exp]
    congr 1
    rw [hMinv]
    congr 1
    rw [QuadraticAction.dual_Q, quadForm_dotProduct, quadForm_dotProduct,
      Matrix.smul_mulVec, dotProduct_smul, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  rw [hL, hR] at hpoisson
  -- flip the prefactor to the other side
  have ha_pos : (0 : ℝ) < A.Q.det / Real.pi ^ r :=
    div_pos hdet_pos (pow_pos Real.pi_pos r)
  have hb_pos : (0 : ℝ) < Real.pi ^ r / A.Q.det :=
    div_pos (pow_pos Real.pi_pos r) hdet_pos
  calc (↑(A.dual.toSectorAction.partFn) : ℂ)
      = 1 * ↑(A.dual.toSectorAction.partFn) := (one_mul _).symm
    _ = (↑(A.Q.det / Real.pi ^ r : ℝ) ^ ((1 : ℂ) / 2)
          * ↑(Real.pi ^ r / A.Q.det : ℝ) ^ ((1 : ℂ) / 2))
          * ↑(A.dual.toSectorAction.partFn) := by
        congr 1
        rw [← Complex.mul_cpow_ofReal_nonneg ha_pos.le hb_pos.le,
          ← Complex.ofReal_mul,
          show (A.Q.det / Real.pi ^ r) * (Real.pi ^ r / A.Q.det) = 1 by
            field_simp,
          Complex.ofReal_one, Complex.one_cpow]
    _ = ↑(A.Q.det / Real.pi ^ r : ℝ) ^ ((1 : ℂ) / 2)
          * (↑(Real.pi ^ r / A.Q.det : ℝ) ^ ((1 : ℂ) / 2)
            * ↑(A.dual.toSectorAction.partFn)) := by ring
    _ = ↑(A.Q.det / Real.pi ^ r : ℝ) ^ ((1 : ℂ) / 2)
          * ↑(A.toSectorAction.partFn) := by rw [← hpoisson]

/-- Dedup witness: the diagonal-family dual (Phase 14) is the general
dual restricted to diagonal Gram forms. The two dual constructions have
the same Gram matrix, hence the same partition function — so
`ofDiagonal_duality` is now a corollary of `QuadraticAction.duality`. -/
theorem ofDiagonal_dual_partFn_eq {r : ℕ} (α : Fin r → ℝ) (hα : ∀ i, 0 < α i) :
    (QuadraticAction.ofDiagonal (fun i => Real.pi ^ 2 / α i)
        (fun i => div_pos (sq_pos_of_pos Real.pi_pos) (hα i))).toSectorAction.partFn
      = (QuadraticAction.ofDiagonal α hα).dual.toSectorAction.partFn :=
  QuadraticAction.partFn_eq_of_Q_eq _ _ (by
    rw [QuadraticAction.ofDiagonal_dual_Q, QuadraticAction.dual_Q])

end Duality


/-! ## Duality algebra: involution, self-duality, flow

The Phase 2 wishlist, now cheap because `dual` is a first-class
`QuadraticAction`. One plan claim is **falsified** here:
`dualityFlow_zero_iff_selfDual` is false at rank ≥ 2 (zero flow
constrains only the determinant), witnessed by `diag(2π, π/2)`. -/

section DualityAlgebra

open Complex

/-- A quadratic action is determined by its Gram matrix: the proof
fields are propositions. -/
theorem QuadraticAction.eq_of_Q_eq {r : ℕ} {A B : QuadraticAction r}
    (h : A.Q = B.Q) : A = B := by
  obtain ⟨QA, sA, pA, mA⟩ := A
  obtain ⟨QB, sB, pB, mB⟩ := B
  have h' : QA = QB := h
  subst h'
  rfl

/-- Inverse of a nonzero scalar multiple of an invertible matrix. -/
private lemma smul_inv_of_isUnit {r : ℕ} {c : ℝ} (hc : c ≠ 0)
    {A : Matrix (Fin r) (Fin r) ℝ} (hA : IsUnit A.det) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc,
    Matrix.mul_nonsing_inv _ hA, one_smul]

/-- **The duality is an involution**: `A.dual.dual = A`. What licenses
calling `Q ↦ π²·Q⁻¹` a duality at all. -/
theorem QuadraticAction.dual_dual {r : ℕ} (A : QuadraticAction r) :
    A.dual.dual = A := by
  apply QuadraticAction.eq_of_Q_eq
  rw [QuadraticAction.dual_Q, QuadraticAction.dual_Q]
  have hdetQ : IsUnit A.Q.det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt A.Q_posDef.det_pos)
  have hpi2 : (Real.pi ^ 2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hdetInv : IsUnit (A.Q⁻¹).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (posDef_inv A.Q_posDef).det_pos)
  rw [smul_inv_of_isUnit hpi2 hdetInv,
    Matrix.nonsing_inv_nonsing_inv _ hdetQ, smul_smul,
    mul_inv_cancel₀ hpi2, one_smul]

/-- Self-duality: the dual coupling matrix is the original. -/
def QuadraticAction.selfDual {r : ℕ} (A : QuadraticAction r) : Prop :=
  A.dual.Q = A.Q

/-- Self-duality is the quadratic condition `Q² = π²·1`. -/
theorem QuadraticAction.selfDual_iff {r : ℕ} (A : QuadraticAction r) :
    A.selfDual ↔ A.Q * A.Q = (Real.pi ^ 2) • (1 : Matrix (Fin r) (Fin r) ℝ) := by
  have hdetQ : IsUnit A.Q.det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt A.Q_posDef.det_pos)
  constructor
  · intro h
    have h' : Real.pi ^ 2 • A.Q⁻¹ = A.Q := h
    calc A.Q * A.Q = A.Q * (Real.pi ^ 2 • A.Q⁻¹) := by rw [h']
      _ = Real.pi ^ 2 • (A.Q * A.Q⁻¹) := by rw [Matrix.mul_smul]
      _ = Real.pi ^ 2 • 1 := by rw [Matrix.mul_nonsing_inv _ hdetQ]
  · intro h
    show Real.pi ^ 2 • A.Q⁻¹ = A.Q
    have h2 : A.Q⁻¹ * (A.Q * A.Q) = A.Q⁻¹ * (Real.pi ^ 2 • 1) := by rw [h]
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdetQ, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one] at h2
    exact h2.symm

/-- The identity matrix is positive definite. Hand-rolled, as with
`posDef_smul'`. -/
lemma posDef_one {r : ℕ} : (1 : Matrix (Fin r) (Fin r) ℝ).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · show (1 : Matrix (Fin r) (Fin r) ℝ)ᴴ = 1
    exact Matrix.conjTranspose_one
  · rw [Matrix.one_mulVec]
    have hstar : star x = x := funext fun i => star_trivial _
    rw [hstar]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    refine Finset.sum_pos' (fun j _ => mul_self_nonneg (x j))
      ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

/-- The sum of positive-definite matrices is positive definite. -/
lemma posDef_add {r : ℕ} {A B : Matrix (Fin r) (Fin r) ℝ}
    (hA : A.PosDef) (hB : B.PosDef) : (A + B).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · show (A + B)ᴴ = A + B
    rw [Matrix.conjTranspose_add]
    congr 1
    · exact (posDef_iff_dotProduct_mulVec.mp hA).1
    · exact (posDef_iff_dotProduct_mulVec.mp hB).1
  · rw [Matrix.add_mulVec, dotProduct_add]
    exact add_pos ((posDef_iff_dotProduct_mulVec.mp hA).2 hx)
      ((posDef_iff_dotProduct_mulVec.mp hB).2 hx)

/-- **Sharpening (Phase 17, from external review)**: for a
positive-definite form, `Q² = π²·1` already forces `Q = π·1` — the
factor `Q + π·1` is positive definite, hence invertible, so
`(Q − π·1)(Q + π·1) = 0` kills the first factor. The self-dual locus
is a **single point**, while zero duality flow is the whole determinant
hypersurface `det Q = π^r`: the gap between the two conditions is now
exactly quantified. -/
theorem QuadraticAction.selfDual_iff_eq {r : ℕ} (A : QuadraticAction r) :
    A.selfDual ↔ A.Q = Real.pi • (1 : Matrix (Fin r) (Fin r) ℝ) := by
  rw [QuadraticAction.selfDual_iff]
  constructor
  · intro h
    have hsum : (A.Q + Real.pi • 1).PosDef :=
      posDef_add A.Q_posDef (posDef_smul' posDef_one Real.pi_pos)
    have hdet : IsUnit (A.Q + Real.pi • 1).det :=
      isUnit_iff_ne_zero.mpr (ne_of_gt hsum.det_pos)
    have hc1 : A.Q * (Real.pi • 1) = Real.pi • A.Q := by
      rw [Matrix.mul_smul, Matrix.mul_one]
    have hc2 : (Real.pi • (1 : Matrix (Fin r) (Fin r) ℝ)) * A.Q
        = Real.pi • A.Q := by
      rw [Matrix.smul_mul, Matrix.one_mul]
    have hc3 : (Real.pi • (1 : Matrix (Fin r) (Fin r) ℝ)) * (Real.pi • 1)
        = (Real.pi ^ 2) • 1 := by
      rw [Matrix.smul_mul, Matrix.one_mul, smul_smul]
      congr 1
      ring
    have hzero : (A.Q - Real.pi • 1) * (A.Q + Real.pi • 1) = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, h, hc1, hc2, hc3]
      abel
    have hcancel := congrArg (fun M => M * (A.Q + Real.pi • 1)⁻¹) hzero
    simp only [Matrix.zero_mul] at hcancel
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      at hcancel
    exact sub_eq_zero.mp hcancel
  · intro h
    rw [h, Matrix.smul_mul, Matrix.one_mul, smul_smul]
    congr 1
    ring

/-- Rank 1: the unique self-dual coupling is `α = π` — the fixed point
the legacy `Duality.lean` layer knows as the variational minimum. -/
theorem QuadraticAction.ofScalar_selfDual_iff (α : ℝ) (hα : 0 < α) :
    (QuadraticAction.ofScalar α hα).selfDual ↔ α = Real.pi := by
  rw [QuadraticAction.selfDual_iff,
    show (QuadraticAction.ofScalar α hα).Q = !![α] from rfl]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [Matrix.mul_apply, Matrix.smul_apply] at h00
    have hfac : (α - Real.pi) * (α + Real.pi) = 0 := by linear_combination h00
    rcases mul_eq_zero.mp hfac with h0 | h0
    · linarith
    · linarith [Real.pi_pos]
  · rintro rfl
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Matrix.smul_apply]
    try ring

/-- Real form of the general Siegel–Poisson duality, with the real
`rpow` prefactor. -/
theorem QuadraticAction.duality_real {r : ℕ} (A : QuadraticAction r) :
    A.dual.toSectorAction.partFn
      = (A.Q.det / Real.pi ^ r) ^ ((1 : ℝ) / 2) * A.toSectorAction.partFn := by
  have h := A.duality
  have hnn : (0 : ℝ) ≤ A.Q.det / Real.pi ^ r :=
    (div_pos A.Q_posDef.det_pos (pow_pos Real.pi_pos r)).le
  apply Complex.ofReal_inj.mp
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hnn]
  convert h using 2
  push_cast
  ring

/-- The duality flow: complexity lost (or gained) in passing to the
dual description. -/
noncomputable def QuadraticAction.dualityFlow {r : ℕ}
    (A : QuadraticAction r) : ℝ :=
  A.toSectorAction.complexity - A.dual.toSectorAction.complexity

/-- The flow in closed form: `-½·log(det Q / π^r)`. The generalization
of the scalar `D(α) = ½·log(π/α)`. -/
theorem QuadraticAction.dualityFlow_eq {r : ℕ} (A : QuadraticAction r) :
    A.dualityFlow = -(1 / 2) * Real.log (A.Q.det / Real.pi ^ r) := by
  have hZ : 0 < A.toSectorAction.partFn := A.toSectorAction.partFn_pos
  have ha : 0 < A.Q.det / Real.pi ^ r :=
    div_pos A.Q_posDef.det_pos (pow_pos Real.pi_pos r)
  show Real.log A.toSectorAction.partFn
      - Real.log A.dual.toSectorAction.partFn = _
  rw [A.duality_real,
    Real.log_mul (Real.rpow_pos_of_pos ha ((1 : ℝ) / 2)).ne' (ne_of_gt hZ),
    Real.log_rpow ha]
  ring

/-- The flow is antisymmetric under the duality involution. -/
theorem QuadraticAction.dualityFlow_dual {r : ℕ} (A : QuadraticAction r) :
    A.dual.dualityFlow = -A.dualityFlow := by
  unfold QuadraticAction.dualityFlow
  rw [A.dual_dual]
  ring

/-- Zero flow characterizes couplings of determinant `π^r` — a
determinant condition, **not** self-duality (see the falsification
below). -/
theorem QuadraticAction.dualityFlow_eq_zero_iff {r : ℕ}
    (A : QuadraticAction r) :
    A.dualityFlow = 0 ↔ A.Q.det = Real.pi ^ r := by
  rw [A.dualityFlow_eq]
  have ha : 0 < A.Q.det / Real.pi ^ r :=
    div_pos A.Q_posDef.det_pos (pow_pos Real.pi_pos r)
  constructor
  · intro h
    have hlog : Real.log (A.Q.det / Real.pi ^ r) = 0 := by linarith
    have hexp := Real.exp_log ha
    rw [hlog, Real.exp_zero] at hexp
    have hπr : Real.pi ^ r ≠ 0 := ne_of_gt (pow_pos Real.pi_pos r)
    field_simp at hexp
    linarith
  · intro h
    rw [h, div_self (ne_of_gt (pow_pos Real.pi_pos r)), Real.log_one, mul_zero]

/-- Self-dual actions have zero flow (via `det(Q²) = det(π²·1)`). -/
theorem QuadraticAction.selfDual.dualityFlow_eq_zero {r : ℕ}
    {A : QuadraticAction r} (h : A.selfDual) : A.dualityFlow = 0 := by
  rw [A.dualityFlow_eq_zero_iff]
  have h' := A.selfDual_iff.mp h
  have hdet : A.Q.det * A.Q.det = (Real.pi ^ 2) ^ r := by
    have hc := congrArg Matrix.det h'
    rwa [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin] at hc
  have hfac : (A.Q.det - Real.pi ^ r) * (A.Q.det + Real.pi ^ r) = 0 := by
    linear_combination hdet
  rcases mul_eq_zero.mp hfac with h0 | h0
  · linarith
  · linarith [A.Q_posDef.det_pos, pow_pos Real.pi_pos r]

/-- **Falsification of the plan's `dualityFlow_zero_iff_selfDual`** at
rank ≥ 2: `Q = diag(2π, π/2)` has determinant `π²`, hence zero flow,
but `Q² = diag(4π², π²/4) ≠ π²·1`, so it is not self-dual. Zero flow
sees only the determinant; self-duality is a condition on the whole
form. The plan's iff is true only at rank 1
(`ofScalar_selfDual_iff` + `dualityFlow_eq_zero_iff`). -/
theorem exists_dualityFlow_eq_zero_not_selfDual :
    ∃ A : QuadraticAction 2, A.dualityFlow = 0 ∧ ¬ A.selfDual := by
  have hpos : ∀ i : Fin 2, 0 < (![2 * Real.pi, Real.pi / 2]) i := by
    intro i
    fin_cases i <;> simp <;> positivity
  refine ⟨QuadraticAction.ofDiagonal ![2 * Real.pi, Real.pi / 2] hpos, ?_, ?_⟩
  · rw [QuadraticAction.dualityFlow_eq_zero_iff, QuadraticAction.ofDiagonal_det,
      Fin.prod_univ_two]
    show 2 * Real.pi * (Real.pi / 2) = Real.pi ^ 2
    ring
  · intro h
    have h' := (QuadraticAction.ofDiagonal ![2 * Real.pi, Real.pi / 2]
      hpos).selfDual_iff.mp h
    rw [QuadraticAction.ofDiagonal_Q, Matrix.diagonal_mul_diagonal] at h'
    have h00 := congrFun (congrFun h' 0) 0
    simp [Matrix.diagonal_apply_eq, Matrix.smul_apply] at h00
    nlinarith [Real.pi_pos, h00]

/-- Rank-1 matrix inverse. Public: also used by the period-model
graph instances (`Meno/PeriodHarmonic.lean`). -/
lemma inv_fin_one (α : ℝ) (hα : α ≠ 0) :
    (!![α] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = !![α⁻¹] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, mul_inv_cancel₀ hα]

/-- The general dual at rank 1 is the scalar dual coupling `π²/α`. -/
theorem QuadraticAction.ofScalar_dual_partFn (α : ℝ) (hα : 0 < α) :
    (QuadraticAction.ofScalar α hα).dual.toSectorAction.partFn
      = QuadraticAction.scalarPartFn (Real.pi ^ 2 / α) := by
  have hπα : 0 < Real.pi ^ 2 / α := div_pos (by positivity) hα
  have hQ : (QuadraticAction.ofScalar α hα).dual.Q
      = (QuadraticAction.ofScalar (Real.pi ^ 2 / α) hπα).Q := by
    rw [QuadraticAction.dual_Q]
    show Real.pi ^ 2 • (!![α] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ = !![Real.pi ^ 2 / α]
    rw [inv_fin_one α (ne_of_gt hα)]
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.smul_apply, div_eq_mul_inv]
  rw [QuadraticAction.partFn_eq_of_Q_eq _ _ hQ,
    QuadraticAction.ofScalar_partFn_eq]

/-- **The scalar T-duality, re-proved through Poisson summation.** The
same statement as `scalarPartFn_duality`, whose existing proof goes
through `jacobiTheta` and the modular `S`-transformation. Two
independent proof traditions — modular forms and Poisson summation —
now corroborate each other inside the spine; the general theorem
specializes to the theta transformation rather than depending on it. -/
theorem scalarPartFn_duality_via_poisson (α : ℝ) (hα : 0 < α) :
    (↑(QuadraticAction.scalarPartFn (Real.pi ^ 2 / α)) : ℂ)
      = ↑(α / Real.pi : ℝ) ^ ((1 : ℂ) / 2)
        * ↑(QuadraticAction.scalarPartFn α) := by
  have h := (QuadraticAction.ofScalar α hα).duality
  rw [QuadraticAction.ofScalar_dual_partFn, QuadraticAction.ofScalar_partFn_eq] at h
  rw [h]
  congr 2
  have hdet : (QuadraticAction.ofScalar α hα).Q.det = α := by
    rw [show (QuadraticAction.ofScalar α hα).Q = !![α] from rfl,
      Matrix.det_fin_one]
    simp
  rw [hdet, pow_one]

end DualityAlgebra

end Meno
