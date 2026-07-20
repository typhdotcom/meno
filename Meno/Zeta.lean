import Meno.QuadraticAction
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Riemann 1859 via the quadratic partition function

This file gives Riemann's 1859 derivation of the functional equation for ζ from
Jacobi's theta identity, applied to the quadratic partition function
`Z(α) = ∑_{n∈ℤ} e^(-α·n²)`.

Mellin-transforming `Z(α) − 1` against `α^(s−1) dα` gives the Mellin identity:

  `menoMellin s = ∫₀^∞ (Z(α) − 1) · α^(s−1) dα = 2 · Γ(s) · ζ(2s)`   (for `s > 1/2`)

Splitting the integral at the self-dual point `α = π` and applying Jacobi's
theta identity `Z(π²/α) = √(α/π)·Z(α)` (`QuadraticAction.scalarPartFn_duality_real`,
the spine's single analytic source) folds the `(0, π]`
piece onto `[π, ∞)`. The resulting symmetry

  `π^(-s) · menoMellin s = π^(-(1/2 − s)) · menoMellinC (1/2 − s)`

is the functional equation, with `menoMellinC t` the standard Riemann completion.

Specialization of the Mellin identity at `s = 3/2` yields Apéry's constant:

  `ζ(3) = (1/√π) · ∫₀^∞ (Z(α) − 1) · √α dα`.
-/

namespace Meno

open MeasureTheory Set Real QuadraticAction

/-! ## Apéry's constant -/

/-- Apéry's constant `ζ(3) = ∑_{k ≥ 1} 1/k³`. Indexed by `k : ℕ` as `k+1` to
    avoid the `1/0³ = 0` case. -/
noncomputable def aperyConst : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3


/-- Our real-valued `aperyConst` matches Mathlib's `riemannZeta 3` after casting to ℂ. -/
theorem aperyConst_eq_riemannZeta_three :
    (aperyConst : ℂ) = riemannZeta 3 := by
  have hre : (1 : ℝ) < ((3 : ℂ).re) := by norm_num
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
  unfold aperyConst
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  have h3 : (3 : ℂ) = ((3 : ℕ) : ℂ) := by norm_cast
  rw [h3, Complex.cpow_natCast]
  push_cast
  ring

/-! ## Γ(3/2) — used by the `s = 3/2` specialization below -/

private lemma gamma_three_halves : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
  have h : Real.Gamma (1 / 2 + 1) = (1 / 2) * Real.Gamma (1 / 2) :=
    Real.Gamma_add_one (by norm_num : (1/2 : ℝ) ≠ 0)
  have h2 : (1 / 2 + 1 : ℝ) = 3 / 2 := by norm_num
  rw [h2] at h
  rw [h, Real.Gamma_one_half_eq]
  ring

/-! ## General Mellin machinery at exponent `s > 0` -/

/-- Integrability of the general per-mode integrand `exp(-rα) · α^(s-1)`
    on `(0, ∞)` for `r > 0`, `s > 0`. -/
private lemma integrable_mellin_mode_gen {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    IntegrableOn (fun α => Real.exp (-(r * α)) * α ^ (s - 1)) (Ioi 0) := by
  have h : IntegrableOn (fun x : ℝ => x ^ (s - 1) * Real.exp (-r * x ^ (1:ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < s - 1)
      (le_refl 1) hr
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hxp : (0:ℝ) < x := hx
  show x ^ (s - 1) * Real.exp (-r * x ^ (1:ℝ)) = Real.exp (-(r * x)) * x ^ (s - 1)
  rw [Real.rpow_one, show (-r * x : ℝ) = -(r * x) from by ring, mul_comm]

/-- General Mellin transform of `exp(-rα)`:
    `∫₀^∞ exp(-r·α) · α^(s-1) dα = Γ(s) / r^s`. -/
private lemma integral_mellin_mode_gen {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ∫ α in Ioi 0, Real.exp (-(r * α)) * α ^ (s - 1) =
      Real.Gamma s / r ^ s := by
  have base := Real.integral_rpow_mul_exp_neg_mul_Ioi hs hr
  have hrw : (fun α : ℝ => α ^ (s - 1) * Real.exp (-(r * α)))
      =ᶠ[ae (volume.restrict (Ioi 0))]
      (fun α => Real.exp (-(r * α)) * α ^ (s - 1)) := by
    filter_upwards with α
    ring
  rw [integral_congr_ae hrw] at base
  rw [base]
  have h1 : (1 / r) ^ s = 1 / r ^ s := by
    rw [Real.div_rpow (by norm_num : (0:ℝ) ≤ 1) hr.le, Real.one_rpow]
  rw [h1]
  field_simp

/-- Specialization at `r = (k+1)²`:
    `∫ exp(-(k+1)²·α) · α^(s-1) dα = Γ(s) / (k+1)^(2s)`. -/
private lemma integral_mellin_mode_sq_gen (k : ℕ) {s : ℝ} (hs : 0 < s) :
    ∫ α in Ioi 0, Real.exp (-(((k:ℝ) + 1)^2 * α)) * α ^ (s - 1) =
      Real.Gamma s / ((k:ℝ) + 1) ^ (2 * s) := by
  have hr : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [integral_mellin_mode_gen hr hs]
  congr 1
  rw [show (((k : ℝ) + 1) ^ 2 : ℝ) = ((k : ℝ) + 1) ^ (2 : ℝ) from
        (Real.rpow_natCast _ 2).symm,
      ← Real.rpow_mul hkpos.le]

/-! ## The Meno spectral integral -/

/-- The Meno spectral integral: the non-vacuum excitation content of the
    partition function, integrated against `√α dα` over all couplings. -/
noncomputable def menoSpectralIntegral : ℝ :=
  ∫ α in Ioi 0, (scalarPartFn α - 1) * Real.sqrt α

/-! ## Symmetric split of the partition function -/

private lemma summable_exp_sq_nat (α : ℝ) (hα : 0 < α) :
    Summable (fun i : ℕ => Real.exp (-α * (i : ℝ) ^ 2)) := by
  have hle : ∀ i : ℕ, (↑i : ℝ) ≤ (↑i : ℝ) ^ 2 := by
    intro i; rcases i with _ | i
    · simp
    · nlinarith [sq_nonneg ((↑(i + 1) : ℝ) - 1),
        show (1 : ℝ) ≤ ↑(i + 1) from by exact_mod_cast Nat.succ_pos i]
  exact Real.summable_exp_nat_mul_of_ge (neg_neg_of_pos hα)
    (f := fun i => (↑i : ℝ) ^ 2) hle

private lemma summable_exp_sq_shift (α : ℝ) (hα : 0 < α) :
    Summable (fun k : ℕ => Real.exp (-α * ((k:ℝ) + 1) ^ 2)) := by
  have h := (summable_nat_add_iff 1).mpr (summable_exp_sq_nat α hα)
  exact h.congr fun k => by push_cast; rfl

/-- Symmetric split: the partition function minus its vacuum term equals
    twice the sum over positive modes. The ℤ-sum over `k²` collapses to
    the ℕ-sum over `(k+1)²` doubled (by evenness) plus the `k=0` term. -/
private lemma scalarPartFn_sub_one_eq (α : ℝ) (hα : 0 < α) :
    scalarPartFn α - 1 = 2 * ∑' k : ℕ, Real.exp (-α * ((k:ℝ) + 1) ^ 2) := by
  set S : ℝ := ∑' k : ℕ, Real.exp (-α * ((k:ℝ) + 1) ^ 2) with hS_def
  have hshift : Summable (fun k : ℕ => Real.exp (-α * ((k:ℝ) + 1) ^ 2)) :=
    summable_exp_sq_shift α hα
  have hSum_S : HasSum (fun k : ℕ => Real.exp (-α * ((k:ℝ) + 1) ^ 2)) S := hshift.hasSum
  have hf₁ : HasSum
      (fun n : ℕ => Real.exp (-α * ((((n:ℤ) + 1):ℤ):ℝ) ^ 2)) S := by
    refine hSum_S.congr fun n => ?_
    push_cast; rfl
  have hf₂ : HasSum
      (fun n : ℕ => Real.exp (-α * ((-(((n:ℤ) + 1)):ℤ):ℝ) ^ 2)) S := by
    refine hSum_S.congr fun n => ?_
    push_cast; ring_nf
  have hZ : HasSum (fun k : ℤ => Real.exp (-α * ((k:ℤ):ℝ) ^ 2))
      (S + Real.exp (-α * (((0:ℤ):ℝ)) ^ 2) + S) :=
    HasSum.of_add_one_of_neg_add_one hf₁ hf₂
  have hZ_val : scalarPartFn α = S + 1 + S := by
    have h := hZ.tsum_eq
    have h0 : Real.exp (-α * (((0:ℤ):ℝ)) ^ 2) = 1 := by simp
    rw [h0] at h
    show ∑' k : ℤ, Real.exp (-α * (k : ℝ) ^ 2) = S + 1 + S
    convert h using 1
  rw [hZ_val]
  ring

/-- General per-mode integrand `2·exp(-α(k+1)²)·α^(s-1)` is integrable on `Ioi 0`. -/
private lemma integrableOn_menoMode_gen (k : ℕ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun α => 2 * Real.exp (-α * ((k:ℝ)+1)^2) * α ^ (s - 1)) (Ioi 0) := by
  have hr : (0 : ℝ) < ((k:ℝ)+1)^2 := by positivity
  have h : IntegrableOn
      (fun α => 2 * (Real.exp (-((((k:ℝ)+1)^2) * α)) * α ^ (s - 1))) (Ioi 0) :=
    (integrable_mellin_mode_gen hr hs).const_mul 2
  refine h.congr_fun ?_ measurableSet_Ioi
  intro α hα
  show 2 * (Real.exp (-((((k:ℝ)+1)^2) * α)) * α ^ (s - 1))
    = 2 * Real.exp (-α * ((k:ℝ)+1)^2) * α ^ (s - 1)
  ring_nf

/-- General per-mode integral value:
    `∫ 2·exp(-α(k+1)²)·α^(s-1) dα = 2·Γ(s) / (k+1)^(2s)`. -/
private lemma integral_menoMode_gen (k : ℕ) {s : ℝ} (hs : 0 < s) :
    ∫ α in Ioi 0, 2 * Real.exp (-α * ((k:ℝ)+1)^2) * α ^ (s - 1) =
      2 * Real.Gamma s / ((k:ℝ) + 1) ^ (2 * s) := by
  have hr : (0 : ℝ) < ((k:ℝ)+1)^2 := by positivity
  have hbase := integral_mellin_mode_sq_gen k hs
  have hrw : ∫ α in Ioi 0, 2 * Real.exp (-α * ((k:ℝ)+1)^2) * α ^ (s - 1)
      = 2 * ∫ α in Ioi 0, Real.exp (-(((k:ℝ)+1)^2 * α)) * α ^ (s - 1) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards with α _
    ring_nf
  rw [hrw, hbase]
  ring

/-! ## The general Meno Mellin identity -/

/-- The Meno Mellin transform at arbitrary exponent `s`:
    `∫₀^∞ (Z(α) - 1) · α^(s-1) dα`. -/
noncomputable def menoMellin (s : ℝ) : ℝ :=
  ∫ α in Ioi 0, (scalarPartFn α - 1) * α ^ (s - 1)

/-- Summability of `∑ 1/(k+1)^(2s)` at `s > 1/2`. -/
private lemma summable_apery_gen {s : ℝ} (hs : 1/2 < s) :
    Summable (fun k : ℕ => 1 / ((k:ℝ) + 1) ^ (2 * s)) := by
  have h2s : 1 < 2 * s := by linarith
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 * s)) :=
    Real.summable_one_div_nat_rpow.mpr h2s
  have hshift : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) ^ (2 * s)) :=
    (summable_nat_add_iff 1).mpr h
  exact hshift.congr fun k => by push_cast; rfl

/-- **Meno Mellin identity** at general exponent `s > 1/2`:
    `∫₀^∞ (Z(α) - 1) · α^(s-1) dα = 2 · Γ(s) · ∑' 1/(k+1)^(2s)`.
    This is Riemann's 1859 Mellin step: theta ↦ zeta. -/
theorem meno_mellin {s : ℝ} (hs : 1/2 < s) :
    menoMellin s = 2 * Real.Gamma s * ∑' k : ℕ, 1 / ((k:ℝ) + 1) ^ (2 * s) := by
  have hs_pos : 0 < s := lt_trans (by norm_num : (0:ℝ) < 1/2) hs
  have hsum_gen := summable_apery_gen hs
  set F : ℕ → ℝ → ℝ := fun k α => 2 * Real.exp (-α * ((k:ℝ)+1)^2) * α ^ (s - 1)
      with hF_def
  have hF_int : ∀ k : ℕ, Integrable (F k) (volume.restrict (Ioi 0)) := fun k =>
    integrableOn_menoMode_gen k hs_pos
  have hF_val : ∀ k : ℕ, ∫ α, F k α ∂(volume.restrict (Ioi 0))
      = 2 * Real.Gamma s / ((k:ℝ) + 1) ^ (2 * s) := fun k => integral_menoMode_gen k hs_pos
  have hNorm_val : ∀ k : ℕ, ∫ α, ‖F k α‖ ∂(volume.restrict (Ioi 0))
      = 2 * Real.Gamma s / ((k:ℝ) + 1) ^ (2 * s) := by
    intro k
    rw [← hF_val k]
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards with α hα
    have hαpos : (0:ℝ) < α := hα
    have hnn : 0 ≤ F k α := by
      show 0 ≤ 2 * Real.exp (-α * ((k:ℝ)+1)^2) * α ^ (s - 1)
      have h1 : 0 ≤ Real.exp (-α * ((k:ℝ)+1)^2) := (Real.exp_pos _).le
      have h2 : 0 ≤ α ^ (s - 1) := Real.rpow_nonneg hαpos.le _
      positivity
    exact Real.norm_of_nonneg hnn
  have hSum_norm : Summable (fun k => ∫ α, ‖F k α‖ ∂(volume.restrict (Ioi 0))) := by
    have h : Summable (fun k : ℕ => 2 * Real.Gamma s / ((k:ℝ)+1)^(2*s)) := by
      have hs_base := hsum_gen.mul_left (2 * Real.Gamma s)
      refine hs_base.congr fun k => ?_
      rw [mul_one_div]
    exact h.congr fun k => (hNorm_val k).symm
  have hInterchange :=
    MeasureTheory.hasSum_integral_of_summable_integral_norm hF_int hSum_norm
  have hLHS : (fun x : ℕ => ∫ α, F x α ∂(volume.restrict (Ioi 0)))
      = fun k : ℕ => 2 * Real.Gamma s / ((k:ℝ) + 1) ^ (2 * s) := by
    funext k; exact hF_val k
  rw [hLHS] at hInterchange
  have hRHS : (∫ α, ∑' k : ℕ, F k α ∂(volume.restrict (Ioi 0)))
      = menoMellin s := by
    show ∫ α in Ioi 0, ∑' k : ℕ, F k α = menoMellin s
    unfold menoMellin
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards with α hα
    have hαpos : (0 : ℝ) < α := hα
    calc ∑' k : ℕ, F k α
        = ∑' k : ℕ, 2 * Real.exp (-α * ((k:ℝ)+1)^2) * α ^ (s - 1) := rfl
      _ = (∑' k : ℕ, 2 * Real.exp (-α * ((k:ℝ)+1)^2)) * α ^ (s - 1) :=
          tsum_mul_right
      _ = (2 * ∑' k : ℕ, Real.exp (-α * ((k:ℝ)+1)^2)) * α ^ (s - 1) := by
          rw [(summable_exp_sq_shift α hαpos).tsum_mul_left]
      _ = (scalarPartFn α - 1) * α ^ (s - 1) := by
          rw [← scalarPartFn_sub_one_eq α hαpos]
  rw [hRHS] at hInterchange
  have hSum_val : HasSum (fun k : ℕ => 2 * Real.Gamma s / ((k:ℝ) + 1) ^ (2 * s))
      (2 * Real.Gamma s * ∑' k : ℕ, 1 / ((k:ℝ) + 1) ^ (2 * s)) := by
    have hs_base := (hsum_gen.hasSum).mul_left (2 * Real.Gamma s)
    refine hs_base.congr_fun fun k => ?_
    rw [mul_one_div]
  exact (hSum_val.unique hInterchange).symm

/-! ## T-duality on the Mellin integrand

`scalarPartFn_duality_real` (from `Meno.Duality`) is Jacobi's theta identity.
The results in this section lift it to the Mellin level. -/

/-- The form of `scalarPartFn_duality_real` that appears inside the Mellin
    integrand, which sees `Z − 1` rather than `Z`. The `√(α/π) − 1` shift is
    the vacuum-subtracted correction to a multiplicative rescaling. -/
theorem dual_partFn_sub_one_eq_residual (α : ℝ) (hα : 0 < α) :
    scalarPartFn (Real.pi ^ 2 / α) - 1 =
      Real.sqrt (α / Real.pi) * (scalarPartFn α - 1) +
        (Real.sqrt (α / Real.pi) - 1) := by
  have h := scalarPartFn_duality_real α hα
  have hsqrt : (α / Real.pi) ^ ((1 : ℝ) / 2) = Real.sqrt (α / Real.pi) :=
    (Real.sqrt_eq_rpow _).symm
  rw [hsqrt] at h
  rw [h]; ring


/-- The spectral integral `∫(Z−1)·√α dα` is the Mellin transform at exponent `3/2`.
    This is the hinge: once this is known, every `s = 3/2` statement reduces to a
    specialization of the general Mellin identity. -/
theorem menoSpectralIntegral_eq_menoMellin_three_halves :
    menoSpectralIntegral = menoMellin (3/2) := by
  unfold menoSpectralIntegral menoMellin
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards with α hα
  have hαpos : (0:ℝ) < α := hα
  have hsqrt : Real.sqrt α = α ^ ((3/2 : ℝ) - 1) := by
    rw [show (3/2 : ℝ) - 1 = 1/2 from by norm_num, Real.sqrt_eq_rpow]
  rw [hsqrt]

/-- **Headline** (Apéry, Meno form): `ζ(3) = (1/√π)·∫₀^∞(Z−1)·√α dα`.
    Proved as the specialization of `meno_mellin` at `s = 3/2`, using
    `Γ(3/2) = √π/2` and `(k+1)^(2·(3/2)) = (k+1)^3`. -/
theorem zeta_three_eq_meno_integral :
    aperyConst = (1 / Real.sqrt Real.pi) * menoSpectralIntegral := by
  have hs : (1/2 : ℝ) < 3/2 := by norm_num
  have hsqrt_pi_ne : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [menoSpectralIntegral_eq_menoMellin_three_halves, meno_mellin hs,
      gamma_three_halves]
  have hconv : (fun k : ℕ => (1:ℝ) / ((k:ℝ) + 1)^(2*(3/2 : ℝ)))
             = (fun k : ℕ => (1:ℝ) / ((k:ℝ) + 1)^(3:ℕ)) := by
    funext k
    congr 1
    rw [show (2 * (3/2) : ℝ) = ((3:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
  rw [hconv]
  unfold aperyConst
  field_simp


/-- **Complex headline**: `ζ(3) = (1/√π)·∫(Z−1)·√α dα` stated against Mathlib's
    `riemannZeta 3`. Composition of `aperyConst_eq_riemannZeta_three` with the
    real headline. -/
theorem riemannZeta_three_eq_meno_spectral_integral :
    riemannZeta 3 = ((1 / Real.sqrt Real.pi * menoSpectralIntegral : ℝ) : ℂ) := by
  rw [← aperyConst_eq_riemannZeta_three, zeta_three_eq_meno_integral]

/-! ## Bridge to Mathlib's complex ζ -/

/-- `menoMellin s` equals `2·Γ(s)·ζ(2s)` in ℂ, for real `s > 1/2`. Gateway to
    Mathlib's complex ζ machinery (functional equation, analytic continuation,
    Euler product). -/
theorem menoMellin_cast_eq_riemannZeta_real {s : ℝ} (hs : 1/2 < s) :
    (menoMellin s : ℂ) = 2 * Complex.Gamma s * riemannZeta (2 * s) := by
  have h2s_real : (1 : ℝ) < 2 * s := by linarith
  have h2s_re : (1 : ℝ) < (((2 : ℂ) * (s : ℂ))).re := by
    have : ((2:ℂ) * (s:ℂ)).re = 2 * s := by simp
    rw [this]; exact h2s_real
  rw [meno_mellin hs, zeta_eq_tsum_one_div_nat_add_one_cpow h2s_re]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_ofNat,
      ← Complex.Gamma_ofReal, Complex.ofReal_tsum]
  congr 1
  refine tsum_congr fun k => ?_
  have hk_nonneg : (0 : ℝ) ≤ (k:ℝ) + 1 := by positivity
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow hk_nonneg]
  push_cast
  ring

/-! ## Functional equation via Riemann 1859 split at α = π -/

/-- **Continuity of the partition function on the closed half-line `[π, ∞)`**.
    Weierstrass M-test with dominating series `exp(-π·k²)` (absolutely summable
    by `summable_scalarPartFn`). Each per-mode term `exp(-α·k²)` decreases in
    `α`, so on `α ≥ π` is dominated by `exp(-π·k²)`. -/
private lemma continuousOn_scalarPartFn_Ici_pi :
    ContinuousOn scalarPartFn (Ici Real.pi) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  unfold scalarPartFn
  refine continuousOn_tsum
    (f := fun (k : ℤ) (α : ℝ) => Real.exp (-α * (k : ℝ) ^ 2))
    (u := fun (k : ℤ) => Real.exp (-Real.pi * (k : ℝ) ^ 2)) ?_ ?_ ?_
  · intro k
    refine Real.continuous_exp.continuousOn.comp ?_ (Set.mapsTo_univ _ _)
    exact ((continuous_id.neg.mul continuous_const).continuousOn)
  · exact summable_scalarPartFn Real.pi hπ
  · intro k α hα
    have hα_ge : Real.pi ≤ α := hα
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hk2 : (0 : ℝ) ≤ (k : ℝ)^2 := sq_nonneg _
    nlinarith

/-- **Exponential bound on `Z(α) - 1` for `α ≥ π`**. From the expansion
    `Z(α) - 1 = 2 ∑_{k≥0} exp(-α(k+1)²)` and the inequality
    `(k+1)² ≥ k+1`, the non-vacuum sum is bounded by a geometric series:
    `∑_{k≥0} exp(-α(k+1)²) ≤ ∑_{k≥0} exp(-α)·exp(-α)^k = exp(-α)/(1-exp(-α))`.
    Monotonicity in the denominator (`exp(-α) ≤ exp(-π)`) gives the π-normalized
    bound. -/
private lemma scalarPartFn_sub_one_tail_bound (α : ℝ) (hα : Real.pi ≤ α) :
    scalarPartFn α - 1 ≤ 2 * Real.exp (-α) / (1 - Real.exp (-Real.pi)) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hα_pos : 0 < α := hπ.trans_le hα
  have hα_exp_pos : 0 < Real.exp (-α) := Real.exp_pos _
  have hα_exp_lt_one : Real.exp (-α) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (neg_neg_of_pos hα_pos)
  have hπ_exp_lt_one : Real.exp (-Real.pi) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (neg_neg_of_pos hπ)
  have h_one_sub_π_pos : 0 < 1 - Real.exp (-Real.pi) := sub_pos.mpr hπ_exp_lt_one
  have h_one_sub_α_pos : 0 < 1 - Real.exp (-α) := sub_pos.mpr hα_exp_lt_one
  have h_exp_mono : Real.exp (-α) ≤ Real.exp (-Real.pi) :=
    Real.exp_le_exp.mpr (neg_le_neg hα)
  have hterm : ∀ k : ℕ,
      Real.exp (-α * ((k:ℝ) + 1)^2) ≤ Real.exp (-α) * Real.exp (-α) ^ k := by
    intro k
    have hpow : Real.exp (-α) ^ k = Real.exp (-α * (k : ℝ)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [hpow, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hrewrite : -α + -α * (k : ℝ) = -α * ((k : ℝ) + 1) := by ring
    rw [hrewrite]
    have hsq : ((k : ℝ) + 1)^2 ≥ (k : ℝ) + 1 := by nlinarith
    nlinarith
  have horig_summ : Summable (fun k : ℕ => Real.exp (-α * ((k:ℝ) + 1)^2)) :=
    summable_exp_sq_shift α hα_pos
  have hgeo : Summable (fun k : ℕ => Real.exp (-α) ^ k) :=
    summable_geometric_of_lt_one hα_exp_pos.le hα_exp_lt_one
  have hbound_summ : Summable (fun k : ℕ => Real.exp (-α) * Real.exp (-α) ^ k) :=
    hgeo.mul_left _
  have htsum_bound : ∑' k : ℕ, Real.exp (-α * ((k:ℝ) + 1)^2)
                   ≤ Real.exp (-α) / (1 - Real.exp (-α)) := by
    calc ∑' k : ℕ, Real.exp (-α * ((k:ℝ) + 1)^2)
        ≤ ∑' k : ℕ, Real.exp (-α) * Real.exp (-α) ^ k :=
          horig_summ.tsum_le_tsum hterm hbound_summ
      _ = Real.exp (-α) * ∑' k : ℕ, Real.exp (-α) ^ k :=
          hgeo.tsum_mul_left (Real.exp (-α))
      _ = Real.exp (-α) * (1 - Real.exp (-α))⁻¹ := by
          rw [tsum_geometric_of_lt_one hα_exp_pos.le hα_exp_lt_one]
      _ = Real.exp (-α) / (1 - Real.exp (-α)) := by rw [div_eq_mul_inv]
  rw [scalarPartFn_sub_one_eq α hα_pos]
  have hstep2 : Real.exp (-α) / (1 - Real.exp (-α))
              ≤ Real.exp (-α) / (1 - Real.exp (-Real.pi)) := by
    apply div_le_div_of_nonneg_left hα_exp_pos.le h_one_sub_π_pos
    linarith
  calc 2 * ∑' k : ℕ, Real.exp (-α * ((k:ℝ) + 1)^2)
      ≤ 2 * (Real.exp (-α) / (1 - Real.exp (-α))) := by linarith
    _ ≤ 2 * (Real.exp (-α) / (1 - Real.exp (-Real.pi))) := by linarith
    _ = 2 * Real.exp (-α) / (1 - Real.exp (-Real.pi)) := by ring

/-- Non-negativity of the tail integrand factor `Z(α) - 1` for `α > 0`.
    Immediate from `scalarPartFn_gt_one`. -/
private lemma scalarPartFn_sub_one_nonneg (α : ℝ) (hα : 0 < α) :
    0 ≤ scalarPartFn α - 1 :=
  le_of_lt (sub_pos.mpr (scalarPartFn_gt_one α hα))

/-- **Integrability of the tail integrand** for any real `s`. Uses
    `integrable_of_isBigO_exp_neg` with `b = 1/2`: continuity on `[π, ∞)` from
    `continuousOn_scalarPartFn_Ici_pi`, and `=O(exp(-α/2))` at `∞` by:
    `(Z-1)·α^(s-1) ≤ C·exp(-α)·α^(s-1) = exp(-α/2)·(exp(-α/2)·α^(s-1))` where
    the last factor is `o(1)` since `α^(s-1) = o(exp(α/2))` at `∞`. -/
private lemma menoMellinTail_integrableOn (s : ℝ) :
    IntegrableOn (fun α => (scalarPartFn α - 1) * α ^ (s - 1)) (Ioi Real.pi) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπ_exp_lt_one : Real.exp (-Real.pi) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (neg_neg_of_pos hπ)
  have h_one_sub_π_pos : 0 < 1 - Real.exp (-Real.pi) := sub_pos.mpr hπ_exp_lt_one
  have hC_pos : 0 < 2 / (1 - Real.exp (-Real.pi)) :=
    div_pos (by norm_num : (0:ℝ) < 2) h_one_sub_π_pos
  apply integrable_of_isBigO_exp_neg (show (0:ℝ) < 1/2 by norm_num)
  · apply ContinuousOn.mul
    · exact continuousOn_scalarPartFn_Ici_pi.sub continuousOn_const
    · intro α hα
      have hα_pos : 0 < α := hπ.trans_le hα
      exact (Real.continuousAt_rpow_const α (s - 1)
        (Or.inl (ne_of_gt hα_pos))).continuousWithinAt
  · have hO1 : (fun α : ℝ => (scalarPartFn α - 1) * α ^ (s - 1)) =O[Filter.atTop]
              (fun α => Real.exp (-α) * α ^ (s - 1)) := by
      refine Asymptotics.IsBigO.of_bound (2 / (1 - Real.exp (-Real.pi))) ?_
      filter_upwards [Filter.eventually_ge_atTop Real.pi] with α hα
      have hα_pos : 0 < α := hπ.trans_le hα
      have h_znn : 0 ≤ scalarPartFn α - 1 := scalarPartFn_sub_one_nonneg α hα_pos
      have h_rpos : 0 < α ^ (s - 1) := Real.rpow_pos_of_pos hα_pos _
      have h_epos : 0 < Real.exp (-α) := Real.exp_pos _
      have h_bd := scalarPartFn_sub_one_tail_bound α hα
      have h_nonneg_l : (0 : ℝ) ≤ (scalarPartFn α - 1) * α ^ (s - 1) := by positivity
      have h_nonneg_r : (0 : ℝ) ≤ Real.exp (-α) * α ^ (s - 1) := by positivity
      rw [Real.norm_of_nonneg h_nonneg_l, Real.norm_of_nonneg h_nonneg_r]
      have hbound_prod : (scalarPartFn α - 1) * α ^ (s - 1) ≤
          (2 / (1 - Real.exp (-Real.pi)) * Real.exp (-α)) * α ^ (s - 1) := by
        apply mul_le_mul_of_nonneg_right _ h_rpos.le
        have : 2 * Real.exp (-α) / (1 - Real.exp (-Real.pi))
             = 2 / (1 - Real.exp (-Real.pi)) * Real.exp (-α) := by ring
        linarith [h_bd]
      linarith [hbound_prod]
    have hlo : (fun α : ℝ => α ^ (s - 1)) =o[Filter.atTop]
              (fun α => Real.exp ((1/2) * α)) :=
      isLittleO_rpow_exp_pos_mul_atTop (s - 1) (by norm_num : (0:ℝ) < 1/2)
    have hexp_rw : (fun α : ℝ => Real.exp (-α) * Real.exp ((1/2) * α))
                 = (fun α => Real.exp (-(1/2) * α)) := by
      funext α
      rw [← Real.exp_add]; congr 1; ring
    have hO2 : (fun α : ℝ => Real.exp (-α) * α ^ (s - 1)) =o[Filter.atTop]
              (fun α => Real.exp (-(1/2) * α)) := by
      have := (Asymptotics.isBigO_refl (fun α : ℝ => Real.exp (-α)) Filter.atTop).mul_isLittleO hlo
      rw [hexp_rw] at this
      exact this
    exact (hO1.trans_isLittleO hO2).isBigO

/-- **The Meno tail Mellin integral** `∫_π^∞ (Z(α) - 1) · α^(s-1) dα`.
    Convergent for every real `s` by `menoMellinTail_integrableOn`. The
    tail-only nature (no singularity at `α = 0`) lifts the `s > 1/2` restriction
    that binds `menoMellin s`. -/
noncomputable def menoMellinTail (s : ℝ) : ℝ :=
  ∫ α in Ioi Real.pi, (scalarPartFn α - 1) * α ^ (s - 1)

/-! ### Sub-interval CoV `α = π²/β` on `Ioc 0 π ↔ Ici π` -/

/-- Image of `β ↦ π²/β` on `Ici π` is `Ioc 0 π`. The involution interchanges the two
    sub-intervals that share the self-dual point `α = π`. -/
private lemma image_pi_sq_div_Ici_pi :
    (fun β : ℝ => Real.pi ^ 2 / β) '' Ici Real.pi = Ioc 0 Real.pi := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπ2 : 0 < Real.pi ^ 2 := sq_pos_of_pos hπ
  ext α
  simp only [Set.mem_image, Set.mem_Ici, Set.mem_Ioc]
  constructor
  · rintro ⟨β, hβ, rfl⟩
    have hβ_pos : 0 < β := hπ.trans_le hβ
    refine ⟨div_pos hπ2 hβ_pos, ?_⟩
    rw [div_le_iff₀ hβ_pos]
    nlinarith
  · rintro ⟨hα_pos, hα_le⟩
    refine ⟨Real.pi ^ 2 / α, ?_, div_div_cancel₀ hπ2.ne'⟩
    rw [le_div_iff₀ hα_pos]
    nlinarith

/-- `β ↦ π²/β` is injective on `Ici π`: strictly decreasing on positive reals
    because the derivative is `-π²/β² < 0`. -/
private lemma injOn_pi_sq_div :
    Set.InjOn (fun β : ℝ => Real.pi ^ 2 / β) (Ici Real.pi) := by
  intro x hx y hy hxy
  have hx_pos : 0 < x := Real.pi_pos.trans_le hx
  have hy_pos : 0 < y := Real.pi_pos.trans_le hy
  have hπ2_ne : Real.pi ^ 2 ≠ 0 := (sq_pos_of_pos Real.pi_pos).ne'
  have hxy' : Real.pi ^ 2 / x = Real.pi ^ 2 / y := hxy
  field_simp at hxy'
  exact hxy'.symm

/-- Derivative of `β ↦ π²/β` within `Ici π` is `-π²/β²`. -/
private lemma hasDerivWithinAt_pi_sq_div (β : ℝ) (hβ : Real.pi ≤ β) :
    HasDerivWithinAt (fun β' : ℝ => Real.pi ^ 2 / β')
        (-(Real.pi ^ 2 / β ^ 2)) (Ici Real.pi) β := by
  have hβ_pos : 0 < β := Real.pi_pos.trans_le hβ
  have hβ_ne : β ≠ 0 := hβ_pos.ne'
  have hinv : HasDerivWithinAt (fun x : ℝ => x⁻¹) (-(β ^ 2)⁻¹) (Ici Real.pi) β :=
    hasDerivWithinAt_inv hβ_ne _
  have hmul := hinv.const_mul (Real.pi ^ 2)
  have hfun_eq : (fun x : ℝ => Real.pi ^ 2 * x⁻¹) = fun x : ℝ => Real.pi ^ 2 / x := by
    funext x; rw [← div_eq_mul_inv]
  have hval : Real.pi ^ 2 * -(β ^ 2)⁻¹ = -(Real.pi ^ 2 / β ^ 2) := by
    rw [mul_neg, ← div_eq_mul_inv]
  rw [hfun_eq] at hmul
  rw [← hval]
  exact hmul

/-- Pointwise algebraic identity: the CoV Jacobian multiplied by the transformed
    power collapses to `π^(2s) · β^(-s-1)`. -/
private lemma cov_rpow_identity (β : ℝ) (hβ : 0 < β) (s : ℝ) :
    (Real.pi ^ 2 / β ^ 2) * (Real.pi ^ 2 / β) ^ (s - 1) =
      Real.pi ^ (2 * s) * β ^ (-s - 1) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπ2 : 0 < Real.pi ^ 2 := sq_pos_of_pos hπ
  have h_pi_two : (Real.pi ^ 2 : ℝ) = Real.pi ^ ((2 : ℝ)) := (Real.rpow_two Real.pi).symm
  have h_beta_two : (β ^ 2 : ℝ) = β ^ ((2 : ℝ)) := (Real.rpow_two β).symm
  rw [Real.div_rpow hπ2.le hβ.le]
  rw [h_pi_two, ← Real.rpow_mul hπ.le]
  rw [h_beta_two]
  rw [div_eq_mul_inv (Real.pi ^ ((2:ℝ))) (β ^ ((2:ℝ))), ← Real.rpow_neg hβ.le]
  rw [div_eq_mul_inv (Real.pi ^ (2 * (s - 1))) (β ^ (s - 1)), ← Real.rpow_neg hβ.le]
  have hprod_pi : Real.pi ^ ((2:ℝ)) * Real.pi ^ (2 * (s - 1)) = Real.pi ^ (2 * s) := by
    rw [← Real.rpow_add hπ]; congr 1; ring
  have hprod_beta : β ^ (-(2:ℝ)) * β ^ (-(s - 1)) = β ^ (-s - 1) := by
    rw [← Real.rpow_add hβ]; congr 1; ring
  calc Real.pi ^ ((2:ℝ)) * β ^ (-(2:ℝ)) * (Real.pi ^ (2 * (s - 1)) * β ^ (-(s - 1)))
      = (Real.pi ^ ((2:ℝ)) * Real.pi ^ (2 * (s - 1))) *
        (β ^ (-(2:ℝ)) * β ^ (-(s - 1))) := by ring
    _ = Real.pi ^ (2 * s) * β ^ (-s - 1) := by rw [hprod_pi, hprod_beta]

/-- **Sub-interval CoV** `α = π²/β`: the `(0, π]` head of `menoMellin` folded onto
    `[π, ∞)` via the measurable involution. Proof applies
    `MeasureTheory.integral_image_eq_integral_abs_deriv_smul` to `f(β) = π²/β` on
    `Ici π`, whose image is `Ioc 0 π` (by `image_pi_sq_div_Ici_pi`) and whose
    Jacobian `|−π²/β²|` combines with the rpow-transformed integrand to produce
    the `π^(2s) · β^(-s-1)` kernel. -/
private lemma menoMellin_head_cov_pi_sq (s : ℝ) :
    ∫ α in Ioc 0 Real.pi, (scalarPartFn α - 1) * α ^ (s - 1) =
      Real.pi ^ (2 * s) *
        ∫ β in Ici Real.pi, (scalarPartFn (Real.pi ^ 2 / β) - 1) * β ^ (-s - 1) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  set f : ℝ → ℝ := fun β => Real.pi ^ 2 / β with hf_def
  set f' : ℝ → ℝ := fun β => -(Real.pi ^ 2 / β ^ 2) with hf'_def
  set g : ℝ → ℝ := fun α => (scalarPartFn α - 1) * α ^ (s - 1) with hg_def
  have h_deriv : ∀ β ∈ Ici Real.pi, HasDerivWithinAt f (f' β) (Ici Real.pi) β :=
    fun β hβ => hasDerivWithinAt_pi_sq_div β hβ
  have hCoV :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (measurableSet_Ici (a := Real.pi)) h_deriv injOn_pi_sq_div g
  rw [image_pi_sq_div_Ici_pi] at hCoV
  rw [hCoV, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.setIntegral_congr_ae measurableSet_Ici ?_
  filter_upwards with β hβ
  have hβ_ge : Real.pi ≤ β := hβ
  have hβ_pos : 0 < β := hπ.trans_le hβ_ge
  have hβ2_pos : 0 < β ^ 2 := sq_pos_of_pos hβ_pos
  have habs : |f' β| = Real.pi ^ 2 / β ^ 2 := by
    show |-(Real.pi ^ 2 / β ^ 2)| = Real.pi ^ 2 / β ^ 2
    rw [abs_neg, abs_of_pos (div_pos (sq_pos_of_pos hπ) hβ2_pos)]
  show |f' β| • g (f β) =
      Real.pi ^ (2 * s) * ((scalarPartFn (Real.pi ^ 2 / β) - 1) * β ^ (-s - 1))
  rw [smul_eq_mul, habs]
  show (Real.pi ^ 2 / β ^ 2) *
        ((scalarPartFn (Real.pi ^ 2 / β) - 1) * (Real.pi ^ 2 / β) ^ (s - 1)) =
      Real.pi ^ (2 * s) * ((scalarPartFn (Real.pi ^ 2 / β) - 1) * β ^ (-s - 1))
  have hid := cov_rpow_identity β hβ_pos s
  set Z := scalarPartFn (Real.pi ^ 2 / β) - 1 with hZ
  calc (Real.pi ^ 2 / β ^ 2) * (Z * (Real.pi ^ 2 / β) ^ (s - 1))
      = ((Real.pi ^ 2 / β ^ 2) * (Real.pi ^ 2 / β) ^ (s - 1)) * Z := by ring
    _ = (Real.pi ^ (2 * s) * β ^ (-s - 1)) * Z := by rw [hid]
    _ = Real.pi ^ (2 * s) * (Z * β ^ (-s - 1)) := by ring

/-! ### Elementary integral: `∫_π^∞ (√(β/π) − 1) · β^(-s-1) dβ` for `s > 1/2` -/

/-- The elementary integral `∫_π^∞ β^(-s-1/2) dβ = π^(1/2-s) / (s - 1/2)` for `s > 1/2`. -/
private lemma integral_rpow_tail_pi_neg_half (s : ℝ) (hs : 1 / 2 < s) :
    ∫ β in Ioi Real.pi, β ^ (-s - 1/2) = Real.pi ^ (1/2 - s) / (s - 1/2) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hy : (-s - 1/2 : ℝ) < -1 := by linarith
  have h := integral_Ioi_rpow_of_lt hy hπ
  -- integral_Ioi_rpow_of_lt gives: ∫ x in Ioi π, x^(y) = -π^(y+1) / (y+1) where y < -1
  -- with y = -s - 1/2, y + 1 = 1/2 - s
  have hrewrite : -Real.pi ^ (-s - 1/2 + 1) / (-s - 1/2 + 1) =
                  Real.pi ^ (1/2 - s) / (s - 1/2) := by
    have h1 : (-s - 1/2 + 1 : ℝ) = 1/2 - s := by ring
    rw [h1]
    have h2 : -Real.pi ^ (1/2 - s) / (1/2 - s) = Real.pi ^ (1/2 - s) / (s - 1/2) := by
      rw [neg_div, ← div_neg]; congr 1; ring
    exact h2
  rw [h, hrewrite]

/-- The elementary integral `∫_π^∞ β^(-s-1) dβ = π^(-s) / s` for `s > 0`. -/
private lemma integral_rpow_tail_pi_neg_one (s : ℝ) (hs : 0 < s) :
    ∫ β in Ioi Real.pi, β ^ (-s - 1) = Real.pi ^ (-s) / s := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hy : (-s - 1 : ℝ) < -1 := by linarith
  have h := integral_Ioi_rpow_of_lt hy hπ
  have hrewrite : -Real.pi ^ (-s - 1 + 1) / (-s - 1 + 1) = Real.pi ^ (-s) / s := by
    have h1 : (-s - 1 + 1 : ℝ) = -s := by ring
    rw [h1]; rw [neg_div, ← div_neg]; congr 1; ring
  rw [h, hrewrite]

/-- Integrability of `√(β/π)·β^(-s-1) = (1/√π)·β^(-s-1/2)` on `Ioi π` for `s > 1/2`. -/
private lemma integrableOn_sqrt_over_pi_rpow (s : ℝ) (hs : 1/2 < s) :
    IntegrableOn (fun β : ℝ => Real.sqrt (β / Real.pi) * β ^ (-s - 1)) (Ioi Real.pi) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hsqrt_pi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hπ
  have hbase : IntegrableOn (fun β : ℝ => β ^ (-s - 1/2)) (Ioi Real.pi) := by
    apply integrableOn_Ioi_rpow_of_lt
    linarith
    exact hπ
  have hconst : IntegrableOn
      (fun β : ℝ => (1 / Real.sqrt Real.pi) * β ^ (-s - 1/2)) (Ioi Real.pi) :=
    hbase.const_mul _
  refine MeasureTheory.IntegrableOn.congr_fun hconst ?_ measurableSet_Ioi
  intro β hβ
  have hβ_pos : 0 < β := hπ.trans hβ
  have hβ_nn : (0:ℝ) ≤ β := hβ_pos.le
  show 1 / Real.sqrt Real.pi * β ^ (-s - 1/2) =
        Real.sqrt (β / Real.pi) * β ^ (-s - 1)
  rw [Real.sqrt_div hβ_nn]
  have hrpow_half : β ^ ((1:ℝ)/2) = Real.sqrt β := (Real.sqrt_eq_rpow _).symm
  rw [← hrpow_half]
  rw [show (β ^ ((1:ℝ)/2) / Real.sqrt Real.pi) = (1 / Real.sqrt Real.pi) * β ^ ((1:ℝ)/2) from
    by ring]
  rw [mul_assoc, ← Real.rpow_add hβ_pos]
  congr 2; ring

/-- Integrability of `β^(-s-1)` on `Ioi π` for `s > 0`. -/
private lemma integrableOn_rpow_neg_s_minus_one (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun β : ℝ => β ^ (-s - 1)) (Ioi Real.pi) := by
  apply integrableOn_Ioi_rpow_of_lt
  linarith
  exact Real.pi_pos

/-- **The elementary tail integral**. For `s > 1/2`:
    `∫_π^∞ (√(β/π) − 1) · β^(-s-1) dβ = π^(-s)/(s(2s-1))`. The individual pieces
    converge at `∞` by the rpow-integrability condition `y < -1` (here `-s-1/2 < -1`
    and `-s-1 < -1`); the difference collapses the two rpow integrals via algebraic
    simplification `1/(s-1/2) − 1/s = 1/(s(2s-1))`. -/
private lemma integral_sqrt_shift_tail (s : ℝ) (hs : 1/2 < s) :
    ∫ β in Ioi Real.pi, (Real.sqrt (β / Real.pi) - 1) * β ^ (-s - 1) =
      Real.pi ^ (-s) / (s * (2*s - 1)) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hs_pos : 0 < s := by linarith
  have hsqrt_pi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hπ
  have h_integrand_eq : ∀ β ∈ Ioi Real.pi,
      (Real.sqrt (β / Real.pi) - 1) * β ^ (-s - 1) =
      (1 / Real.sqrt Real.pi) * β ^ (-s - 1/2) - β ^ (-s - 1) := by
    intro β hβ
    have hβ_pos : 0 < β := hπ.trans hβ
    have hβ_nn : (0:ℝ) ≤ β := hβ_pos.le
    have hrpow_half : β ^ ((1:ℝ)/2) = Real.sqrt β := (Real.sqrt_eq_rpow _).symm
    have h_sqrt_div : Real.sqrt (β / Real.pi) = Real.sqrt β / Real.sqrt Real.pi := by
      rw [Real.sqrt_div hβ_nn]
    rw [h_sqrt_div]
    have h_sqrt_mul : Real.sqrt β / Real.sqrt Real.pi * β ^ (-s - 1) =
        (1 / Real.sqrt Real.pi) * β ^ (-s - 1/2) := by
      rw [← hrpow_half]
      rw [show (β ^ ((1:ℝ)/2) / Real.sqrt Real.pi) = (1 / Real.sqrt Real.pi) * β ^ ((1:ℝ)/2) from
        by ring]
      rw [mul_assoc, ← Real.rpow_add hβ_pos]
      congr 2; ring
    rw [sub_mul, one_mul, h_sqrt_mul]
  have h1 : IntegrableOn (fun β : ℝ => (1 / Real.sqrt Real.pi) * β ^ (-s - 1/2)) (Ioi Real.pi) := by
    have hbase : IntegrableOn (fun β : ℝ => β ^ (-s - 1/2)) (Ioi Real.pi) := by
      apply integrableOn_Ioi_rpow_of_lt
      · linarith
      · exact hπ
    exact hbase.const_mul _
  have h2 : IntegrableOn (fun β : ℝ => β ^ (-s - 1)) (Ioi Real.pi) :=
    integrableOn_rpow_neg_s_minus_one s hs_pos
  have h_rewrite : ∫ β in Ioi Real.pi, (Real.sqrt (β / Real.pi) - 1) * β ^ (-s - 1) =
      ∫ β in Ioi Real.pi, ((1 / Real.sqrt Real.pi) * β ^ (-s - 1/2) - β ^ (-s - 1)) := by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards with β hβ using h_integrand_eq β hβ
  rw [h_rewrite]
  rw [MeasureTheory.integral_sub h1 h2]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_rpow_tail_pi_neg_half s hs]
  rw [integral_rpow_tail_pi_neg_one s hs_pos]
  have h_sqrt_pi_rpow : Real.sqrt Real.pi = Real.pi ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow _
  have h_prod_simp : (1 : ℝ) / Real.sqrt Real.pi * Real.pi ^ ((1:ℝ)/2 - s) = Real.pi ^ (-s) := by
    rw [h_sqrt_pi_rpow, one_div, ← Real.rpow_neg hπ.le, ← Real.rpow_add hπ]
    congr 1; ring
  have hs_ne : s ≠ 0 := hs_pos.ne'
  have hs_half_ne : s - (1:ℝ)/2 ≠ 0 := by linarith
  have h2s_minus_one_ne : (2*s - 1 : ℝ) ≠ 0 := by linarith
  rw [show (1 : ℝ) / Real.sqrt Real.pi * (Real.pi ^ ((1:ℝ)/2 - s) / (s - (1:ℝ)/2))
        = (1 / Real.sqrt Real.pi * Real.pi ^ ((1:ℝ)/2 - s)) / (s - 1/2) from by ring,
      h_prod_simp]
  have h_combine : Real.pi ^ (-s) / (s - (1:ℝ)/2) - Real.pi ^ (-s) / s
                 = Real.pi ^ (-s) / (s * (2*s - 1)) := by
    rw [div_sub_div _ _ hs_half_ne hs_ne]
    rw [div_eq_div_iff (mul_ne_zero hs_half_ne hs_ne)
                       (mul_ne_zero hs_ne h2s_minus_one_ne)]
    ring
  exact h_combine

/-! ### The split identity and the Meno-side functional equation -/

/-- **The head integral via duality and sub-interval CoV**. For `s > 1/2`:

  `∫_[π,∞) (Z(π²/β) − 1) · β^(-s-1) dβ = (1/√π) · menoMellinTail(1/2 − s) + π^(-s)/(s(2s−1))`

    Applies `dual_partFn_sub_one_eq_residual` to expose the T-duality residual
    `√(β/π) · (Z(β) − 1) + (√(β/π) − 1)`, splits by linearity, and uses
    `integral_sqrt_shift_tail` for the elementary piece. -/
private lemma head_integral_eq_tail_pieces {s : ℝ} (hs : 1/2 < s) :
    ∫ β in Ici Real.pi, (scalarPartFn (Real.pi ^ 2 / β) - 1) * β ^ (-s - 1) =
      (1 / Real.sqrt Real.pi) * menoMellinTail (1/2 - s)
        + Real.pi ^ (-s) / (s * (2*s - 1)) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπ_le : (0 : ℝ) ≤ Real.pi := hπ.le
  have hsqrt_pi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hπ
  have hsqrt_pi_ne : Real.sqrt Real.pi ≠ 0 := hsqrt_pi_pos.ne'
  have hs_pos : 0 < s := by linarith
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  -- Pointwise identity via duality
  have h_pointwise : ∀ β ∈ Ioi Real.pi,
      (scalarPartFn (Real.pi ^ 2 / β) - 1) * β ^ (-s - 1)
    = (1 / Real.sqrt Real.pi) *
        ((scalarPartFn β - 1) * β ^ ((1/2 - s) - 1))
    + (Real.sqrt (β / Real.pi) - 1) * β ^ (-s - 1) := by
    intro β hβ
    have hβ_pos : 0 < β := hπ.trans hβ
    have hβ_nn : (0 : ℝ) ≤ β := hβ_pos.le
    rw [dual_partFn_sub_one_eq_residual β hβ_pos]
    have h_sqrt_mul : Real.sqrt (β / Real.pi) * β ^ (-s - 1)
                    = (1 / Real.sqrt Real.pi) * β ^ ((1/2 - s) - 1) := by
      rw [Real.sqrt_div hβ_nn]
      have hβ_half : Real.sqrt β = β ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow _
      rw [hβ_half]
      rw [show β ^ ((1:ℝ)/2) / Real.sqrt Real.pi * β ^ (-s - 1)
            = (1 / Real.sqrt Real.pi) * (β ^ ((1:ℝ)/2) * β ^ (-s - 1)) from by ring]
      rw [← Real.rpow_add hβ_pos]
      congr 2; ring
    -- Now the goal after unfolding duality is:
    -- (√(β/π)·(Z(β)-1) + (√(β/π)-1)) · β^(-s-1)
    --   = (1/√π)·((Z(β)-1)·β^((1/2-s)-1)) + (√(β/π)-1)·β^(-s-1)
    have h_expand :
        (Real.sqrt (β / Real.pi) * (scalarPartFn β - 1) +
          (Real.sqrt (β / Real.pi) - 1)) * β ^ (-s - 1) =
        Real.sqrt (β / Real.pi) * β ^ (-s - 1) * (scalarPartFn β - 1)
        + (Real.sqrt (β / Real.pi) - 1) * β ^ (-s - 1) := by ring
    rw [h_expand, h_sqrt_mul]
    ring
  -- Integrabilities
  have hint_half_s : IntegrableOn
      (fun β : ℝ => (1 / Real.sqrt Real.pi) *
        ((scalarPartFn β - 1) * β ^ ((1/2 - s) - 1))) (Ioi Real.pi) :=
    (menoMellinTail_integrableOn (1/2 - s)).const_mul _
  have hint_sqrt : IntegrableOn
      (fun β : ℝ => Real.sqrt (β / Real.pi) * β ^ (-s - 1)) (Ioi Real.pi) :=
    integrableOn_sqrt_over_pi_rpow s hs
  have hint_rpow : IntegrableOn (fun β : ℝ => β ^ (-s - 1)) (Ioi Real.pi) :=
    integrableOn_rpow_neg_s_minus_one s hs_pos
  have hint_shift : IntegrableOn
      (fun β : ℝ => (Real.sqrt (β / Real.pi) - 1) * β ^ (-s - 1)) (Ioi Real.pi) := by
    have hsub := hint_sqrt.sub hint_rpow
    refine MeasureTheory.IntegrableOn.congr_fun hsub ?_ measurableSet_Ioi
    intro β _
    show Real.sqrt (β / Real.pi) * β ^ (-s - 1) - β ^ (-s - 1)
       = (Real.sqrt (β / Real.pi) - 1) * β ^ (-s - 1)
    ring
  -- Apply pointwise rewrite, then linearity
  rw [show ∫ β in Ioi Real.pi, (scalarPartFn (Real.pi ^ 2 / β) - 1) * β ^ (-s - 1)
        = ∫ β in Ioi Real.pi,
            ((1 / Real.sqrt Real.pi) *
              ((scalarPartFn β - 1) * β ^ ((1/2 - s) - 1))
            + (Real.sqrt (β / Real.pi) - 1) * β ^ (-s - 1)) from by
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards with β hβ using h_pointwise β hβ]
  rw [MeasureTheory.integral_add hint_half_s hint_shift]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_sqrt_shift_tail s hs]
  rfl

/-- **Riemann 1859 split at `α = π`**. For `s > 1/2`:

  `menoMellin s = menoMellinTail s + π^(2s−1/2) · menoMellinTail (1/2 − s) + π^s / (s(2s−1))`

    The `(0, π]` head folds onto `[π, ∞)` via `menoMellin_head_cov_pi_sq`, producing
    an integral of `(Z(π²/β) − 1) · β^(-s-1)`. The integrand is decomposed via
    `dual_partFn_sub_one_eq_residual` into `√(β/π) · (Z(β) − 1) + (√(β/π) − 1)`.
    The first piece contributes `π^(2s − 1/2) · menoMellinTail (1/2 − s)`, the second
    the elementary `π^s / (s(2s − 1))`. -/
theorem menoMellin_split_at_pi {s : ℝ} (hs : 1/2 < s) :
    menoMellin s = menoMellinTail s
                 + Real.pi ^ (2*s - 1/2) * menoMellinTail (1/2 - s)
                 + Real.pi ^ s / (s * (2*s - 1)) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hπ_le : (0 : ℝ) ≤ Real.pi := hπ.le
  have hsqrt_pi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hπ
  have hsqrt_pi_rpow : Real.sqrt Real.pi = Real.pi ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow _
  have hs_pos : 0 < s := by linarith
  -- Integrability on Ioc 0 π via CoV transfer
  have h_deriv : ∀ β ∈ Ici Real.pi, HasDerivWithinAt (fun β' : ℝ => Real.pi ^ 2 / β')
      (-(Real.pi ^ 2 / β ^ 2)) (Ici Real.pi) β :=
    fun β hβ => hasDerivWithinAt_pi_sq_div β hβ
  -- Integrability hypotheses on Ici π for the transformed integrand
  have hint_transformed_Ioi : IntegrableOn
      (fun β : ℝ => Real.pi ^ (2*s) *
        ((scalarPartFn (Real.pi ^ 2 / β) - 1) * β ^ (-s - 1))) (Ioi Real.pi) := by
    -- Apply pointwise identity, then linearity
    have h_pt : ∀ β ∈ Ioi Real.pi,
        Real.pi ^ (2*s) *
          ((scalarPartFn (Real.pi ^ 2 / β) - 1) * β ^ (-s - 1)) =
        Real.pi ^ (2*s) * (1 / Real.sqrt Real.pi) *
          ((scalarPartFn β - 1) * β ^ ((1/2 - s) - 1))
        + Real.pi ^ (2*s) *
          ((Real.sqrt (β / Real.pi) - 1) * β ^ (-s - 1)) := by
      intro β hβ
      have hβ_pos : 0 < β := hπ.trans hβ
      have hβ_nn : (0 : ℝ) ≤ β := hβ_pos.le
      rw [dual_partFn_sub_one_eq_residual β hβ_pos]
      have h_sqrt_mul : Real.sqrt (β / Real.pi) * β ^ (-s - 1)
                      = (1 / Real.sqrt Real.pi) * β ^ ((1/2 - s) - 1) := by
        rw [Real.sqrt_div hβ_nn]
        have hβ_half : Real.sqrt β = β ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow _
        rw [hβ_half]
        rw [show β ^ ((1:ℝ)/2) / Real.sqrt Real.pi * β ^ (-s - 1)
              = (1 / Real.sqrt Real.pi) * (β ^ ((1:ℝ)/2) * β ^ (-s - 1)) from by ring]
        rw [← Real.rpow_add hβ_pos]
        congr 2; ring
      have h_expand :
          Real.pi ^ (2*s) *
            ((Real.sqrt (β / Real.pi) * (scalarPartFn β - 1) +
              (Real.sqrt (β / Real.pi) - 1)) * β ^ (-s - 1)) =
          Real.pi ^ (2*s) * (Real.sqrt (β / Real.pi) * β ^ (-s - 1)) *
            (scalarPartFn β - 1)
          + Real.pi ^ (2*s) *
            ((Real.sqrt (β / Real.pi) - 1) * β ^ (-s - 1)) := by ring
      rw [h_expand, h_sqrt_mul]
      ring
    have hint_A : IntegrableOn
        (fun β : ℝ => Real.pi ^ (2*s) * (1 / Real.sqrt Real.pi) *
          ((scalarPartFn β - 1) * β ^ ((1/2 - s) - 1))) (Ioi Real.pi) :=
      (menoMellinTail_integrableOn (1/2 - s)).const_mul _
    have hint_B : IntegrableOn
        (fun β : ℝ => Real.pi ^ (2*s) *
          ((Real.sqrt (β / Real.pi) - 1) * β ^ (-s - 1))) (Ioi Real.pi) := by
      have h_sub : IntegrableOn
          (fun β : ℝ => Real.sqrt (β / Real.pi) * β ^ (-s - 1) - β ^ (-s - 1))
          (Ioi Real.pi) :=
        (integrableOn_sqrt_over_pi_rpow s hs).sub (integrableOn_rpow_neg_s_minus_one s hs_pos)
      have hint_shift_raw : IntegrableOn
          (fun β : ℝ => (Real.sqrt (β / Real.pi) - 1) * β ^ (-s - 1)) (Ioi Real.pi) := by
        refine h_sub.congr_fun ?_ measurableSet_Ioi
        intro β _; ring
      exact hint_shift_raw.const_mul _
    refine MeasureTheory.IntegrableOn.congr_fun (hint_A.add hint_B) ?_ measurableSet_Ioi
    intro β hβ; exact (h_pt β hβ).symm
  have hint_transformed_Ici : IntegrableOn
      (fun β : ℝ => Real.pi ^ (2*s) *
        ((scalarPartFn (Real.pi ^ 2 / β) - 1) * β ^ (-s - 1))) (Ici Real.pi) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hint_transformed_Ioi
  -- Transfer integrability via CoV iff
  have hint_head_Ioc : IntegrableOn
      (fun α : ℝ => (scalarPartFn α - 1) * α ^ (s - 1)) (Ioc 0 Real.pi) := by
    have h_iff := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      (measurableSet_Ici (a := Real.pi)) h_deriv injOn_pi_sq_div
      (fun α : ℝ => (scalarPartFn α - 1) * α ^ (s - 1))
    rw [image_pi_sq_div_Ici_pi] at h_iff
    apply h_iff.mpr
    refine hint_transformed_Ici.congr_fun ?_ measurableSet_Ici
    intro β hβ
    have hβ_ge : Real.pi ≤ β := hβ
    have hβ_pos : 0 < β := hπ.trans_le hβ_ge
    have hβ2_pos : 0 < β ^ 2 := sq_pos_of_pos hβ_pos
    show Real.pi ^ (2*s) *
        ((scalarPartFn (Real.pi ^ 2 / β) - 1) * β ^ (-s - 1)) =
      |-(Real.pi ^ 2 / β ^ 2)| •
        ((scalarPartFn (Real.pi ^ 2 / β) - 1) * (Real.pi ^ 2 / β) ^ (s - 1))
    rw [smul_eq_mul, abs_neg, abs_of_pos (div_pos (sq_pos_of_pos hπ) hβ2_pos)]
    have hid := cov_rpow_identity β hβ_pos s
    set Z := scalarPartFn (Real.pi ^ 2 / β) - 1 with hZ
    calc Real.pi ^ (2*s) * (Z * β ^ (-s - 1))
        = (Real.pi ^ (2*s) * β ^ (-s - 1)) * Z := by ring
      _ = ((Real.pi ^ 2 / β ^ 2) * (Real.pi ^ 2 / β) ^ (s - 1)) * Z := by rw [← hid]
      _ = (Real.pi ^ 2 / β ^ 2) * (Z * (Real.pi ^ 2 / β) ^ (s - 1)) := by ring
  -- Tail integrability
  have hint_tail_s : IntegrableOn
      (fun α : ℝ => (scalarPartFn α - 1) * α ^ (s - 1)) (Ioi Real.pi) :=
    menoMellinTail_integrableOn s
  -- Split Ioi 0 = Ioc 0 π ∪ Ioi π
  have hdisj : Disjoint (Ioc (0:ℝ) Real.pi) (Ioi Real.pi) :=
    Set.Ioc_disjoint_Ioi_same
  have hunion : Ioc (0:ℝ) Real.pi ∪ Ioi Real.pi = Ioi 0 :=
    Set.Ioc_union_Ioi_eq_Ioi hπ.le
  -- Main computation
  unfold menoMellin
  rw [← hunion]
  rw [MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hint_head_Ioc hint_tail_s]
  rw [menoMellin_head_cov_pi_sq s]
  rw [head_integral_eq_tail_pieces hs]
  -- Current: π^(2s) * ((1/√π) * menoMellinTail(1/2-s) + π^(-s)/(s*(2s-1))) + menoMellinTail s
  --     = menoMellinTail s + π^(2s-1/2) * menoMellinTail(1/2-s) + π^s/(s*(2s-1))
  rw [show Real.pi ^ (2*s) *
        ((1 / Real.sqrt Real.pi) * menoMellinTail (1/2 - s) +
          Real.pi ^ (-s) / (s * (2*s - 1)))
        = Real.pi ^ (2*s) * (1 / Real.sqrt Real.pi) * menoMellinTail (1/2 - s) +
          Real.pi ^ (2*s) * (Real.pi ^ (-s) / (s * (2*s - 1))) from by ring]
  have h_pi_factor : Real.pi ^ (2*s) * (1 / Real.sqrt Real.pi) = Real.pi ^ (2*s - 1/2) := by
    rw [hsqrt_pi_rpow, one_div, ← Real.rpow_neg hπ.le, ← Real.rpow_add hπ]
    ring_nf
  have h_pi_s : Real.pi ^ (2*s) * Real.pi ^ (-s) = Real.pi ^ s := by
    rw [← Real.rpow_add hπ]; congr 1; ring
  rw [h_pi_factor]
  rw [show Real.pi ^ (2*s) * (Real.pi ^ (-s) / (s * (2*s - 1)))
        = (Real.pi ^ (2*s) * Real.pi ^ (-s)) / (s * (2*s - 1)) from by ring,
      h_pi_s]
  show Real.pi ^ (2*s - 1/2) * menoMellinTail (1/2 - s) + Real.pi ^ s / (s * (2*s - 1))
       + menoMellinTail s =
       menoMellinTail s + Real.pi ^ (2*s - 1/2) * menoMellinTail (1/2 - s)
       + Real.pi ^ s / (s * (2*s - 1))
  ring

/-- **Completed Meno-Mellin** on `(π, ∞)`: the concrete functional whose
    `π^(-s)`-weighted completion is symmetric under `s ↔ 1/2 − s`. On the
    convergence regime `1/2 < s`, `menoMellinC s = menoMellin s` by the
    Riemann-1859 split (`menoMellin_split_at_pi`); on the reflected regime
    `1/2 − s < 1/2` (where the classical `menoMellin (1/2 − s)` is divergent),
    `menoMellinC` provides its analytic-continuation image — `menoMellinTail`
    converges for every real exponent.

    **Structural status**: `menoMellinC` is defined entirely from `menoMellinTail`
    and elementary π-powers. No `riemannZeta` appears in the definition. -/
noncomputable def menoMellinC (t : ℝ) : ℝ :=
  menoMellinTail t + Real.pi ^ (2*t - 1/2) * menoMellinTail (1/2 - t)
    + Real.pi ^ t / (t * (2*t - 1))

/-- **Functional equation**: the `π^(-s)`-completion of `menoMellin s` equals the
    `π^(-(1/2 − s))`-completion of `menoMellinC (1/2 − s)` — the Riemann symmetry
    under `s ↔ 1/2 − s`. Obtained by rewriting `menoMellin s` to `menoMellinC s`
    via `menoMellin_split_at_pi`, then applying the algebraic `s ↔ 1/2 − s`
    symmetry of `menoMellinC`. -/
theorem menoMellin_functional_equation {s : ℝ} (hs : 1/2 < s) :
    Real.pi ^ (-s) * menoMellin s =
      Real.pi ^ (-(1/2 - s)) * menoMellinC (1/2 - s) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have h_split : menoMellin s = menoMellinC s := by
    unfold menoMellinC
    exact menoMellin_split_at_pi hs
  rw [h_split]
  unfold menoMellinC
  -- Algebraic s ↔ 1/2 − s symmetry of menoMellinC.
  have hs_sub : (1:ℝ)/2 - (1/2 - s) = s := by ring
  rw [hs_sub]
  have hL1 : Real.pi ^ (-s) * Real.pi ^ (2*s - 1/2) = Real.pi ^ (s - 1/2) := by
    rw [← Real.rpow_add hπ]; congr 1; ring
  have hL2 : Real.pi ^ (-s) * Real.pi ^ s = 1 := by
    rw [← Real.rpow_add hπ, show -s + s = (0:ℝ) from by ring, Real.rpow_zero]
  have hR1 : Real.pi ^ (-(1/2 - s)) = Real.pi ^ (s - 1/2) := by
    congr 1; ring
  have hR2 : Real.pi ^ (s - 1/2) * Real.pi ^ (2 * (1/2 - s) - 1/2) = Real.pi ^ (-s) := by
    rw [← Real.rpow_add hπ]; congr 1; ring
  have hR3 : Real.pi ^ (s - 1/2) * Real.pi ^ (1/2 - s) = 1 := by
    rw [← Real.rpow_add hπ, show (s - 1/2) + (1/2 - s) = (0:ℝ) from by ring, Real.rpow_zero]
  have h_denom : (1/2 - s) * (2 * (1/2 - s) - 1) = s * (2*s - 1) := by ring
  rw [hR1, mul_add, mul_add, mul_add, mul_add,
      mul_div_assoc' (Real.pi ^ (-s)) (Real.pi ^ s) (s * (2*s - 1)),
      mul_div_assoc' (Real.pi ^ (s - 1/2)) (Real.pi ^ (1/2 - s)) ((1/2 - s) * (2 * (1/2 - s) - 1)),
      ← mul_assoc (Real.pi ^ (-s)) (Real.pi ^ (2*s - 1/2)),
      ← mul_assoc (Real.pi ^ (s - 1/2)) (Real.pi ^ (2 * (1/2 - s) - 1/2)),
      hL1, hL2, hR2, hR3, h_denom]
  ring

/-- **Functional equation** (completion form): the `π^(-s)`-completion of
    `2·Γ(s)·ζ(2s)` equals the `π^(-(1/2 − s))`-completion of `menoMellinC (1/2 − s)`.
    Obtained by casting `menoMellin_functional_equation` to ℂ and applying the
    Mellin-ζ bridge `menoMellin_cast_eq_riemannZeta_real`. -/
theorem meno_zeta_functional_equation_real {s : ℝ} (hs : 1/2 < s) :
    (Real.pi : ℂ) ^ (-(s : ℂ)) *
      ((2 : ℂ) * Complex.Gamma (s : ℂ) * riemannZeta (2 * (s : ℂ))) =
    (Real.pi : ℂ) ^ (-((1/2 : ℂ) - (s : ℂ))) *
      ((menoMellinC (1/2 - s) : ℝ) : ℂ) := by
  have hπ : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hFE_real := menoMellin_functional_equation hs
  have hbridge := menoMellin_cast_eq_riemannZeta_real hs
  rw [← hbridge]
  have h := congrArg (Complex.ofReal : ℝ → ℂ) hFE_real
  simp only [Complex.ofReal_mul] at h
  rw [show ((Real.pi ^ (-s) : ℝ) : ℂ) = (Real.pi : ℂ) ^ (-(s : ℂ)) from by
        rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) from by norm_cast]
        exact Complex.ofReal_cpow hπ _] at h
  rw [show ((Real.pi ^ (-(1/2 - s)) : ℝ) : ℂ) =
           (Real.pi : ℂ) ^ (-((1/2 : ℂ) - (s : ℂ))) from by
        rw [show (-((1/2 : ℂ) - (s : ℂ))) = ((-(1/2 - s) : ℝ) : ℂ) from by push_cast; ring]
        exact Complex.ofReal_cpow hπ _] at h
  exact h

end Meno
