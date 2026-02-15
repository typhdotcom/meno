import Meno.Groupoid
import Meno.Theta
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Fourier Duality on GroupoidObj

Lifts the analytic T-duality (Theta.lean) to a structural operation on GroupoidObj:
for quadratic energy α·k² on ℤ-endomorphisms, the Fourier dual has coupling π²/α.
The dual construction is involutive. -/

namespace Simplicial

open UpperHalfPlane CategoryTheory

/-! ## Generalized quadratic partition function -/

noncomputable def quadraticPartFn (α : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp (-α * (k : ℝ) ^ 2)

private lemma summable_quadraticPartFn_nat (α : ℝ) (hα : 0 < α) :
    Summable (fun i : ℕ => Real.exp (-α * (↑i : ℝ) ^ 2)) := by
  have hle : ∀ i : ℕ, (↑i : ℝ) ≤ (↑i : ℝ) ^ 2 := by
    intro i; rcases i with _ | i
    · simp
    · nlinarith [sq_nonneg ((↑(i + 1) : ℝ) - 1),
        show (1 : ℝ) ≤ ↑(i + 1) from by exact_mod_cast Nat.succ_pos i]
  exact (Real.summable_exp_nat_mul_of_ge (neg_neg_of_pos hα)
    (f := fun i => (↑i : ℝ) ^ 2) hle).congr fun i => by congr 1

theorem summable_quadraticPartFn (α : ℝ) (hα : 0 < α) :
    Summable (fun k : ℤ => Real.exp (-α * (k : ℝ) ^ 2)) :=
  .of_nat_of_neg (summable_quadraticPartFn_nat α hα)
    ((summable_quadraticPartFn_nat α hα).congr fun i => by push_cast; congr 1; ring)

theorem quadraticPartFn_eq_partitionFn (n : ℕ) (hn : n ≥ 3) :
    quadraticPartFn (1 / ↑n) = partitionFn n hn := by
  simp only [quadraticPartFn, partitionFn]; congr 1; ext k; congr 1; ring

/-! ## Generalized T-duality via modular S-transformation -/

private noncomputable def quadTau (α : ℝ) : ℂ :=
  Complex.I * ↑α / ↑Real.pi

private lemma quad_tau_im_pos (α : ℝ) (hα : 0 < α) : (quadTau α).im > 0 := by
  unfold quadTau
  rw [mul_div_assoc, ← Complex.ofReal_div, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  simp only [zero_mul, one_mul, zero_add]
  exact div_pos hα Real.pi_pos

private noncomputable def quadUHP (α : ℝ) (hα : 0 < α) : UpperHalfPlane :=
  ⟨quadTau α, quad_tau_im_pos α hα⟩

private lemma quad_theta_exponent (α : ℝ) (k : ℤ) :
    ↑Real.pi * Complex.I * (↑k : ℂ) ^ 2 * quadTau α =
    ↑(-α * (k : ℝ) ^ 2) := by
  simp only [quadTau]
  have hpi : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  push_cast; field_simp; rw [Complex.I_sq]; ring

private theorem quadraticPartFn_eq_jacobiTheta (α : ℝ) :
    (↑(quadraticPartFn α) : ℂ) = jacobiTheta (quadTau α) := by
  simp only [quadraticPartFn, jacobiTheta]
  rw [Complex.ofReal_tsum]
  congr 1; ext k
  rw [quad_theta_exponent α k, ← Complex.ofReal_exp]

private theorem quad_S_transform (α : ℝ) (hα : 0 < α) :
    (↑(ModularGroup.S • quadUHP α hα) : ℂ) = quadTau (Real.pi ^ 2 / α) := by
  have h : (↑(quadUHP α hα) : ℂ) = quadTau α := rfl
  rw [modular_S_smul, coe_mk, h]
  simp only [quadTau]
  have hpi : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  have hα0 : (↑α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hα)
  push_cast; field_simp; exact Complex.I_sq.symm

private theorem quad_prefactor (α : ℝ) (hα : 0 < α) :
    -Complex.I * (↑(quadUHP α hα) : ℂ) = ↑(α / Real.pi : ℝ) := by
  have : (↑(quadUHP α hα) : ℂ) = quadTau α := rfl
  rw [this]; simp only [quadTau]
  have hpi : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  push_cast; field_simp; rw [Complex.I_sq]; ring

theorem quadraticPartFn_duality (α : ℝ) (hα : 0 < α) :
    (↑(quadraticPartFn (Real.pi ^ 2 / α)) : ℂ) =
    ↑(α / Real.pi : ℝ) ^ ((1 : ℂ) / 2) * ↑(quadraticPartFn α) := by
  have hτ : (↑(quadUHP α hα) : ℂ) = quadTau α := rfl
  rw [quadraticPartFn_eq_jacobiTheta, quadraticPartFn_eq_jacobiTheta,
      show quadTau (Real.pi ^ 2 / α) = ↑(ModularGroup.S • quadUHP α hα) from
        (quad_S_transform α hα).symm,
      jacobiTheta_S_smul, quad_prefactor α hα, hτ]

/-! ## Fourier dual of a GroupoidObj -/

noncomputable def GroupoidObj.dual
    (E : GroupoidObj) (wind : End E.base ≃ ℤ) (α : ℝ) (hα : 0 < α)
    (_hK : ∀ g, E.energy g = α * (wind g : ℝ) ^ 2) : GroupoidObj where
  G := E.G
  base := E.base
  energy g := (Real.pi ^ 2 / α) * (wind g : ℝ) ^ 2
  summable := by
    have h := summable_quadraticPartFn (Real.pi ^ 2 / α)
      (div_pos (sq_pos_of_pos Real.pi_pos) hα)
    exact (wind.summable_iff.mpr h).congr fun g => by simp only [Function.comp_apply, neg_mul]

private theorem partFn_eq_quadraticPartFn
    (E : GroupoidObj) (wind : End E.base ≃ ℤ) (α : ℝ)
    (hK : ∀ g, E.energy g = α * (wind g : ℝ) ^ 2) :
    E.partFn = quadraticPartFn α := by
  unfold GroupoidObj.partFn groupoidPartitionFn quadraticPartFn
  conv_lhs =>
    rw [show (fun g => Real.exp (-E.energy g)) =
        (fun k : ℤ => Real.exp (-α * (k : ℝ) ^ 2)) ∘ wind from by
      ext g; simp only [Function.comp_apply]; rw [hK g]; ring_nf]
  exact Equiv.tsum_eq wind (fun k : ℤ => Real.exp (-α * (k : ℝ) ^ 2))

theorem GroupoidObj.dual_partFn
    (E : GroupoidObj) (wind : End E.base ≃ ℤ) (α : ℝ) (hα : 0 < α)
    (hK : ∀ g, E.energy g = α * (wind g : ℝ) ^ 2) :
    (↑((E.dual wind α hα hK).partFn) : ℂ) =
    ↑(α / Real.pi : ℝ) ^ ((1 : ℂ) / 2) * ↑E.partFn := by
  have hK' : ∀ g, (E.dual wind α hα hK).energy g = (Real.pi ^ 2 / α) * (wind g : ℝ) ^ 2 :=
    fun g => rfl
  rw [partFn_eq_quadraticPartFn (E.dual wind α hα hK) wind _ hK']
  rw [partFn_eq_quadraticPartFn E wind α hK]
  exact quadraticPartFn_duality α hα

theorem GroupoidObj.dual_dual_equiv
    (E : GroupoidObj) (wind : End E.base ≃ ℤ) (α : ℝ) (hα : 0 < α)
    (hK : ∀ g, E.energy g = α * (wind g : ℝ) ^ 2) :
    GroupoidObj.Equiv
      ((E.dual wind α hα hK).dual wind (Real.pi ^ 2 / α)
        (div_pos (sq_pos_of_pos Real.pi_pos) hα) (fun _ => rfl))
      E := by
  refine ⟨Equiv.refl _, fun _ => ?_⟩
  simp only [Equiv.refl_apply, GroupoidObj.dual]
  rw [hK]; congr 1
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hpi0 : Real.pi ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos Real.pi_pos)
  field_simp

/-! ## Complexity-Rank Bound

T-duality converts the vacuum bound Z ≥ 1 into a nontrivial lower bound on
the partition function: Z(α) ≥ √(π/α). Taking logs gives a complexity floor
that grows with topological rank. -/

theorem quadraticPartFn_gt_one (α : ℝ) (hα : 0 < α) : quadraticPartFn α > 1 := by
  have hsm := summable_quadraticPartFn α hα
  have hle : ({0, 1} : Finset ℤ).sum (fun k => Real.exp (-α * (k : ℝ) ^ 2)) ≤
      quadraticPartFn α := by
    show _ ≤ ∑' k, _
    exact hsm.sum_le_tsum {0, 1} (fun k _ => le_of_lt (Real.exp_pos _))
  simp at hle
  linarith [Real.exp_pos (-α)]

theorem quadraticPartFn_duality_real (α : ℝ) (hα : 0 < α) :
    quadraticPartFn (Real.pi ^ 2 / α) =
    (α / Real.pi) ^ ((1 : ℝ) / 2) * quadraticPartFn α := by
  have h := quadraticPartFn_duality α hα
  have hnn : (0 : ℝ) ≤ α / Real.pi := le_of_lt (div_pos hα Real.pi_pos)
  apply Complex.ofReal_inj.mp
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hnn]
  convert h using 2
  push_cast; ring

theorem quadraticPartFn_lower_bound (α : ℝ) (hα : 0 < α) :
    quadraticPartFn α ≥ (Real.pi / α) ^ ((1 : ℝ) / 2) := by
  have hαπ : 0 < α / Real.pi := div_pos hα Real.pi_pos
  have hge := le_of_lt (quadraticPartFn_gt_one (Real.pi ^ 2 / α)
    (div_pos (sq_pos_of_pos Real.pi_pos) hα))
  rw [quadraticPartFn_duality_real α hα] at hge
  have hprod : (Real.pi / α) ^ ((1:ℝ)/2) * (α / Real.pi) ^ ((1:ℝ)/2) = 1 := by
    rw [← Real.mul_rpow (le_of_lt (div_pos Real.pi_pos hα)) (le_of_lt hαπ)]
    have : Real.pi / α * (α / Real.pi) = 1 := by field_simp
    rw [this, Real.one_rpow]
  nlinarith [Real.rpow_pos_of_pos (div_pos Real.pi_pos hα) ((1:ℝ)/2),
             mul_comm ((α / Real.pi) ^ ((1:ℝ)/2)) (quadraticPartFn α)]

theorem complexity_rank_bound (α : ℝ) (hα : 0 < α) :
    Real.log (quadraticPartFn α) ≥ (1 / 2) * Real.log (Real.pi / α) := by
  have hπα : 0 < Real.pi / α := div_pos Real.pi_pos hα
  calc Real.log (quadraticPartFn α)
      ≥ Real.log ((Real.pi / α) ^ ((1 : ℝ) / 2)) :=
        Real.log_le_log (Real.rpow_pos_of_pos hπα _) (quadraticPartFn_lower_bound α hα)
    _ = (1 / 2) * Real.log (Real.pi / α) :=
        Real.log_rpow hπα _

theorem GroupoidObj.complexity_ge (E : GroupoidObj) (wind : End E.base ≃ ℤ)
    (α : ℝ) (hα : 0 < α) (hK : ∀ g, E.energy g = α * (wind g : ℝ) ^ 2) :
    E.complexity ≥ (1 / 2) * Real.log (Real.pi / α) := by
  simp only [GroupoidObj.complexity, groupoidComplexity]
  rw [show groupoidPartitionFn E.base E.energy E.summable = quadraticPartFn α from
    partFn_eq_quadraticPartFn E wind α hK]
  exact complexity_rank_bound α hα

theorem cycle_complexity_ge (E : GroupoidObj) (wind : End E.base ≃ ℤ)
    (n : ℕ) (hn : 0 < n) (hK : ∀ g, E.energy g = (wind g : ℝ) ^ 2 / n) :
    E.complexity ≥ (1 / 2) * Real.log (Real.pi * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hα : (0 : ℝ) < 1 / n := div_pos one_pos hn0
  have hK' : ∀ g, E.energy g = (1 / ↑n) * (wind g : ℝ) ^ 2 := fun g => by rw [hK]; ring
  have h := GroupoidObj.complexity_ge E wind (1 / ↑n) hα hK'
  convert h using 2
  have : (0 : ℝ) < n := hn0
  field_simp

theorem rank_complexity_bound (E₁ E₂ : GroupoidObj)
    (wind₁ : End E₁.base ≃ ℤ) (wind₂ : End E₂.base ≃ ℤ)
    (n₁ n₂ : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hK₁ : ∀ g, E₁.energy g = (wind₁ g : ℝ) ^ 2 / n₁)
    (hK₂ : ∀ g, E₂.energy g = (wind₂ g : ℝ) ^ 2 / n₂) :
    (E₁.prod E₂).complexity ≥
    (1 / 2) * Real.log (Real.pi * n₁) + (1 / 2) * Real.log (Real.pi * n₂) := by
  rw [GroupoidObj.prod_complexity]
  exact add_le_add (cycle_complexity_ge E₁ wind₁ n₁ hn₁ hK₁)
                   (cycle_complexity_ge E₂ wind₂ n₂ hn₂ hK₂)

/-! ## Complexity Decomposition

The duality identity decomposes complexity into a topological part
(1/2)·log(π/α), determined by the coupling alone, plus a strictly positive
dual residual log(Z(π²/α)) that vanishes exponentially as α → 0. -/

theorem complexity_decomposition (α : ℝ) (hα : 0 < α) :
    Real.log (quadraticPartFn α) =
    (1 / 2) * Real.log (Real.pi / α) +
    Real.log (quadraticPartFn (Real.pi ^ 2 / α)) := by
  have hαπ : 0 < α / Real.pi := div_pos hα Real.pi_pos
  have hπα : 0 < Real.pi / α := div_pos Real.pi_pos hα
  have hZ : 0 < quadraticPartFn α := lt_trans one_pos (quadraticPartFn_gt_one α hα)
  have hpf : 0 < (α / Real.pi) ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hαπ _
  have hlog : Real.log (quadraticPartFn (Real.pi ^ 2 / α)) =
      (1/2) * Real.log (α / Real.pi) + Real.log (quadraticPartFn α) := by
    rw [quadraticPartFn_duality_real α hα,
        Real.log_mul (ne_of_gt hpf) (ne_of_gt hZ), Real.log_rpow hαπ]
  have hsum : Real.log (Real.pi / α) + Real.log (α / Real.pi) = 0 := by
    rw [← Real.log_mul (ne_of_gt hπα) (ne_of_gt hαπ)]
    have : Real.pi / α * (α / Real.pi) = 1 := by field_simp
    rw [this, Real.log_one]
  linarith

theorem complexity_gap_pos (α : ℝ) (hα : 0 < α) :
    Real.log (quadraticPartFn (Real.pi ^ 2 / α)) > 0 :=
  Real.log_pos (quadraticPartFn_gt_one _ (div_pos (sq_pos_of_pos Real.pi_pos) hα))

/-! ## Self-Dual Fixed Point

At coupling α = π, the dual coupling π²/α = π. The object is its own
Fourier dual — the description and its dual description coincide. -/

theorem GroupoidObj.self_dual (E : GroupoidObj) (wind : End E.base ≃ ℤ)
    (hK : ∀ g, E.energy g = Real.pi * (wind g : ℝ) ^ 2) :
    GroupoidObj.Equiv (E.dual wind Real.pi Real.pi_pos hK) E := by
  refine ⟨Equiv.refl _, fun g => ?_⟩
  simp only [Equiv.refl_apply, GroupoidObj.dual, hK]
  have : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

/-- The self-dual coupling is unique: Z(π²/α) = Z(α) if and only if α = π. -/
theorem quadraticPartFn_self_dual_iff (α : ℝ) (hα : 0 < α) :
    quadraticPartFn (Real.pi ^ 2 / α) = quadraticPartFn α ↔ α = Real.pi := by
  constructor
  · intro h
    have hdual := quadraticPartFn_duality_real α hα
    rw [h] at hdual
    have hαπ : 0 < α / Real.pi := div_pos hα Real.pi_pos
    have hZpos : 0 < quadraticPartFn α :=
      lt_trans zero_lt_one (quadraticPartFn_gt_one α hα)
    have hlog := congr_arg Real.log hdual
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hαπ _)) (ne_of_gt hZpos),
        Real.log_rpow hαπ] at hlog
    have : Real.log (α / Real.pi) = 0 := by linarith
    rcases Real.log_eq_zero.mp this with h3 | h3 | h3
    · linarith
    · linarith [(div_eq_iff (ne_of_gt Real.pi_pos)).mp h3]
    · linarith
  · intro h; subst h
    show quadraticPartFn (Real.pi ^ 2 / Real.pi) = quadraticPartFn Real.pi
    congr 1; have : Real.pi ≠ 0 := ne_of_gt Real.pi_pos; field_simp

/-- Sub-critical regime: the dual has smaller partition function iff α < π. -/
theorem dual_partFn_lt_iff (α : ℝ) (hα : 0 < α) :
    quadraticPartFn (Real.pi ^ 2 / α) < quadraticPartFn α ↔ α < Real.pi := by
  have hdual := quadraticPartFn_duality_real α hα
  have hZpos : 0 < quadraticPartFn α :=
    lt_trans zero_lt_one (quadraticPartFn_gt_one α hα)
  have hαπ : 0 < α / Real.pi := div_pos hα Real.pi_pos
  rw [hdual, mul_lt_iff_lt_one_left hZpos]
  constructor
  · intro h
    by_contra hle; push_neg at hle
    have : 1 ≤ α / Real.pi := by rwa [le_div_iff₀ Real.pi_pos, one_mul]
    linarith [Real.one_le_rpow this (by norm_num : (0:ℝ) ≤ 1/2)]
  · intro h
    exact Real.rpow_lt_one (le_of_lt hαπ) (by rwa [div_lt_one Real.pi_pos]) (by norm_num)

/-! ## Duality Flow

The duality flow D(α) = log Z(α) - log Z(π²/α) measures asymmetry between
an object and its Fourier dual. The complexity decomposition gives
D(α) = (1/2)·log(π/α) in closed form. -/

noncomputable def dualityFlow (α : ℝ) : ℝ :=
  Real.log (quadraticPartFn α) - Real.log (quadraticPartFn (Real.pi ^ 2 / α))

theorem duality_flow_eq (α : ℝ) (hα : 0 < α) :
    dualityFlow α = (1 / 2) * Real.log (Real.pi / α) := by
  unfold dualityFlow
  linarith [complexity_decomposition α hα]

theorem duality_flow_antisymmetric (α : ℝ) (hα : 0 < α) :
    dualityFlow (Real.pi ^ 2 / α) =
    -dualityFlow α := by
  rw [duality_flow_eq α hα,
      duality_flow_eq _ (div_pos (sq_pos_of_pos Real.pi_pos) hα)]
  rw [show Real.pi / (Real.pi ^ 2 / α) = α / Real.pi from by field_simp]
  rw [Real.log_div (ne_of_gt hα) (ne_of_gt Real.pi_pos),
      Real.log_div (ne_of_gt Real.pi_pos) (ne_of_gt hα)]
  ring

theorem duality_flow_pos_iff (α : ℝ) (hα : 0 < α) :
    0 < dualityFlow α ↔ α < Real.pi := by
  rw [duality_flow_eq α hα]
  constructor
  · intro h
    have hlog : 0 < Real.log (Real.pi / α) := by nlinarith
    rwa [Real.log_pos_iff (le_of_lt (div_pos Real.pi_pos hα)),
         one_lt_div hα] at hlog
  · intro h
    have := Real.log_pos ((one_lt_div hα).mpr h)
    nlinarith

theorem duality_flow_zero_iff (α : ℝ) (hα : 0 < α) :
    dualityFlow α = 0 ↔ α = Real.pi := by
  rw [duality_flow_eq α hα]
  constructor
  · intro h
    have hlog : Real.log (Real.pi / α) = 0 := by nlinarith
    rcases Real.log_eq_zero.mp hlog with h1 | h1 | h1
    · linarith [div_pos Real.pi_pos hα]
    · linarith [(div_eq_one_iff_eq (ne_of_gt hα)).mp h1]
    · linarith [div_pos Real.pi_pos hα]
  · intro h; subst h
    simp [Real.log_one]

/-! ## Variational Principle

The self-dual point α = π minimizes the total complexity of any dual pair:
Z(π)² ≤ Z(α) · Z(π²/α). Equivalently, among all objects and their Fourier
duals, the self-dual pair has the smallest combined descriptive cost. -/

theorem quadraticPartFn_strictAnti :
    StrictAntiOn quadraticPartFn (Set.Ioi 0) := by
  intro α (hα : 0 < α) β (hβ : 0 < β) (hlt : α < β)
  show quadraticPartFn β < quadraticPartFn α
  simp only [quadraticPartFn]
  exact Summable.tsum_lt_tsum (i := (1 : ℤ))
    (fun k => Real.exp_le_exp_of_le (by nlinarith [sq_nonneg (k : ℝ)]))
    (Real.exp_lt_exp.mpr (by push_cast; nlinarith))
    (summable_quadraticPartFn β hβ)
    (summable_quadraticPartFn α hα)

theorem dual_pair_product (α : ℝ) (hα : 0 < α) :
    quadraticPartFn α * quadraticPartFn (Real.pi ^ 2 / α) =
    (α / Real.pi) ^ ((1 : ℝ) / 2) * quadraticPartFn α ^ 2 := by
  rw [quadraticPartFn_duality_real α hα]; ring

/-- Derivative of each summand: d/dβ exp(-β·k²) = -k²·exp(-β·k²). -/
private lemma hasDerivAt_exp_neg_mul_sq (k : ℤ) (β : ℝ) :
    HasDerivAt (fun γ => Real.exp (-γ * (k : ℝ) ^ 2))
      (-(k : ℝ) ^ 2 * Real.exp (-β * (k : ℝ) ^ 2)) β := by
  have : HasDerivAt (fun γ => -γ * (k : ℝ) ^ 2) (-(1 : ℝ) * (k : ℝ) ^ 2) β :=
    (hasDerivAt_id β).neg.mul_const _
  convert this.exp using 1; ring

private lemma summable_sq_mul_exp (β : ℝ) (hβ : 0 < β) :
    Summable (fun k : ℤ => (k : ℝ) ^ 2 * Real.exp (-β * (k : ℝ) ^ 2)) := by
  have hβ2 : 0 < β / 2 := by linarith
  have hdom : Summable (fun k : ℤ => (2 / β) * Real.exp (-(β / 2) * (k : ℝ) ^ 2)) :=
    (summable_quadraticPartFn (β / 2) hβ2).const_smul (2 / β)
  exact Summable.of_nonneg_of_le
    (fun k => mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _)))
    (fun k => by
      have h1 : β / 2 * (k : ℝ) ^ 2 ≤ Real.exp (β / 2 * (k : ℝ) ^ 2) :=
        le_trans (by linarith [mul_nonneg (le_of_lt hβ2) (sq_nonneg (k : ℝ))])
          (Real.add_one_le_exp _)
      calc (k : ℝ) ^ 2 * Real.exp (-β * (k : ℝ) ^ 2)
          = (2 / β) * (β / 2 * (k : ℝ) ^ 2) * Real.exp (-β * (k : ℝ) ^ 2) := by
            congr 1; field_simp
        _ ≤ (2 / β) * Real.exp (β / 2 * (k : ℝ) ^ 2) * Real.exp (-β * (k : ℝ) ^ 2) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h1 (by positivity)) (le_of_lt (Real.exp_pos _))
        _ = (2 / β) * Real.exp (-(β / 2) * (k : ℝ) ^ 2) := by
            rw [mul_assoc, ← Real.exp_add]; congr 1; ring_nf)
    hdom

private lemma hasDerivAt_quadraticPartFn (β : ℝ) (hβ : 0 < β) :
    HasDerivAt quadraticPartFn
      (∑' k : ℤ, -(k : ℝ) ^ 2 * Real.exp (-β * (k : ℝ) ^ 2)) β := by
  unfold quadraticPartFn
  exact hasDerivAt_tsum_of_isPreconnected
    (g := fun (k : ℤ) (γ : ℝ) => Real.exp (-γ * (k : ℝ) ^ 2))
    (g' := fun (k : ℤ) (γ : ℝ) => -(k : ℝ) ^ 2 * Real.exp (-γ * (k : ℝ) ^ 2))
    (u := fun k : ℤ => (k : ℝ) ^ 2 * Real.exp (-(β / 2) * (k : ℝ) ^ 2))
    (t := Set.Ioi (β / 2))
    (y₀ := β)
    (summable_sq_mul_exp (β / 2) (by linarith))
    isOpen_Ioi
    isPreconnected_Ioi
    (fun k y _ => hasDerivAt_exp_neg_mul_sq k y)
    (fun k y (hy : β / 2 < y) => by
      show |-(k : ℝ) ^ 2 * Real.exp (-y * (k : ℝ) ^ 2)| ≤
        (k : ℝ) ^ 2 * Real.exp (-(β / 2) * (k : ℝ) ^ 2)
      rw [show -(k : ℝ) ^ 2 * Real.exp (-y * (k : ℝ) ^ 2) =
          -((k : ℝ) ^ 2 * Real.exp (-y * (k : ℝ) ^ 2)) from by ring,
          abs_neg, abs_of_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _)))]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp_of_le (by nlinarith [sq_nonneg (k : ℝ)]))
        (sq_nonneg _))
    (Set.mem_Ioi.mpr (by linarith))
    (summable_quadraticPartFn β hβ)
    (Set.mem_Ioi.mpr (by linarith))

private lemma summable_N_summand (β : ℝ) (hβ : 0 < β) :
    Summable (fun k : ℤ => (1 - 4 * β * (k : ℝ) ^ 2) * Real.exp (-β * (k : ℝ) ^ 2)) := by
  have h1 := summable_quadraticPartFn β hβ
  have h2 := (summable_sq_mul_exp β hβ).mul_left (4 * β)
  exact (h1.sub h2).congr fun k => by ring

/-- N(π) = 0: differentiating Z(π²/α) = √(α/π)·Z(α) at α = π gives ⟨k²⟩_π = 1/(4π). -/
private lemma N_self_dual :
    ∑' k : ℤ, (1 - 4 * Real.pi * (k : ℝ) ^ 2) *
      Real.exp (-Real.pi * (k : ℝ) ^ 2) = 0 := by
  set Z'π := ∑' k : ℤ, -(k : ℝ) ^ 2 * Real.exp (-Real.pi * (k : ℝ) ^ 2)
  have hπ_pos := Real.pi_pos
  have hπ_ne := ne_of_gt hπ_pos
  have hZ := hasDerivAt_quadraticPartFn Real.pi hπ_pos
  have h_inv : HasDerivAt (fun α : ℝ => Real.pi ^ 2 / α) (-1) Real.pi := by
    have h := (hasDerivAt_const Real.pi (Real.pi ^ 2)).div
      (hasDerivAt_id Real.pi) hπ_ne
    simp only [id] at h; convert h using 1; field_simp; ring
  have hZ_at : HasDerivAt quadraticPartFn Z'π (Real.pi ^ 2 / Real.pi) := by
    rwa [show Real.pi ^ 2 / Real.pi = Real.pi from by field_simp]
  have hLHS := hZ_at.comp Real.pi h_inv
  have h_div : HasDerivAt (fun α : ℝ => α / Real.pi) (1 / Real.pi) Real.pi := by
    simpa using (hasDerivAt_id Real.pi).div_const Real.pi
  have h_rpow : HasDerivAt (fun α => (α / Real.pi) ^ ((1:ℝ)/2))
      (1 / Real.pi * ((1:ℝ)/2) * (Real.pi / Real.pi) ^ ((1:ℝ)/2 - 1)) Real.pi :=
    h_div.rpow_const (Or.inl (ne_of_gt (div_pos hπ_pos hπ_pos)))
  have hRHS := h_rpow.mul hZ
  have hfun : (fun α => (α / Real.pi) ^ ((1:ℝ)/2) * quadraticPartFn α) =ᶠ[nhds Real.pi]
      (quadraticPartFn ∘ fun α => Real.pi ^ 2 / α) := by
    filter_upwards [eventually_gt_nhds hπ_pos] with α hα
    exact (quadraticPartFn_duality_real α hα).symm
  have heq := (hLHS.congr_of_eventuallyEq hfun).unique hRHS
  simp only [div_self hπ_ne, Real.one_rpow, one_mul, mul_one] at heq
  rw [show ∑' k : ℤ, -(k : ℝ) ^ 2 * Real.exp (-Real.pi * (k : ℝ) ^ 2) = Z'π from rfl] at heq
  field_simp at heq
  suffices hN : ∑' k : ℤ, (1 - 4 * Real.pi * (k : ℝ) ^ 2) *
      Real.exp (-Real.pi * (k : ℝ) ^ 2) = quadraticPartFn Real.pi + 4 * Real.pi * Z'π by
    linarith
  have h1 := summable_quadraticPartFn Real.pi hπ_pos
  have h2 : Summable (fun k : ℤ =>
      4 * Real.pi * (-(k : ℝ) ^ 2 * Real.exp (-Real.pi * (k : ℝ) ^ 2))) :=
    ((summable_sq_mul_exp Real.pi hπ_pos).neg.mul_left (4 * Real.pi)).congr fun k => by ring
  trans (∑' k : ℤ, Real.exp (-Real.pi * (k : ℝ) ^ 2) +
      ∑' k : ℤ, 4 * Real.pi * (-(k : ℝ) ^ 2 * Real.exp (-Real.pi * (k : ℝ) ^ 2)))
  · rw [← h1.tsum_add h2]; congr 1; ext k; ring
  · unfold quadraticPartFn; congr 1
    rw [show Z'π = ∑' k : ℤ, -(k : ℝ) ^ 2 * Real.exp (-Real.pi * (k : ℝ) ^ 2) from rfl]
    rw [← tsum_mul_left]

/-- For A ≥ 4 and t ≥ 0: (A + 4t)·e⁻ᵗ ≤ A. Uses only e^t ≥ 1 + t and A ≥ 4. -/
private lemma aux_exp_ineq (A t : ℝ) (hA : 4 ≤ A) (ht : 0 ≤ t) :
    (A + 4 * t) * Real.exp (-t) ≤ A := by
  rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos t)]
  calc A + 4 * t ≤ A + A * t := by nlinarith
    _ = A * (1 + t) := by ring
    _ ≤ A * Real.exp t :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp t]) (by linarith)

/-- Each summand of N is nondecreasing in β for β ≥ π (4π > 5 argument). -/
private lemma N_summand_mono (k : ℤ) (β : ℝ) (hβ : Real.pi ≤ β) :
    (1 - 4 * Real.pi * (k : ℝ) ^ 2) * Real.exp (-Real.pi * (k : ℝ) ^ 2) ≤
    (1 - 4 * β * (k : ℝ) ^ 2) * Real.exp (-β * (k : ℝ) ^ 2) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
      rcases le_or_gt k (-1) with h | h
      · have : (k : ℝ) ≤ -1 := by exact_mod_cast h
        nlinarith [sq_nonneg ((k : ℝ) + 1)]
      · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
        nlinarith [sq_nonneg ((k : ℝ) - 1)]
    have hA : 4 ≤ 4 * Real.pi * (k : ℝ) ^ 2 - 1 := by nlinarith [Real.pi_gt_three]
    have ht : 0 ≤ (β - Real.pi) * (k : ℝ) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have haux := aux_exp_ineq (4 * Real.pi * (k : ℝ) ^ 2 - 1)
      ((β - Real.pi) * (k : ℝ) ^ 2) hA ht
    -- Factor exp(-βk²) = exp(-πk²) · exp(-(β-π)k²)
    have hfac : Real.exp (-β * (k : ℝ) ^ 2) =
        Real.exp (-Real.pi * (k : ℝ) ^ 2) * Real.exp (-(β - Real.pi) * (k : ℝ) ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hfac]
    -- Reduce to: (1-4πk²) ≤ (1-4βk²)·exp(-(β-π)k²), then multiply by exp(-πk²) > 0
    suffices hsuff : 1 - 4 * Real.pi * (k : ℝ) ^ 2 ≤
        (1 - 4 * β * (k : ℝ) ^ 2) * Real.exp (-(β - Real.pi) * (k : ℝ) ^ 2) by
      calc (1 - 4 * Real.pi * (k : ℝ) ^ 2) * Real.exp (-Real.pi * (k : ℝ) ^ 2)
          ≤ ((1 - 4 * β * (k : ℝ) ^ 2) * Real.exp (-(β - Real.pi) * (k : ℝ) ^ 2)) *
            Real.exp (-Real.pi * (k : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right hsuff (le_of_lt (Real.exp_pos _))
        _ = (1 - 4 * β * (k : ℝ) ^ 2) *
            (Real.exp (-Real.pi * (k : ℝ) ^ 2) *
             Real.exp (-(β - Real.pi) * (k : ℝ) ^ 2)) := by ring
    -- -(4πk²-1) ≤ -(4πk²-1+4(β-π)k²)·exp, follows from haux by negation
    have hrw1 : 1 - 4 * β * (k : ℝ) ^ 2 =
        -(4 * Real.pi * (k : ℝ) ^ 2 - 1 + 4 * ((β - Real.pi) * (k : ℝ) ^ 2)) := by ring
    have hrw2 : -(β - Real.pi) * (k : ℝ) ^ 2 = -((β - Real.pi) * (k : ℝ) ^ 2) := by ring
    rw [hrw1, hrw2, neg_mul]
    linarith

/-- N(β) ≥ 0 for β ≥ π: term-by-term from N(π) = 0. -/
private lemma N_nonneg (β : ℝ) (hβ : Real.pi ≤ β) :
    0 ≤ ∑' k : ℤ, (1 - 4 * β * (k : ℝ) ^ 2) *
      Real.exp (-β * (k : ℝ) ^ 2) := by
  rw [show (0 : ℝ) = ∑' k : ℤ, (1 - 4 * Real.pi * (k : ℝ) ^ 2) *
    Real.exp (-Real.pi * (k : ℝ) ^ 2) from N_self_dual.symm]
  exact (summable_N_summand Real.pi Real.pi_pos).tsum_le_tsum
    (fun k => N_summand_mono k β hβ)
    (summable_N_summand β (lt_of_lt_of_le Real.pi_pos hβ))

/-- β ↦ (β/π)^{1/2}·Z(β)² is monotone on [π,∞).
Reduces to N(β) ≥ 0 via `monotoneOn_of_deriv_nonneg` + `hasDerivAt_tsum`. -/
private lemma quadraticPartFn_rpow_sq_monotone :
    MonotoneOn (fun β => (β / Real.pi) ^ ((1:ℝ)/2) * quadraticPartFn β ^ 2)
    (Set.Ici Real.pi) := by
  have hf_at : ∀ β : ℝ, 0 < β →
      HasDerivAt (fun α => (α / Real.pi) ^ ((1:ℝ)/2) * quadraticPartFn α ^ 2)
        (1 / Real.pi * ((1:ℝ)/2) * (β / Real.pi) ^ ((1:ℝ)/2 - 1) *
         quadraticPartFn β ^ 2 +
         (β / Real.pi) ^ ((1:ℝ)/2) *
         (↑2 * quadraticPartFn β ^ (2 - 1) *
          (∑' k : ℤ, -(k : ℝ) ^ 2 * Real.exp (-β * (k : ℝ) ^ 2))))
        β := fun β hβ =>
    (((hasDerivAt_id β).div_const Real.pi).rpow_const
      (Or.inl (ne_of_gt (div_pos hβ Real.pi_pos)))).mul
      ((hasDerivAt_quadraticPartFn β hβ).pow 2)
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · exact fun β hβ => (hf_at β (lt_of_lt_of_le Real.pi_pos hβ)).differentiableAt.continuousAt.continuousWithinAt
  · rw [interior_Ici]; exact fun β hβ => (hf_at β (lt_trans Real.pi_pos hβ)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]; intro β hβ
    have hβ_pos : 0 < β := lt_trans Real.pi_pos hβ
    have hβπ : 0 < β / Real.pi := div_pos hβ_pos Real.pi_pos
    rw [(hf_at β hβ_pos).deriv]
    simp only [show (2:ℕ) - 1 = 1 from rfl, pow_one]
    set c := (β / Real.pi) ^ ((1:ℝ)/2) with hc_def
    set ci := (β / Real.pi) ^ ((1:ℝ)/2 - 1) with hci_def
    set Zβ := quadraticPartFn β
    set Z'β := ∑' k : ℤ, -(k : ℝ) ^ 2 * Real.exp (-β * (k : ℝ) ^ 2)
    have hc_pos : 0 < c := Real.rpow_pos_of_pos hβπ _
    have hc_ci : c * ci = 1 := by
      simp only [hc_def, hci_def]
      rw [← Real.rpow_add hβπ, show (1:ℝ)/2 + ((1:ℝ)/2 - 1) = 0 from by ring,
         Real.rpow_zero]
    have hc_sq : c * c = β / Real.pi := by
      simp only [hc_def]
      rw [← Real.rpow_add hβπ, show (1:ℝ)/2 + (1:ℝ)/2 = 1 from by norm_num,
         Real.rpow_one]
    have hZ_pos : 0 < Zβ := lt_trans one_pos (quadraticPartFn_gt_one β hβ_pos)
    have hπ_ne := ne_of_gt Real.pi_pos
    have hNβ : 0 ≤ Zβ + 4 * β * Z'β := by
      have hN := N_nonneg β (le_of_lt hβ)
      rw [show Zβ + 4 * β * Z'β =
          ∑' k : ℤ, (1 - 4 * β * (k : ℝ) ^ 2) * Real.exp (-β * (k : ℝ) ^ 2) from by
        show quadraticPartFn β + 4 * β *
            (∑' k : ℤ, -(k : ℝ) ^ 2 * Real.exp (-β * (k : ℝ) ^ 2)) =
            ∑' k : ℤ, (1 - 4 * β * (k : ℝ) ^ 2) * Real.exp (-β * (k : ℝ) ^ 2)
        unfold quadraticPartFn; rw [← tsum_mul_left]
        rw [← (summable_quadraticPartFn β hβ_pos).tsum_add
            (((summable_sq_mul_exp β hβ_pos).neg.mul_left (4 * β)).congr fun k => by ring)]
        congr 1; ext k; ring]
      exact hN
    suffices h : 0 ≤ 2 * Real.pi * c *
        (1 / Real.pi * (1 / 2) * ci * Zβ ^ 2 + c * (2 * Zβ * Z'β)) by
      exact nonneg_of_mul_nonneg_right h
        (mul_pos (mul_pos two_pos Real.pi_pos) hc_pos)
    have hring : 2 * Real.pi * c *
        (1 / Real.pi * (1 / 2) * ci * Zβ ^ 2 + c * (2 * Zβ * Z'β)) =
        c * ci * Zβ ^ 2 + 4 * Real.pi * (c * c) * Zβ * Z'β := by
      field_simp; ring
    rw [hring, hc_ci, hc_sq]
    have hfinal : 1 * Zβ ^ 2 + 4 * Real.pi * (β / Real.pi) * Zβ * Z'β =
        Zβ * (Zβ + 4 * β * Z'β) := by field_simp
    rw [hfinal]
    exact mul_nonneg (le_of_lt hZ_pos) hNβ

set_option maxHeartbeats 800000 in
private lemma quadraticPartFn_self_dual_minimum (α : ℝ) (hα : 0 < α) :
    quadraticPartFn Real.pi ^ 2 ≤
    (α / Real.pi) ^ ((1 : ℝ) / 2) * quadraticPartFn α ^ 2 := by
  suffices h : ∀ β : ℝ, β ≥ Real.pi → quadraticPartFn Real.pi ^ 2 ≤
      (β / Real.pi) ^ ((1 : ℝ) / 2) * quadraticPartFn β ^ 2 by
    by_cases hle : α ≥ Real.pi
    · exact h α hle
    · push_neg at hle
      have hβ := h (Real.pi ^ 2 / α) (by rw [ge_iff_le, le_div_iff₀ hα]; nlinarith [Real.pi_pos])
      rw [quadraticPartFn_duality_real α hα] at hβ
      convert hβ using 1
      have hπ : Real.pi > 0 := Real.pi_pos
      have hαπ : 0 < α / Real.pi := div_pos hα hπ
      have hsimp : Real.pi ^ 2 / α / Real.pi = Real.pi / α := by field_simp
      rw [hsimp, mul_pow]
      have hsq : ((α / Real.pi) ^ ((1:ℝ)/2)) ^ 2 = α / Real.pi := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hαπ)]; norm_num
      rw [hsq]
      suffices hkey : (Real.pi / α) ^ ((1:ℝ)/2) * (α / Real.pi) = (α / Real.pi) ^ ((1:ℝ)/2) by
        nlinarith [sq_nonneg (quadraticPartFn α)]
      have step1 : (Real.pi / α) ^ ((1:ℝ)/2) = ((α / Real.pi) ^ ((1:ℝ)/2))⁻¹ := by
        rw [show (Real.pi / α : ℝ) = (α / Real.pi)⁻¹ from (inv_div α Real.pi).symm]
        exact Real.inv_rpow (le_of_lt hαπ) _
      set x := (α / Real.pi) ^ ((1:ℝ)/2) with hx_def
      have hx : 0 < x := Real.rpow_pos_of_pos hαπ _
      rw [step1, ← hsq, show x⁻¹ * x ^ 2 = x from by
        rw [sq, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hx), one_mul]]
  intro β hβ
  have hπ_mem : Real.pi ∈ Set.Ici Real.pi := Set.left_mem_Ici
  have hβ_mem : β ∈ Set.Ici Real.pi := hβ
  have hmono := quadraticPartFn_rpow_sq_monotone hπ_mem hβ_mem hβ
  simp only [div_self (ne_of_gt Real.pi_pos), Real.one_rpow, one_mul] at hmono
  exact hmono

theorem dual_pair_variational (α : ℝ) (hα : 0 < α) :
    quadraticPartFn Real.pi ^ 2 ≤
    quadraticPartFn α * quadraticPartFn (Real.pi ^ 2 / α) := by
  rw [dual_pair_product α hα]
  exact quadraticPartFn_self_dual_minimum α hα

theorem GroupoidObj.dual_pair_variational
    (E : GroupoidObj) (wind : End E.base ≃ ℤ) (α : ℝ) (hα : 0 < α)
    (hK : ∀ g, E.energy g = α * (wind g : ℝ) ^ 2) :
    quadraticPartFn Real.pi ^ 2 ≤ E.partFn * (E.dual wind α hα hK).partFn := by
  rw [partFn_eq_quadraticPartFn E wind α hK,
      partFn_eq_quadraticPartFn (E.dual wind α hα hK) wind _ (fun _ => rfl)]
  exact Simplicial.dual_pair_variational α hα

/-! ## Mass Duality

Geodesic mass (combinatorial, ℕ) and harmonic mass (analytic, ℝ) are reciprocal:
their product is 1. T-duality exchanges these two measures. -/

theorem mass_duality (n : ℕ) (hn : n ≥ 3) :
    (↑(geodesicLength (CycleGraph n hn) (cycleWalk n hn)) : ℝ) * harmonicEnergy n hn = 1 := by
  rw [cycleGraph_geodesic_eq_n, cycleGraph_harmonicEnergy]
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

end Simplicial
