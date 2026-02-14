import Meno.Groupoid
import Meno.Theta

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

end Simplicial
