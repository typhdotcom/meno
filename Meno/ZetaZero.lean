import Meno.LatticeZeta
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.Order.Interval.Finset.Box
import Mathlib.Analysis.Complex.Convex

/-! # The zero criterion

The Newton certificate (`exists_zero_of_newton`), and its analytic input for the
Epstein zeta `Z(s) = ∑_{k≠0} Q(k)^{−s}` of a coercive integral binary form: the
termwise derivatives, the log-weighted majorants, the shell bounds on the tail past a
cutoff, the cutoff split, and the criterion `Coercive.exists_zero` reducing a zero in
a disc to three numbers. -/

namespace Meno

open Metric

/-- **The Newton certificate**: a differentiable `f` on a closed disc whose
derivative stays within `q·|c|` of a fixed `c ≠ 0` (`q < 1`), and whose
value at the centre is at most `(1 − q)·ρ·|c|`, vanishes in the disc —
the Newton map `z ↦ z − f z / c` is a `q`-contraction of the disc into
itself, and its fixed point is a zero. -/
theorem exists_zero_of_newton {f f' : ℂ → ℂ} {z₀ c : ℂ} {ρ q : ℝ} (hρ : 0 < ρ) (hq : q < 1)
    (hc : c ≠ 0) (hf : ∀ z ∈ closedBall z₀ ρ, HasDerivAt f (f' z) z)
    (hder : ∀ z ∈ closedBall z₀ ρ, ‖f' z - c‖ ≤ q * ‖c‖)
    (hval : ‖f z₀‖ ≤ (1 - q) * ρ * ‖c‖) :
    ∃ z ∈ closedBall z₀ ρ, f z = 0 := by
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hq0 : 0 ≤ q := by
    have := (norm_nonneg _).trans (hder z₀ (mem_closedBall_self hρ.le))
    exact nonneg_of_mul_nonneg_left this hcn
  set T : ℂ → ℂ := fun z => z - f z / c with hT
  have hTd : ∀ z ∈ closedBall z₀ ρ, HasDerivWithinAt T (1 - f' z / c) (closedBall z₀ ρ) z :=
    fun z hz => ((hasDerivAt_id z).sub ((hf z hz).div_const c)).hasDerivWithinAt
  have hTb : ∀ z ∈ closedBall z₀ ρ, ‖1 - f' z / c‖₊ ≤ q.toNNReal := by
    intro z hz
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal q hq0]
    rw [show (1 : ℂ) - f' z / c = -((f' z - c) / c) by field_simp; ring, norm_neg, norm_div]
    exact (div_le_iff₀ hcn).mpr (hder z hz)
  have hLip : LipschitzOnWith q.toNNReal T (closedBall z₀ ρ) :=
    (convex_closedBall z₀ ρ).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hTd hTb
  have hmaps : Set.MapsTo T (closedBall z₀ ρ) (closedBall z₀ ρ) := by
    intro z hz
    have h1 : dist (T z) (T z₀) ≤ q * dist z z₀ := by
      simpa [Real.coe_toNNReal q hq0] using hLip.dist_le_mul z hz z₀ (mem_closedBall_self hρ.le)
    have h2 : dist (T z₀) z₀ ≤ (1 - q) * ρ := by
      rw [dist_eq_norm, hT]
      simp only [sub_sub_cancel_left, norm_neg, norm_div]
      exact (div_le_iff₀ hcn).mpr hval
    have hz' : dist z z₀ ≤ ρ := hz
    rw [mem_closedBall]
    calc dist (T z) z₀ ≤ dist (T z) (T z₀) + dist (T z₀) z₀ := dist_triangle _ _ _
      _ ≤ q * ρ + (1 - q) * ρ := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_left hz' hq0)
      _ = ρ := by ring
  have hcon : ContractingWith q.toNNReal (hmaps.restrict T (closedBall z₀ ρ) (closedBall z₀ ρ)) :=
    ⟨by rw [← NNReal.coe_lt_coe, Real.coe_toNNReal q hq0]; exact hq, hLip.mapsToRestrict hmaps⟩
  obtain ⟨z, hz, hfix, -⟩ := hcon.exists_fixedPoint' isClosed_closedBall.isComplete hmaps
    (mem_closedBall_self hρ.le) (edist_ne_top _ _)
  refine ⟨z, hz, ?_⟩
  have : z - f z / c = z := hfix
  have : f z / c = 0 := by linear_combination -this
  exact (div_eq_zero_iff.mp this).resolve_right hc

/-! ## The Epstein zeta of an integral binary form -/

namespace Epstein

open Finset Complex

/-- An integral binary form `a x² + b xy + c y²`. -/
structure BinForm where
  a : ℤ
  b : ℤ
  c : ℤ

namespace BinForm

variable (F : BinForm)

/-- The form's value at a lattice point. -/
def val (k : ℤ × ℤ) : ℤ := F.a * k.1 ^ 2 + F.b * k.1 * k.2 + F.c * k.2 ^ 2

/-- The form's value, as a natural number. -/
def q (k : ℤ × ℤ) : ℕ := (F.val k).toNat

end BinForm

/-- The sup norm on `ℤ × ℤ`. -/
def supNorm (k : ℤ × ℤ) : ℕ := max k.1.natAbs k.2.natAbs

/-- **Two-sided coercivity** of a binary form against the sup norm:
`(lN/lD)·‖k‖² ≤ Q(k) ≤ hi·‖k‖²`. -/
structure Coercive (F : BinForm) (lN lD hi : ℕ) : Prop where
  lN_pos : 0 < lN
  lD_pos : 0 < lD
  lower : ∀ k, lN * supNorm k ^ 2 ≤ lD * F.q k
  upper : ∀ k, F.q k ≤ hi * supNorm k ^ 2

variable {F : BinForm} {lN lD hi : ℕ}

theorem supNorm_eq_zero {k : ℤ × ℤ} : supNorm k = 0 ↔ k = 0 := by
  constructor
  · intro h
    have h1 : k.1.natAbs = 0 := by unfold supNorm at h; omega
    have h2 : k.2.natAbs = 0 := by unfold supNorm at h; omega
    exact Prod.ext (Int.natAbs_eq_zero.mp h1) (Int.natAbs_eq_zero.mp h2)
  · rintro rfl; rfl

theorem Coercive.q_pos (hF : Coercive F lN lD hi) {k : ℤ × ℤ} (hk : k ≠ 0) : 0 < F.q k := by
  have hm : 0 < supNorm k := Nat.pos_of_ne_zero (fun h => hk (supNorm_eq_zero.mp h))
  have := hF.lower k
  have h1 : 0 < lN * supNorm k ^ 2 := Nat.mul_pos hF.lN_pos (pow_pos hm 2)
  exact Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at this; omega

theorem Coercive.q_eq_zero_iff (hF : Coercive F lN lD hi) {k : ℤ × ℤ} : F.q k = 0 ↔ k = 0 := by
  constructor
  · intro h; by_contra hk; exact (hF.q_pos hk).ne' h
  · rintro rfl; simp [BinForm.q, BinForm.val]

/-- The real majorant `Q(k)^{−σ}` (zero at the origin). -/
noncomputable def maj (F : BinForm) (σ : ℝ) (k : ℤ × ℤ) : ℝ :=
  if F.q k = 0 then 0 else (F.q k : ℝ) ^ (-σ)

theorem maj_nonneg (σ : ℝ) (k : ℤ × ℤ) : 0 ≤ maj F σ k := by
  unfold maj; split_ifs <;> positivity

/-- The majorant is dominated by the sup-norm p-series. -/
theorem Coercive.maj_le (hF : Coercive F lN lD hi) {σ : ℝ} (hσ : 0 ≤ σ) (k : ℤ × ℤ) :
    maj F σ k ≤ ((lD : ℝ) / lN) ^ σ * (supNorm k : ℝ) ^ (-(2 * σ)) := by
  unfold maj
  split_ifs with h0
  · positivity
  · have hk : k ≠ 0 := fun hk => h0 ((hF.q_eq_zero_iff).mpr hk)
    have hm : (0 : ℝ) < supNorm k := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => hk (supNorm_eq_zero.mp h))
    have hlN : (0 : ℝ) < lN := by exact_mod_cast hF.lN_pos
    have hlD : (0 : ℝ) < lD := by exact_mod_cast hF.lD_pos
    have hlow : (lN : ℝ) / lD * (supNorm k : ℝ) ^ 2 ≤ F.q k := by
      have := hF.lower k
      have h' : (lN : ℝ) * (supNorm k : ℝ) ^ 2 ≤ (lD : ℝ) * F.q k := by exact_mod_cast this
      rw [div_mul_eq_mul_div, div_le_iff₀ hlD]
      linarith
    have hpos : 0 < (lN : ℝ) / lD * (supNorm k : ℝ) ^ 2 := by positivity
    calc (F.q k : ℝ) ^ (-σ) ≤ ((lN : ℝ) / lD * (supNorm k : ℝ) ^ 2) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos hpos hlow (by linarith)
      _ = ((lD : ℝ) / lN) ^ σ * (supNorm k : ℝ) ^ (-(2 * σ)) := by
          have e1 : ((lN : ℝ) / lD) ^ (-σ) = ((lD : ℝ) / lN) ^ σ := by
            rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_div]
          have e2 : ((supNorm k : ℝ) ^ 2) ^ (-σ) = (supNorm k : ℝ) ^ (-(2 * σ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hm.le]
            push_cast
            ring_nf
          rw [Real.mul_rpow (by positivity) (by positivity), e1, e2]

/-- The sup-norm p-series on `ℤ × ℤ` converges past exponent `2`. -/
theorem summable_supNorm_rpow {t : ℝ} (ht : 2 < t) :
    Summable (fun k : ℤ × ℤ => (supNorm k : ℝ) ^ (-t)) := by
  have h := EisensteinSeries.summable_one_div_norm_rpow ht
  refine ((finTwoArrowEquiv ℤ).symm.summable_iff.mpr h).congr fun k => ?_
  simp only [Function.comp_apply, EisensteinSeries.norm_eq_max_natAbs, supNorm,
    finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_max]

/-- **The majorant series converges** past `σ = 1`. -/
theorem Coercive.summable_maj (hF : Coercive F lN lD hi) {σ : ℝ} (hσ : 1 < σ) :
    Summable (maj F σ) :=
  ((summable_supNorm_rpow (by linarith : 2 < 2 * σ)).mul_left _).of_nonneg_of_le
    (maj_nonneg σ) (hF.maj_le (by linarith))

/-- The square `[−M, M]²` is the disjoint union of the shells `box m`, `m ≤ M`. -/
theorem sum_Icc_eq_sum_box (f : ℤ × ℤ → ℝ) (M : ℕ) :
    ∑ k ∈ Icc (-(M : ℤ × ℤ)) M, f k = ∑ m ∈ range (M + 1), ∑ k ∈ box m, f k := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ← ih, ← Finset.box_succ_disjUnion M, sum_disjUnion, add_comm]

/-- **The telescoping estimate**: `m^{−p} ≤ ((m−1)^{1−p} − m^{1−p})/(p−1)` for
`p > 1`, `m > 1` — the mean value theorem for `x^{1−p}`. -/
theorem rpow_neg_le_telescope {p m : ℝ} (hp : 1 < p) (hm : 1 < m) :
    m ^ (-p) ≤ ((m - 1) ^ (1 - p) - m ^ (1 - p)) / (p - 1) := by
  have hm1 : 0 < m - 1 := by linarith
  obtain ⟨ξ, hξ, hξd⟩ := exists_hasDerivAt_eq_slope (fun x : ℝ => x ^ (1 - p))
    (fun x => (1 - p) * x ^ (1 - p - 1)) (by linarith : m - 1 < m)
    (fun x hx => (Real.continuousAt_rpow_const x _
      (Or.inl (by linarith [hx.1] : (x : ℝ) ≠ 0).symm.symm)).continuousWithinAt)
    (fun x hx => Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1])))
  have hξ0 : 0 < ξ := by linarith [hξ.1]
  have hslope : (m - 1) ^ (1 - p) - m ^ (1 - p) = (p - 1) * ξ ^ (-p) := by
    have h := hξd
    rw [show m - (m - 1) = (1 : ℝ) by ring, div_one] at h
    rw [show (1 : ℝ) - p - 1 = -p by ring] at h
    linarith
  rw [hslope, mul_div_cancel_left₀ _ (by linarith : (p - 1) ≠ 0)]
  exact Real.rpow_le_rpow_of_nonpos hξ0 hξ.2.le (by linarith)

/-- Partial sums of `m^{−p}` from `m₀ ≥ 2` are at most `(m₀ − 1)^{1−p}/(p − 1)`. -/
theorem sum_Icc_rpow_neg_le {p : ℝ} (hp : 1 < p) {m₀ : ℕ} (hm₀ : 2 ≤ m₀) (M : ℕ) :
    ∑ m ∈ Icc m₀ M, (m : ℝ) ^ (-p) ≤ ((m₀ : ℝ) - 1) ^ (1 - p) / (p - 1) := by
  have hp1 : 0 < p - 1 := by linarith
  have key : ∀ d : ℕ, ∑ m ∈ Icc m₀ (m₀ - 1 + d), (m : ℝ) ^ (-p)
      ≤ (((m₀ : ℝ) - 1) ^ (1 - p) - ((((m₀ - 1 + d : ℕ) : ℝ)) ^ (1 - p))) / (p - 1) := by
    intro d
    induction d with
    | zero =>
      rw [Icc_eq_empty (by omega), sum_empty, add_zero]
      push_cast [Nat.cast_sub (by omega : 1 ≤ m₀)]
      simp
    | succ d ih =>
      have hins : insert (m₀ - 1 + d + 1) (Icc m₀ (m₀ - 1 + d)) = Icc m₀ (m₀ - 1 + (d + 1)) := by
        rw [← add_assoc]; exact Finset.insert_Icc_right_eq_Icc_add_one (by omega)
      rw [← hins, sum_insert (by simp)]
      have ht := rpow_neg_le_telescope hp
        (show (1 : ℝ) < ((m₀ - 1 + d + 1 : ℕ) : ℝ) by
          have : 1 < m₀ - 1 + d + 1 := by omega
          exact_mod_cast this)
      have hcast : (((m₀ - 1 + d + 1 : ℕ) : ℝ) - 1) = ((m₀ - 1 + d : ℕ) : ℝ) := by
        push_cast; ring
      rw [hcast] at ht
      rw [show m₀ - 1 + (d + 1) = m₀ - 1 + d + 1 by ring]
      calc ((m₀ - 1 + d + 1 : ℕ) : ℝ) ^ (-p) + ∑ m ∈ Icc m₀ (m₀ - 1 + d), (m : ℝ) ^ (-p)
          ≤ (((m₀ - 1 + d : ℕ) : ℝ) ^ (1 - p) - ((m₀ - 1 + d + 1 : ℕ) : ℝ) ^ (1 - p)) / (p - 1)
            + (((m₀ : ℝ) - 1) ^ (1 - p) - (((m₀ - 1 + d : ℕ) : ℝ)) ^ (1 - p)) / (p - 1) :=
            add_le_add ht ih
        _ = (((m₀ : ℝ) - 1) ^ (1 - p) - ((m₀ - 1 + d + 1 : ℕ) : ℝ) ^ (1 - p)) / (p - 1) := by
            ring
  rcases Nat.lt_or_ge M m₀ with h | h
  · rw [Icc_eq_empty (by omega), sum_empty]
    have : (0 : ℝ) < (m₀ : ℝ) - 1 := by
      have : (1 : ℝ) < m₀ := by exact_mod_cast (by omega : 1 < m₀)
      linarith
    positivity
  · obtain ⟨d, rfl⟩ : ∃ d, M = m₀ - 1 + d := ⟨M - (m₀ - 1), by omega⟩
    refine (key d).trans ?_
    have : 0 ≤ (((m₀ - 1 + d : ℕ) : ℝ)) ^ (1 - p) := by positivity
    gcongr
    linarith

/-- **The shell tail bound**: past `N`, the majorant sums to at most
`8·(lD/lN)^σ·(m₀ − 1)^{2−2σ}/(2σ − 2)`, where every lattice point with
`Q(k) > N` lies at sup norm at least `m₀` (`hi·(m₀ − 1)² ≤ N`). -/
theorem Coercive.tail_le (hF : Coercive F lN lD hi) {σ : ℝ} (hσ : 1 < σ) {N m₀ : ℕ}
    (hm₀ : 2 ≤ m₀) (hN : hi * (m₀ - 1) ^ 2 ≤ N) :
    ∑' k, (if N < F.q k then maj F σ k else 0)
      ≤ 8 * ((lD : ℝ) / lN) ^ σ * (((m₀ : ℝ) - 1) ^ (2 - 2 * σ) / (2 * σ - 2)) := by
  set C := ((lD : ℝ) / lN) ^ σ with hC
  have hC0 : 0 ≤ C := by positivity
  have hg0 : 0 ≤ fun k : ℤ × ℤ => if N < F.q k then maj F σ k else 0 := fun k => by
    show 0 ≤ (if N < F.q k then maj F σ k else 0)
    split_ifs <;> first | exact maj_nonneg σ k | exact le_rfl
  refine Real.tsum_le_of_sum_le hg0 fun u => ?_
  obtain ⟨M, hM⟩ : ∃ M : ℕ, u ⊆ Icc (-(M : ℤ × ℤ)) M := by
    refine ⟨u.sup supNorm, fun k hk => ?_⟩
    have hle : supNorm k ≤ u.sup supNorm := le_sup hk
    have h1 : k.1.natAbs ≤ u.sup supNorm := le_trans (le_max_left _ _) hle
    have h2 : k.2.natAbs ≤ u.sup supNorm := le_trans (le_max_right _ _) hle
    simp only [mem_Icc, Prod.le_def, Prod.fst_neg, Prod.snd_neg, Prod.fst_natCast,
      Prod.snd_natCast]
    omega
  calc ∑ k ∈ u, (if N < F.q k then maj F σ k else 0)
      ≤ ∑ k ∈ Icc (-(M : ℤ × ℤ)) M, (if N < F.q k then maj F σ k else 0) :=
        sum_le_sum_of_subset_of_nonneg hM fun k _ _ => hg0 k
    _ = ∑ m ∈ range (M + 1), ∑ k ∈ box m, (if N < F.q k then maj F σ k else 0) :=
        sum_Icc_eq_sum_box _ M
    _ ≤ ∑ m ∈ range (M + 1), (if m₀ ≤ m then 8 * C * (m : ℝ) ^ (-(2 * σ - 1)) else 0) := by
        refine sum_le_sum fun m _ => ?_
        split_ifs with hm
        · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
          calc ∑ k ∈ box m, (if N < F.q k then maj F σ k else 0)
              ≤ ∑ k ∈ box m, C * (m : ℝ) ^ (-(2 * σ)) := by
                refine sum_le_sum fun k hk => ?_
                have hsk : supNorm k = m := Int.mem_box.mp hk
                split_ifs
                · have := hF.maj_le (by linarith : (0 : ℝ) ≤ σ) k
                  rwa [hsk] at this
                · exact mul_nonneg hC0 (by positivity)
            _ = 8 * C * (m : ℝ) ^ (-(2 * σ - 1)) := by
                rw [sum_const, Int.card_box (by omega), nsmul_eq_mul]
                push_cast
                rw [show -(2 * σ - 1) = 1 + -(2 * σ) by ring,
                  Real.rpow_add (by linarith), Real.rpow_one]
                ring
        · refine (sum_eq_zero fun k hk => ?_).le
          have hsk : supNorm k = m := Int.mem_box.mp hk
          rw [ite_eq_right]
          intro hq
          have hup := hF.upper k
          rw [hsk] at hup
          have : hi * (m₀ - 1) ^ 2 < hi * m ^ 2 := lt_of_le_of_lt hN (lt_of_lt_of_le hq hup)
          have hlt : (m₀ - 1) ^ 2 < m ^ 2 := lt_of_mul_lt_mul_left this (Nat.zero_le _)
          have : m₀ - 1 < m := lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) hlt
          omega
    _ = 8 * C * ∑ m ∈ Icc m₀ M, (m : ℝ) ^ (-(2 * σ - 1)) := by
        rw [mul_sum, sum_ite, sum_const_zero, add_zero]
        congr 1
        ext m
        simp only [mem_filter, mem_range, mem_Icc]
        omega
    _ ≤ 8 * C * (((m₀ : ℝ) - 1) ^ (2 - 2 * σ) / (2 * σ - 2)) := by
        gcongr
        have := sum_Icc_rpow_neg_le (by linarith : 1 < 2 * σ - 1) hm₀ M
        rw [show 1 - (2 * σ - 1) = 2 - 2 * σ by ring,
          show 2 * σ - 1 - 1 = 2 * σ - 2 by ring] at this
        exact this

/-- The log-weighted majorant `(log Q)^j·Q^{−σ}`. -/
noncomputable def lmaj (F : BinForm) (j : ℕ) (σ : ℝ) (k : ℤ × ℤ) : ℝ :=
  if F.q k = 0 then 0 else Real.log (F.q k) ^ j * (F.q k : ℝ) ^ (-σ)

theorem lmaj_nonneg (j : ℕ) (σ : ℝ) (k : ℤ × ℤ) : 0 ≤ lmaj F j σ k := by
  unfold lmaj
  split_ifs with h
  · exact le_rfl
  · have : (1 : ℝ) ≤ F.q k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    exact mul_nonneg (pow_nonneg (Real.log_nonneg this) _) (by positivity)

/-- `log x ≤ x^τ/(e·τ)`: `y ≤ e^{y−1}` at `y = τ·log x`. -/
theorem log_le_rpow_div_exp {x τ : ℝ} (hx : 0 < x) (hτ : 0 < τ) :
    Real.log x ≤ x ^ τ / (Real.exp 1 * τ) := by
  rw [le_div_iff₀ (by positivity), Real.rpow_def_of_pos hx]
  have h := Real.add_one_le_exp (Real.log x * τ - 1)
  rw [Real.exp_sub, le_div_iff₀ (Real.exp_pos 1)] at h
  linarith

/-- **The power trick**: `(log Q)^j·Q^{−σ} ≤ (eτ)^{−j}·Q^{−(σ − jτ)}`, from
`log x ≤ x^τ/(eτ)`. -/
theorem lmaj_le (j : ℕ) {τ : ℝ} (hτ : 0 < τ) (σ : ℝ) (k : ℤ × ℤ) :
    lmaj F j σ k ≤ (1 / (Real.exp 1 * τ)) ^ j * maj F (σ - j * τ) k := by
  unfold lmaj maj
  split_ifs with h
  · simp
  · have hq1 : (1 : ℝ) ≤ F.q k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    have hq0 : (0 : ℝ) < F.q k := by linarith
    have hlog := log_le_rpow_div_exp hq0 hτ
    have hl0 := Real.log_nonneg hq1
    have he : 0 < Real.exp 1 * τ := by positivity
    calc Real.log (F.q k) ^ j * (F.q k : ℝ) ^ (-σ)
        ≤ ((F.q k : ℝ) ^ τ / (Real.exp 1 * τ)) ^ j * (F.q k : ℝ) ^ (-σ) := by gcongr
      _ = (1 / (Real.exp 1 * τ)) ^ j * (F.q k : ℝ) ^ (-(σ - j * τ)) := by
          rw [div_pow, ← Real.rpow_natCast ((F.q k : ℝ) ^ τ), ← Real.rpow_mul hq0.le,
            show -(σ - j * τ) = τ * j + -σ by ring, Real.rpow_add hq0, one_div, inv_pow]
          ring

theorem Coercive.summable_lmaj (hF : Coercive F lN lD hi) (j : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (lmaj F j σ) := by
  have hτ : 0 < (σ - 1) / (2 * (j + 1)) := by positivity
  refine ((hF.summable_maj (σ := σ - j * ((σ - 1) / (2 * (j + 1)))) ?_).mul_left _).of_nonneg_of_le
    (lmaj_nonneg j σ) (lmaj_le j hτ σ)
  have : (j : ℝ) * ((σ - 1) / (2 * (j + 1))) < σ - 1 := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- The Dirichlet term `Q(k)^{−s}` (zero at the origin). -/
noncomputable def term (F : BinForm) (s : ℂ) (k : ℤ × ℤ) : ℂ :=
  if F.q k = 0 then 0 else (F.q k : ℂ) ^ (-s)

/-- Its derivative in `s`, `−log Q(k)·Q(k)^{−s}`. -/
noncomputable def dterm (F : BinForm) (s : ℂ) (k : ℤ × ℤ) : ℂ :=
  if F.q k = 0 then 0 else -(Real.log (F.q k) : ℂ) * (F.q k : ℂ) ^ (-s)

/-- **The Epstein zeta** `Z(s) = ∑_{k ≠ 0} Q(k)^{−s}` of the form. -/
noncomputable def Z (F : BinForm) (s : ℂ) : ℂ := ∑' k, term F s k

/-- Its termwise derivative `Z'(s) = −∑_{k ≠ 0} log Q(k)·Q(k)^{−s}`. -/
noncomputable def Zd (F : BinForm) (s : ℂ) : ℂ := ∑' k, dterm F s k

theorem norm_term (s : ℂ) (k : ℤ × ℤ) : ‖term F s k‖ = maj F s.re k := by
  unfold term maj
  split_ifs with h
  · simp
  · rw [norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h), neg_re]

theorem norm_dterm (s : ℂ) (k : ℤ × ℤ) : ‖dterm F s k‖ = lmaj F 1 s.re k := by
  unfold dterm lmaj
  split_ifs with h
  · simp
  · have : (1 : ℝ) ≤ F.q k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg this),
      norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h), neg_re, pow_one]

theorem hasDerivAt_term (s : ℂ) (k : ℤ × ℤ) : HasDerivAt (fun w => term F w k) (dterm F s k) s := by
  unfold term dterm
  split_ifs with h
  · exact hasDerivAt_const s 0
  · have hq : (F.q k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h
    have h2 : HasDerivAt (fun w : ℂ => -w) (-1) s := (hasDerivAt_id' s).neg
    have := h2.const_cpow (c := (F.q k : ℂ)) (Or.inl hq)
    convert this using 1
    rw [← Complex.natCast_log]
    ring

/-- **`Z` is differentiable past `1`** with derivative `Z'`. -/
theorem Coercive.hasDerivAt_Z (hF : Coercive F lN lD hi) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (Z F) (Zd F s) s := by
  set σ₁ := (1 + s.re) / 2 with hσ₁
  have h1 : 1 < σ₁ := by rw [hσ₁]; linarith
  have h2 : σ₁ < s.re := by rw [hσ₁]; linarith
  have ht : IsOpen {w : ℂ | σ₁ < w.re} := isOpen_lt continuous_const Complex.continuous_re
  refine hasDerivAt_tsum_of_isPreconnected (hF.summable_lmaj 1 h1) ht
    (convex_halfSpace_re_gt σ₁).isPreconnected (fun k w _ => hasDerivAt_term w k)
    (fun k w hw => ?_) h2 ?_ h2
  · rw [norm_dterm]
    unfold lmaj
    split_ifs with h
    · exact le_rfl
    · have hq1 : (1 : ℝ) ≤ F.q k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
      have hw' : σ₁ < w.re := hw
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)) (pow_nonneg (Real.log_nonneg hq1) _)
  · exact (hF.summable_maj (by linarith : 1 < s.re)).of_norm_bounded
      (fun k => (norm_term s k).le) |>.congr fun k => rfl

/-- The second termwise derivative, `(log Q)²·Q^{−s}`. -/
noncomputable def ddterm (F : BinForm) (s : ℂ) (k : ℤ × ℤ) : ℂ :=
  if F.q k = 0 then 0 else (Real.log (F.q k) : ℂ) ^ 2 * (F.q k : ℂ) ^ (-s)

theorem hasDerivAt_dterm (s : ℂ) (k : ℤ × ℤ) :
    HasDerivAt (fun w => dterm F w k) (ddterm F s k) s := by
  unfold dterm ddterm
  split_ifs with h
  · exact hasDerivAt_const s 0
  · have hq : (F.q k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h
    have h2 : HasDerivAt (fun w : ℂ => -w) (-1) s := (hasDerivAt_id' s).neg
    have := (h2.const_cpow (c := (F.q k : ℂ)) (Or.inl hq)).const_mul (-(Real.log (F.q k) : ℂ))
    refine this.congr_deriv ?_
    rw [← Complex.natCast_log]
    ring

theorem norm_ddterm (s : ℂ) (k : ℤ × ℤ) : ‖ddterm F s k‖ = lmaj F 2 s.re k := by
  unfold ddterm lmaj
  split_ifs with h
  · simp
  · rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h), neg_re]

theorem lmaj_anti (j : ℕ) {σ σ' : ℝ} (h : σ ≤ σ') (k : ℤ × ℤ) : lmaj F j σ' k ≤ lmaj F j σ k := by
  unfold lmaj
  split_ifs with hq
  · exact le_rfl
  · have hq1 : (1 : ℝ) ≤ F.q k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith))
      (pow_nonneg (Real.log_nonneg hq1) _)

/-- Points of the disc `|z − z₀| ≤ ρ` have real part at least `Re z₀ − ρ`. -/
theorem re_ge_of_mem_closedBall {z z₀ : ℂ} {ρ : ℝ} (hz : z ∈ closedBall z₀ ρ) :
    z₀.re - ρ ≤ z.re := by
  have h1 : z₀.re - z.re ≤ ‖z - z₀‖ := by
    have := Complex.abs_re_le_norm (z₀ - z)
    rw [Complex.sub_re] at this
    rw [norm_sub_rev]
    exact (le_abs_self _).trans this
  have h2 : ‖z - z₀‖ ≤ ρ := mem_closedBall_iff_norm.mp hz
  linarith

/-- **The derivative moves slowly on the disc**: each term of `Z'` changes by at
most `ρ·(log Q)²·Q^{−(Re z₀ − ρ)}`. -/
theorem norm_dterm_sub_le {z z₀ : ℂ} {ρ : ℝ} (hz : z ∈ closedBall z₀ ρ) (k : ℤ × ℤ) :
    ‖dterm F z k - dterm F z₀ k‖ ≤ lmaj F 2 (z₀.re - ρ) k * ρ := by
  have hρ : 0 ≤ ρ := (dist_nonneg).trans (mem_closedBall.mp hz)
  have h := (convex_closedBall z₀ ρ).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun w => dterm F w k) (f' := fun w => ddterm F w k)
    (fun w _ => (hasDerivAt_dterm w k).hasDerivWithinAt)
    (fun w hw => by rw [norm_ddterm]; exact lmaj_anti 2 (re_ge_of_mem_closedBall hw) k)
    (mem_closedBall_self hρ) hz
  exact h.trans (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.mp hz) (lmaj_nonneg 2 _ k))

/-- **THE ZERO CRITERION**: a zero of `Z` in the disc `|z − z₀| ≤ ρ` follows from
three numbers — `‖Z(z₀)‖`, `‖Z'(z₀) − c‖`, and a bound `B₂` on
`∑ (log Q)²·Q^{−(Re z₀ − ρ)}` — through the Newton certificate. -/
theorem Coercive.exists_zero (hF : Coercive F lN lD hi) {z₀ c : ℂ} {ρ q B₂ : ℝ} (hρ : 0 < ρ)
    (hq : q < 1) (hc : c ≠ 0) (hσ : 1 < z₀.re - ρ)
    (hB₂ : ∑' k, lmaj F 2 (z₀.re - ρ) k ≤ B₂)
    (hval : ‖Z F z₀‖ ≤ (1 - q) * ρ * ‖c‖)
    (hder : ‖Zd F z₀ - c‖ + ρ * B₂ ≤ q * ‖c‖) :
    ∃ z ∈ closedBall z₀ ρ, Z F z = 0 := by
  have hre : ∀ z ∈ closedBall z₀ ρ, 1 < z.re := fun z hz =>
    lt_of_lt_of_le hσ (re_ge_of_mem_closedBall hz)
  have hsumd : ∀ w : ℂ, 1 < w.re → Summable (fun k => dterm F w k) := fun w hw =>
    (hF.summable_lmaj 1 hw).of_norm_bounded (fun k => (norm_dterm w k).le)
  refine exists_zero_of_newton hρ hq hc (f' := Zd F) (fun z hz => hF.hasDerivAt_Z (hre z hz))
    (fun z hz => ?_) hval
  have hz0 : z₀ ∈ closedBall z₀ ρ := mem_closedBall_self hρ.le
  have hmaj := hF.summable_lmaj 2 hσ
  have hdiff : Zd F z - Zd F z₀ = ∑' k, (dterm F z k - dterm F z₀ k) :=
    ((hsumd z (hre z hz)).tsum_sub (hsumd z₀ (hre z₀ hz0))).symm
  have hbound : ‖Zd F z - Zd F z₀‖ ≤ ρ * B₂ := by
    rw [hdiff]
    have hs : Summable (fun k => lmaj F 2 (z₀.re - ρ) k * ρ) := hmaj.mul_right ρ
    calc ‖∑' k, (dterm F z k - dterm F z₀ k)‖
        ≤ ∑' k, lmaj F 2 (z₀.re - ρ) k * ρ :=
          tsum_of_norm_bounded hs.hasSum fun k => norm_dterm_sub_le hz k
      _ = ρ * ∑' k, lmaj F 2 (z₀.re - ρ) k := by rw [tsum_mul_right, mul_comm]
      _ ≤ ρ * B₂ := mul_le_mul_of_nonneg_left hB₂ hρ.le
  calc ‖Zd F z - c‖ = ‖(Zd F z - Zd F z₀) + (Zd F z₀ - c)‖ := by ring_nf
    _ ≤ ‖Zd F z - Zd F z₀‖ + ‖Zd F z₀ - c‖ := norm_add_le _ _
    _ ≤ q * ‖c‖ := by linarith

/-! ## Splitting at a cutoff -/

theorem lmaj_zero (σ : ℝ) (k : ℤ × ℤ) : lmaj F 0 σ k = maj F σ k := by
  simp [lmaj, maj]

theorem summable_ite_gt {g : ℤ × ℤ → ℝ} (hg : Summable g) (hg0 : ∀ k, 0 ≤ g k) (N : ℕ) :
    Summable (fun k => if N < F.q k then g k else 0) :=
  hg.of_nonneg_of_le (fun k => by split_ifs <;> first | exact hg0 k | exact le_rfl)
    (fun k => by split_ifs <;> first | exact le_rfl | exact hg0 k)

/-- **The log-weighted tail**: past `N`, `∑ (log Q)^j·Q^{−σ}` is at most `(eτ)^{−j}`
times the shell bound at any `σ' ∈ (1, σ − jτ]`. -/
theorem Coercive.ltail_le (hF : Coercive F lN lD hi) (j : ℕ) {σ τ σ' : ℝ} (hτ : 0 < τ)
    (hσ' : 1 < σ') (hσσ' : σ' ≤ σ - j * τ) {N m₀ : ℕ} (hm₀ : 2 ≤ m₀)
    (hN : hi * (m₀ - 1) ^ 2 ≤ N) :
    ∑' k, (if N < F.q k then lmaj F j σ k else 0)
      ≤ (1 / (Real.exp 1 * τ)) ^ j *
        (8 * ((lD : ℝ) / lN) ^ σ' * (((m₀ : ℝ) - 1) ^ (2 - 2 * σ') / (2 * σ' - 2))) := by
  have hs := summable_ite_gt (F := F) (hF.summable_maj hσ') (maj_nonneg σ') N
  have hb : ∀ k, (if N < F.q k then lmaj F j σ k else 0)
      ≤ (1 / (Real.exp 1 * τ)) ^ j * (if N < F.q k then maj F σ' k else 0) := fun k => by
    split_ifs
    · refine (lmaj_le j hτ σ k).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      rw [← lmaj_zero, ← lmaj_zero]
      exact lmaj_anti 0 hσσ' k
    · simp
  calc ∑' k, (if N < F.q k then lmaj F j σ k else 0)
      ≤ ∑' k, (1 / (Real.exp 1 * τ)) ^ j * (if N < F.q k then maj F σ' k else 0) :=
        Summable.tsum_le_tsum hb ((hs.mul_left _).of_nonneg_of_le
          (fun k => by split_ifs <;> first | exact lmaj_nonneg j σ k | exact le_rfl) hb)
          (hs.mul_left _)
    _ = (1 / (Real.exp 1 * τ)) ^ j * ∑' k, (if N < F.q k then maj F σ' k else 0) :=
        tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (hF.tail_le hσ' hm₀ hN) (by positivity)

/-- Every lattice point with `Q(k) ≤ N` lies in the square `[−B, B]²` once
`lD·N < lN·(B + 1)²`. -/
theorem Coercive.mem_Icc_of_q_le (hF : Coercive F lN lD hi) {N B : ℕ}
    (hB : lD * N < lN * (B + 1) ^ 2) {k : ℤ × ℤ} (hk : F.q k ≤ N) :
    k ∈ Icc (-(B : ℤ × ℤ)) B := by
  have h1 : lN * supNorm k ^ 2 < lN * (B + 1) ^ 2 :=
    lt_of_le_of_lt ((hF.lower k).trans (Nat.mul_le_mul_left _ hk)) hB
  have h2 : supNorm k < B + 1 :=
    (Nat.pow_lt_pow_iff_left (by norm_num)).mp (Nat.lt_of_mul_lt_mul_left h1)
  have ha : k.1.natAbs ≤ B := by unfold supNorm at h2; omega
  have hb : k.2.natAbs ≤ B := by unfold supNorm at h2; omega
  simp only [mem_Icc, Prod.le_def, Prod.fst_neg, Prod.snd_neg, Prod.fst_natCast,
    Prod.snd_natCast]
  omega

/-- **The cutoff split**: a dominated lattice sum is its part over `Q ≤ N`,
a finite sum over the square, plus its tail past `N`. -/
theorem Coercive.tsum_split (hF : Coercive F lN lD hi) {N B : ℕ}
    (hB : lD * N < lN * (B + 1) ^ 2) {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {f : ℤ × ℤ → E} {g : ℤ × ℤ → ℝ} (hfg : ∀ k, ‖f k‖ ≤ g k) (hg : Summable g) :
    ∑' k, f k = ∑ k ∈ Icc (-(B : ℤ × ℤ)) B, (if F.q k ≤ N then f k else 0)
      + ∑' k, (if N < F.q k then f k else 0) := by
  have hs : ∀ p : ℤ × ℤ → Prop, [DecidablePred p] → Summable (fun k => if p k then f k else 0) :=
    fun p _ => hg.of_norm_bounded fun k => by
      split_ifs
      · exact hfg k
      · simpa using (norm_nonneg _).trans (hfg k)
  have hsplit : ∀ k, f k = (if F.q k ≤ N then f k else 0) + (if N < F.q k then f k else 0) :=
    fun k => by split_ifs <;> first | omega | simp
  rw [tsum_congr hsplit, Summable.tsum_add (hs _) (hs _),
    tsum_eq_sum (s := Icc (-(B : ℤ × ℤ)) B) fun k hk =>
      ite_eq_right fun hq => hk (hF.mem_Icc_of_q_le hB hq)]

/-- The tail of a dominated sum is dominated by the tail of the majorant. -/
theorem norm_tsum_ite_le {E : Type*} [NormedAddCommGroup E] {f : ℤ × ℤ → E} {g : ℤ × ℤ → ℝ}
    (hfg : ∀ k, ‖f k‖ ≤ g k) (hg : Summable g) (hg0 : ∀ k, 0 ≤ g k) (N : ℕ) :
    ‖∑' k, (if N < F.q k then f k else 0)‖ ≤ ∑' k, (if N < F.q k then g k else 0) :=
  tsum_of_norm_bounded (summable_ite_gt hg hg0 N).hasSum fun k => by
    split_ifs
    · exact hfg k
    · simp

end Epstein

end Meno
