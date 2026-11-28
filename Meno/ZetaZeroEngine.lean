import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Kernel interval arithmetic for the certified zero

Nonnegative fixed-point intervals on the grid `1/U`, computed with `Nat`
primitives only (which the kernel evaluates natively), each operation
rounded outward. `Iv.Mem a x` says `x ∈ [a.lo/U, a.hi/U]`; every operation
carries a soundness lemma, and the transcendental enclosures (log, exp,
cos/sin) rest on Mathlib's series identities and remainder bounds. The unit `U` is
a parameter so that no large literal sits inside a definition the kernel unfolds
while checking the soundness lemmas. -/

namespace Meno

namespace Engine

variable {U : ℕ} [Fact (0 < U)]

theorem U_pos : 0 < U := Fact.out

theorem U_real_pos : (0 : ℝ) < U := by exact_mod_cast (U_pos (U := U))

/-- Ceiling division. -/
def cd (a d : ℕ) : ℕ := (a + d - 1) / d

theorem le_cd_mul (a : ℕ) {d : ℕ} (hd : 0 < d) : a ≤ cd a d * d := by
  unfold cd
  have := Nat.lt_div_mul_add (a := a + d - 1) hd
  omega

theorem cd_real (a : ℕ) {d : ℕ} (hd : 0 < d) : (a : ℝ) / d ≤ cd a d := by
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast le_cd_mul a hd

theorem div_real (a : ℕ) {d : ℕ} (hd : 0 < d) : ((a / d : ℕ) : ℝ) ≤ (a : ℝ) / d := by
  rw [le_div_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast Nat.div_mul_le_self a d

/-- A nonnegative interval `[lo/U, hi/U]`. -/
structure Iv (U : ℕ) where
  lo : ℕ
  hi : ℕ
deriving DecidableEq

namespace Iv

/-- Membership of a real number. -/
def Mem (a : Iv U) (x : ℝ) : Prop := (a.lo : ℝ) / U ≤ x ∧ x ≤ (a.hi : ℝ) / U

theorem Mem.nonneg {a : Iv U} {x : ℝ} (h : a.Mem x) : 0 ≤ x :=
  le_trans (div_nonneg (Nat.cast_nonneg _) (U_real_pos (U := U)).le) h.1

def add (a b : Iv U) : Iv U := ⟨a.lo + b.lo, a.hi + b.hi⟩

omit [Fact (0 < U)] in
theorem mem_add {a b : Iv U} {x y : ℝ} (ha : a.Mem x) (hb : b.Mem y) : (a.add b).Mem (x + y) := by
  unfold Mem add at *
  push_cast
  constructor <;> rw [add_div] <;> linarith [ha.1, ha.2, hb.1, hb.2]

def mul (a b : Iv U) : Iv U := ⟨a.lo * b.lo / U, cd (a.hi * b.hi) U⟩

theorem mem_mul {a b : Iv U} {x y : ℝ} (ha : a.Mem x) (hb : b.Mem y) : (a.mul b).Mem (x * y) := by
  have hx := ha.nonneg
  have hy := hb.nonneg
  have hU := U_real_pos (U := U)
  unfold Mem mul at *
  constructor
  · calc (((a.lo * b.lo / U : ℕ) : ℝ)) / U ≤ ((a.lo * b.lo : ℕ) : ℝ) / U / U :=
          div_le_div_of_nonneg_right (div_real _ (U_pos (U := U))) hU.le
      _ = ((a.lo : ℝ) / U) * ((b.lo : ℝ) / U) := by push_cast; ring
      _ ≤ x * y := mul_le_mul ha.1 hb.1 (by positivity) hx
  · calc x * y ≤ ((a.hi : ℝ) / U) * ((b.hi : ℝ) / U) :=
          mul_le_mul ha.2 hb.2 hy (le_trans hx ha.2)
      _ = ((a.hi * b.hi : ℕ) : ℝ) / U / U := by push_cast; ring
      _ ≤ (cd (a.hi * b.hi) U : ℝ) / U :=
          div_le_div_of_nonneg_right (cd_real _ (U_pos (U := U))) hU.le

def divN (a : Iv U) (d : ℕ) : Iv U := ⟨a.lo / d, cd a.hi d⟩

theorem mem_divN {a : Iv U} {x : ℝ} (ha : a.Mem x) {d : ℕ} (hd : 0 < d) :
    (a.divN d).Mem (x / d) := by
  have hU := U_real_pos (U := U)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold Mem divN at *
  constructor
  · calc ((a.lo / d : ℕ) : ℝ) / U ≤ ((a.lo : ℝ) / d) / U :=
          div_le_div_of_nonneg_right (div_real _ hd) hU.le
      _ = ((a.lo : ℝ) / U) / d := by ring
      _ ≤ x / d := div_le_div_of_nonneg_right ha.1 hdR.le
  · calc x / d ≤ ((a.hi : ℝ) / U) / d := div_le_div_of_nonneg_right ha.2 hdR.le
      _ = ((a.hi : ℝ) / d) / U := by ring
      _ ≤ (cd a.hi d : ℝ) / U := div_le_div_of_nonneg_right (cd_real _ hd) hU.le

/-- The exact grid point `n/U`. -/
def pt (n : ℕ) : Iv U := ⟨n, n⟩

omit [Fact (0 < U)] in
theorem mem_pt (n : ℕ) : (pt (U := U) n).Mem ((n : ℝ) / U) := ⟨le_rfl, le_rfl⟩

end Iv

namespace Iv

/-! ## The exponential series -/

/-- Fold for `exp`: carries the term `t ≈ x^m/m!` and the partial sum. -/
def expGo (x : Iv U) : ℕ → Iv U → Iv U → ℕ → Iv U × Iv U
  | _, t, acc, 0 => (t, acc)
  | m, t, acc, f + 1 => expGo x (m + 1) ((t.mul x).divN (m + 1)) (acc.add t) f

theorem expGo_mem {x : Iv U} {r : ℝ} (hx : x.Mem r) :
    ∀ (f m : ℕ) (t acc : Iv U), t.Mem (r ^ m / m.factorial) →
      acc.Mem (∑ j ∈ Finset.range m, r ^ j / j.factorial) →
      (expGo x m t acc f).1.Mem (r ^ (m + f) / (m + f).factorial) ∧
      (expGo x m t acc f).2.Mem (∑ j ∈ Finset.range (m + f), r ^ j / j.factorial) := by
  intro f
  induction f with
  | zero => intro m t acc ht hacc; exact ⟨ht, hacc⟩
  | succ f ih =>
    intro m t acc ht hacc
    have ht' : ((t.mul x).divN (m + 1)).Mem (r ^ (m + 1) / (m + 1).factorial) := by
      have := mem_divN (mem_mul ht hx) (Nat.succ_pos m)
      convert this using 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    have hacc' : (acc.add t).Mem (∑ j ∈ Finset.range (m + 1), r ^ j / j.factorial) := by
      rw [Finset.sum_range_succ]
      exact mem_add hacc ht
    have := ih (m + 1) _ _ ht' hacc'
    simp only [expGo]
    rwa [show m + 1 + f = m + (f + 1) by ring] at this

/-- **Enclosure of `exp`** on `[0, 1]`: the `n`-term partial sum, widened by
the Taylor remainder `x^n/n!·(n+1)/n`. -/
def expE (x : Iv U) (n : ℕ) : Iv U :=
  let r := expGo x 0 (pt U) ⟨0, 0⟩ n
  ⟨r.2.lo, r.2.hi + cd (r.1.hi * (n + 1)) n⟩

theorem mem_expE {x : Iv U} {r : ℝ} (hx : x.Mem r) (h1 : r ≤ 1) {n : ℕ} (hn : 0 < n) :
    (x.expE n).Mem (Real.exp r) := by
  have hr0 := hx.nonneg
  have hU := U_real_pos (U := U)
  have h0 : (pt (U := U) U).Mem (r ^ 0 / (0 : ℕ).factorial) := by
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    exact ⟨by simp [pt, div_self hU.ne'], by simp [pt, div_self hU.ne']⟩
  have hz : (⟨0, 0⟩ : Iv U).Mem (∑ j ∈ Finset.range 0, r ^ j / j.factorial) := by
    simp [Mem]
  obtain ⟨ht, hs⟩ := expGo_mem hx n 0 (pt U) ⟨0, 0⟩ h0 hz
  rw [zero_add] at ht hs
  have hb := Real.exp_bound (x := r) (by rw [abs_of_nonneg hr0]; exact h1) hn
  rw [abs_of_nonneg hr0] at hb
  have hsum_le : (∑ j ∈ Finset.range n, r ^ j / j.factorial) ≤ Real.exp r := by
    have := Real.sum_le_exp_of_nonneg hr0 n
    exact this
  have hrem : r ^ n * (n.succ / (n.factorial * n)) ≤ (cd ((expGo x 0 (pt U) ⟨0, 0⟩ n).1.hi * (n + 1)) n : ℝ) / U := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    calc r ^ n * (n.succ / (n.factorial * n)) = (r ^ n / n.factorial) * (n + 1) / n := by
          push_cast; field_simp
      _ ≤ (((expGo x 0 (pt U) ⟨0, 0⟩ n).1.hi : ℝ) / U) * (n + 1) / n := by
          apply div_le_div_of_nonneg_right _ hnR.le
          exact mul_le_mul_of_nonneg_right ht.2 (by positivity)
      _ = (((expGo x 0 (pt U) ⟨0, 0⟩ n).1.hi * (n + 1) : ℕ) : ℝ) / n / U := by
          push_cast; ring
      _ ≤ _ := div_le_div_of_nonneg_right (cd_real _ hn) hU.le
  unfold expE Mem
  refine ⟨hs.1.trans hsum_le, ?_⟩
  have h2 := (abs_sub_le_iff.mp hb).1
  push_cast
  rw [add_div]
  linarith [hs.2]

end Iv

namespace Iv

/-! ## Cosine and sine -/

/-- The partial sums of `x^i/i!` over `i < m` with `i ≡ j (mod 4)`. -/
noncomputable def bucket (r : ℝ) (j m : ℕ) : ℝ :=
  ∑ i ∈ (Finset.range m).filter (fun i => i % 4 = j), r ^ i / i.factorial

theorem bucket_succ (r : ℝ) (j m : ℕ) :
    bucket r j (m + 1) = bucket r j m + if m % 4 = j then r ^ m / m.factorial else 0 := by
  unfold bucket
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.sum_insert (by simp)]; ring
  · ring

/-- **The complex partial sum in buckets**:
`∑_{i<m} (i r)^i/i! = (B₀ − B₂) + i(B₁ − B₃)`. -/
theorem sum_I_mul_pow (r : ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, ((r : ℂ) * Complex.I) ^ i / i.factorial
      = ((bucket r 0 m - bucket r 2 m : ℝ) : ℂ) + ((bucket r 1 m - bucket r 3 m : ℝ) : ℂ) * Complex.I := by
  induction m with
  | zero => simp [bucket]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, bucket_succ, bucket_succ, bucket_succ, bucket_succ]
    have hI : Complex.I ^ m = Complex.I ^ (m % 4) := by
      conv_lhs => rw [← Nat.div_add_mod m 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]
    rw [mul_pow, hI]
    have hm : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases hm with h | h | h | h <;> simp only [h] <;> norm_num <;> ring_nf

/-- Fold for cos/sin: the term and the four bucket sums. -/
def cisGo (x : Iv U) : ℕ → Iv U → Iv U → Iv U → Iv U → Iv U → ℕ → Iv U × Iv U × Iv U × Iv U × Iv U
  | _, t, b0, b1, b2, b3, 0 => (t, b0, b1, b2, b3)
  | m, t, b0, b1, b2, b3, f + 1 =>
    let t' := (t.mul x).divN (m + 1)
    match m % 4 with
    | 0 => cisGo x (m + 1) t' (b0.add t) b1 b2 b3 f
    | 1 => cisGo x (m + 1) t' b0 (b1.add t) b2 b3 f
    | 2 => cisGo x (m + 1) t' b0 b1 (b2.add t) b3 f
    | _ => cisGo x (m + 1) t' b0 b1 b2 (b3.add t) f

theorem cisGo_mem {x : Iv U} {r : ℝ} (hx : x.Mem r) :
    ∀ (f m : ℕ) (t b0 b1 b2 b3 : Iv U), t.Mem (r ^ m / m.factorial) →
      b0.Mem (bucket r 0 m) → b1.Mem (bucket r 1 m) → b2.Mem (bucket r 2 m) →
      b3.Mem (bucket r 3 m) →
      let o := cisGo x m t b0 b1 b2 b3 f
      o.1.Mem (r ^ (m + f) / (m + f).factorial) ∧ o.2.1.Mem (bucket r 0 (m + f)) ∧
      o.2.2.1.Mem (bucket r 1 (m + f)) ∧ o.2.2.2.1.Mem (bucket r 2 (m + f)) ∧
      o.2.2.2.2.Mem (bucket r 3 (m + f)) := by
  intro f
  induction f with
  | zero => intro m t b0 b1 b2 b3 ht h0 h1 h2 h3; exact ⟨ht, h0, h1, h2, h3⟩
  | succ f ih =>
    intro m t b0 b1 b2 b3 ht h0 h1 h2 h3
    have ht' : ((t.mul x).divN (m + 1)).Mem (r ^ (m + 1) / (m + 1).factorial) := by
      have := mem_divN (mem_mul ht hx) (Nat.succ_pos m)
      convert this using 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    have key : ∀ j, ∀ b : Iv U, b.Mem (bucket r j m) →
        (if m % 4 = j then b.add t else b).Mem (bucket r j (m + 1)) := by
      intro j b hb
      rw [bucket_succ]
      split_ifs
      · exact mem_add hb ht
      · simpa using hb
    rw [show m + (f + 1) = m + 1 + f by ring]
    have k0 := key 0 b0 h0
    have k1 := key 1 b1 h1
    have k2 := key 2 b2 h2
    have k3 := key 3 b3 h3
    simp only [cisGo]
    have hm : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases hm with hmod | hmod | hmod | hmod <;> simp only [hmod] at k0 k1 k2 k3 ⊢ <;>
      simp only [ite_true, ite_false, reduceCtorEq, OfNat.ofNat_ne_zero, zero_ne_one] at k0 k1 k2 k3 <;>
      first
      | exact ih (m + 1) _ _ _ _ _ ht' k0 k1 k2 k3

/-- **Enclosures of `cos` and `sin`** on `[0, 1]`: bucket differences widened
by the complex Taylor remainder. -/
def cisE (x : Iv U) (n : ℕ) : Iv U × Iv U :=
  let o := cisGo x 0 (pt U) ⟨0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩ n
  let rem := cd (o.1.hi * (n + 1)) n
  (⟨o.2.1.lo - (o.2.2.2.1.hi + rem), o.2.1.hi + rem - o.2.2.2.1.lo⟩,
   ⟨o.2.2.1.lo - (o.2.2.2.2.hi + rem), o.2.2.1.hi + rem - o.2.2.2.2.lo⟩)

/-- A nonnegative real squeezed by `(a − b ± e)/U` lies in the truncated interval. -/
theorem mem_sub_trunc {y A B : ℝ} {alo ahi blo bhi e : ℕ} (hy : 0 ≤ y)
    (hA : (alo : ℝ) / U ≤ A ∧ A ≤ (ahi : ℝ) / U) (hB : (blo : ℝ) / U ≤ B ∧ B ≤ (bhi : ℝ) / U)
    (hlo : A - B - (e : ℝ) / U ≤ y) (hhi : y ≤ A - B + (e : ℝ) / U) :
    (⟨alo - (bhi + e), ahi + e - blo⟩ : Iv U).Mem y := by
  have hU := U_real_pos (U := U)
  constructor
  · show ((alo - (bhi + e) : ℕ) : ℝ) / U ≤ y
    rcases Nat.lt_or_ge alo (bhi + e) with h | h
    · rw [Nat.sub_eq_zero_of_le h.le]; simpa using hy
    · rw [Nat.cast_sub h, sub_div]
      push_cast
      rw [add_div]
      linarith [hA.1, hB.2]
  · show y ≤ ((ahi + e - blo : ℕ) : ℝ) / U
    have h1 : (blo : ℝ) / U ≤ (ahi : ℝ) / U + (e : ℝ) / U := by linarith [hA.2, hB.1]
    have h2 : blo ≤ ahi + e := by
      rw [← add_div, div_le_div_iff_of_pos_right hU] at h1
      exact_mod_cast h1
    rw [Nat.cast_sub h2, sub_div]
    push_cast
    rw [add_div]
    linarith [hA.2, hB.1]

theorem mem_cisE {x : Iv U} {r : ℝ} (hx : x.Mem r) (h1 : r ≤ 1) {n : ℕ} (hn : 0 < n) :
    (x.cisE n).1.Mem (Real.cos r) ∧ (x.cisE n).2.Mem (Real.sin r) := by
  have hr0 := hx.nonneg
  have hU := U_real_pos (U := U)
  have h0 : (pt (U := U) U).Mem (r ^ 0 / (0 : ℕ).factorial) := by
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    exact ⟨by simp [pt, div_self hU.ne'], by simp [pt, div_self hU.ne']⟩
  have hz : ∀ j, (⟨0, 0⟩ : Iv U).Mem (bucket r j 0) := fun j => by simp [Mem, bucket]
  obtain ⟨ht, hb0, hb1, hb2, hb3⟩ :=
    cisGo_mem hx n 0 (pt U) ⟨0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩ h0 (hz 0) (hz 1) (hz 2) (hz 3)
  simp only [zero_add] at ht hb0 hb1 hb2 hb3
  set o := cisGo x 0 (pt U) ⟨0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩ ⟨0, 0⟩ n with ho
  have hnorm : ‖((r : ℂ) * Complex.I)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hr0]
    exact h1
  have hb := Complex.exp_bound hnorm hn
  rw [sum_I_mul_pow, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hr0] at hb
  have hrem : r ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) ≤ (cd (o.1.hi * (n + 1)) n : ℝ) / U := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    calc r ^ n * ((n.succ : ℝ) * (n.factorial * n : ℝ)⁻¹) = (r ^ n / n.factorial) * (n + 1) / n := by
          push_cast; field_simp
      _ ≤ ((o.1.hi : ℝ) / U) * (n + 1) / n := by
          apply div_le_div_of_nonneg_right _ hnR.le
          exact mul_le_mul_of_nonneg_right ht.2 (by positivity)
      _ = ((o.1.hi * (n + 1) : ℕ) : ℝ) / n / U := by push_cast; ring
      _ ≤ _ := div_le_div_of_nonneg_right (cd_real _ hn) hU.le
  have hexp : Complex.exp ((r : ℂ) * Complex.I) = (Real.cos r : ℂ) + (Real.sin r : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hexp] at hb
  set e := cd (o.1.hi * (n + 1)) n
  have hre : |Real.cos r - (bucket r 0 n - bucket r 2 n)| ≤ (e : ℝ) / U := by
    refine le_trans ?_ (hb.trans hrem)
    have := Complex.abs_re_le_norm ((Real.cos r : ℂ) + (Real.sin r : ℂ) * Complex.I -
      (((bucket r 0 n - bucket r 2 n : ℝ) : ℂ) + ((bucket r 1 n - bucket r 3 n : ℝ) : ℂ) * Complex.I))
    simpa [Complex.cos_ofReal_re, Complex.sin_ofReal_re] using this
  have him : |Real.sin r - (bucket r 1 n - bucket r 3 n)| ≤ (e : ℝ) / U := by
    refine le_trans ?_ (hb.trans hrem)
    have := Complex.abs_im_le_norm ((Real.cos r : ℂ) + (Real.sin r : ℂ) * Complex.I -
      (((bucket r 0 n - bucket r 2 n : ℝ) : ℂ) + ((bucket r 1 n - bucket r 3 n : ℝ) : ℂ) * Complex.I))
    simpa [Complex.cos_ofReal_re, Complex.sin_ofReal_re] using this
  have hcos0 : 0 ≤ Real.cos r := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_gt_three], by linarith [Real.pi_gt_three]⟩
  have hsin0 : 0 ≤ Real.sin r := Real.sin_nonneg_of_nonneg_of_le_pi hr0 (by linarith [Real.pi_gt_three])
  constructor
  · exact mem_sub_trunc hcos0 hb0 hb2 (by linarith [(abs_le.mp hre).1]) (by linarith [(abs_le.mp hre).2])
  · exact mem_sub_trunc hsin0 hb1 hb3 (by linarith [(abs_le.mp him).1]) (by linarith [(abs_le.mp him).2])

end Iv

namespace Iv

/-! ## The logarithm -/

/-- Fold for `atanh`: carries `p ≈ z^{2j+1}` and `∑_{i<j} z^{2i+1}/(2i+1)`. -/
def atGo (z2 : Iv U) : ℕ → Iv U → Iv U → ℕ → Iv U × Iv U
  | _, p, acc, 0 => (p, acc)
  | j, p, acc, f + 1 => atGo z2 (j + 1) (p.mul z2) (acc.add (p.divN (2 * j + 1))) f

theorem atGo_mem {z2 : Iv U} {z : ℝ} (hz2 : z2.Mem (z ^ 2)) :
    ∀ (f j : ℕ) (p acc : Iv U), p.Mem (z ^ (2 * j + 1)) →
      acc.Mem (∑ i ∈ Finset.range j, z ^ (2 * i + 1) / (2 * i + 1 : ℕ)) →
      (atGo z2 j p acc f).1.Mem (z ^ (2 * (j + f) + 1)) ∧
      (atGo z2 j p acc f).2.Mem (∑ i ∈ Finset.range (j + f), z ^ (2 * i + 1) / (2 * i + 1 : ℕ)) := by
  intro f
  induction f with
  | zero => intro j p acc hp hacc; exact ⟨hp, hacc⟩
  | succ f ih =>
    intro j p acc hp hacc
    have hp' : (p.mul z2).Mem (z ^ (2 * (j + 1) + 1)) := by
      have := mem_mul hp hz2
      convert this using 1
      ring
    have hacc' : (acc.add (p.divN (2 * j + 1))).Mem
        (∑ i ∈ Finset.range (j + 1), z ^ (2 * i + 1) / (2 * i + 1 : ℕ)) := by
      rw [Finset.sum_range_succ]
      exact mem_add hacc (mem_divN hp (by omega))
    have := ih (j + 1) _ _ hp' hacc'
    simp only [atGo]
    rwa [show j + 1 + f = j + (f + 1) by ring] at this

/-- **The atanh bounds**: for `0 ≤ z ≤ 1/3`,
`2·S_J ≤ log(1+z) − log(1−z) ≤ 2·S_J + (9/4)·z^{2J+1}`. -/
theorem log_atanh_bounds {z : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ 1 / 3) (J : ℕ) :
    2 * ∑ i ∈ Finset.range J, z ^ (2 * i + 1) / (2 * i + 1 : ℕ) ≤ Real.log (1 + z) - Real.log (1 - z) ∧
    Real.log (1 + z) - Real.log (1 - z)
      ≤ 2 * ∑ i ∈ Finset.range J, z ^ (2 * i + 1) / (2 * i + 1 : ℕ) + 9 / 4 * z ^ (2 * J + 1) := by
  have habs : |z| < 1 := by rw [abs_of_nonneg h0]; linarith
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one habs
  set g : ℕ → ℝ := fun k => 2 * (1 / (2 * k + 1)) * z ^ (2 * k + 1) with hg
  have hg0 : ∀ k, 0 ≤ g k := fun k => by rw [hg]; positivity
  have hpart : ∑ i ∈ Finset.range J, g i = 2 * ∑ i ∈ Finset.range J, z ^ (2 * i + 1) / (2 * i + 1 : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hg]; push_cast; ring
  constructor
  · rw [← hpart]; exact sum_le_hasSum _ (fun k _ => hg0 k) hs
  · have hz2 : z ^ 2 < 1 := by nlinarith
    have hgeo : HasSum (fun k : ℕ => 2 * z ^ (2 * J + 1) * (z ^ 2) ^ k)
        (2 * z ^ (2 * J + 1) * (1 - z ^ 2)⁻¹) :=
      (hasSum_geometric_of_lt_one (by positivity) hz2).mul_left _
    have htail_le : ∀ k, g (k + J) ≤ 2 * z ^ (2 * J + 1) * (z ^ 2) ^ k := fun k => by
      rw [hg]
      have : z ^ (2 * (k + J : ℕ) + 1) = z ^ (2 * J + 1) * (z ^ 2) ^ k := by
        rw [← pow_mul, ← pow_add]; congr 1; ring
      push_cast
      rw [show 2 * ((k : ℝ) + J) + 1 = ((2 * (k + J) + 1 : ℕ) : ℝ) by push_cast; ring, this]
      calc 2 * (1 / ((2 * (k + J) + 1 : ℕ) : ℝ)) * (z ^ (2 * J + 1) * (z ^ 2) ^ k)
          ≤ 2 * 1 * (z ^ (2 * J + 1) * (z ^ 2) ^ k) := by
            gcongr
            rw [div_le_one (by positivity)]
            exact_mod_cast (by omega : 1 ≤ 2 * (k + J) + 1)
        _ = 2 * z ^ (2 * J + 1) * (z ^ 2) ^ k := by ring
    have hsplit := (hs.summable.sum_add_tsum_nat_add J)
    rw [hs.tsum_eq] at hsplit
    have htail : ∑' k, g (k + J) ≤ 2 * z ^ (2 * J + 1) * (1 - z ^ 2)⁻¹ :=
      ((hs.summable.comp_injective (add_left_injective J)).tsum_le_tsum htail_le hgeo.summable).trans
        hgeo.tsum_eq.le
    have hinv : (1 - z ^ 2)⁻¹ ≤ 9 / 8 := by
      rw [inv_le_comm₀ (by nlinarith) (by norm_num)]
      nlinarith
    rw [← hsplit, hpart]
    have : 2 * z ^ (2 * J + 1) * (1 - z ^ 2)⁻¹ ≤ 9 / 4 * z ^ (2 * J + 1) := by
      have hzp : 0 ≤ z ^ (2 * J + 1) := by positivity
      nlinarith
    linarith

/-- The fixed-point enclosure of the rational `a/b`. -/
def ofFrac (a b : ℕ) : Iv U := ⟨a * U / b, cd (a * U) b⟩

theorem mem_ofFrac (a : ℕ) {b : ℕ} (hb : 0 < b) : (ofFrac (U := U) a b).Mem ((a : ℝ) / b) := by
  have hU := U_real_pos (U := U)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  unfold ofFrac Mem
  constructor
  · calc (((a * U / b : ℕ)) : ℝ) / U ≤ ((a * U : ℕ) : ℝ) / b / U :=
          div_le_div_of_nonneg_right (div_real _ hb) hU.le
      _ = (a : ℝ) / b := by push_cast; field_simp
  · calc (a : ℝ) / b = ((a * U : ℕ) : ℝ) / b / U := by push_cast; field_simp
      _ ≤ (cd (a * U) b : ℝ) / U := div_le_div_of_nonneg_right (cd_real _ hb) hU.le

/-- The `log 2` enclosure from the series at `z = 1/3`. -/
def log2E (J : ℕ) : Iv U :=
  let z : Iv U := ofFrac 1 3
  let o := atGo (z.mul z) 0 z ⟨0, 0⟩ J
  ⟨2 * o.2.lo, 2 * o.2.hi + cd (o.1.hi * 9) 4⟩

theorem mem_log2E (J : ℕ) : (log2E (U := U) J).Mem (Real.log 2) := by
  have hU := U_real_pos (U := U)
  have hz := mem_ofFrac (U := U) 1 (by norm_num : 0 < 3)
  push_cast at hz
  have hz2 : ((ofFrac (U := U) 1 3).mul (ofFrac (U := U) 1 3)).Mem ((1 / 3 : ℝ) ^ 2) := by
    rw [sq]; exact mem_mul hz hz
  have h0 : (⟨0, 0⟩ : Iv U).Mem (∑ i ∈ Finset.range 0, (1 / 3 : ℝ) ^ (2 * i + 1) / (2 * i + 1 : ℕ)) := by
    simp [Mem]
  obtain ⟨hp, hacc⟩ := atGo_mem hz2 J 0 (ofFrac (U := U) 1 3) ⟨0, 0⟩ (by simpa using hz) h0
  simp only [zero_add] at hp hacc
  obtain ⟨hlo, hhi⟩ := log_atanh_bounds (z := 1 / 3) (by norm_num) le_rfl J
  have hlog : Real.log (1 + 1 / 3) - Real.log (1 - 1 / 3) = Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [hlog] at hlo hhi
  unfold log2E Mem
  push_cast
  constructor
  · rw [mul_div_assoc]; linarith [hacc.1]
  · calc Real.log 2 ≤ 2 * ∑ i ∈ Finset.range J, (1 / 3 : ℝ) ^ (2 * i + 1) / (2 * i + 1 : ℕ)
          + 9 / 4 * (1 / 3) ^ (2 * J + 1) := hhi
      _ ≤ 2 * ((((atGo ((ofFrac (U := U) 1 3).mul (ofFrac (U := U) 1 3)) 0 (ofFrac (U := U) 1 3) ⟨0, 0⟩ J).2.hi : ℕ) : ℝ) / U)
          + ((cd ((atGo ((ofFrac (U := U) 1 3).mul (ofFrac (U := U) 1 3)) 0 (ofFrac (U := U) 1 3) ⟨0, 0⟩ J).1.hi * 9) 4 : ℕ) : ℝ) / U := by
          gcongr
          · exact hacc.2
          · calc 9 / 4 * (1 / 3 : ℝ) ^ (2 * J + 1)
                ≤ 9 / 4 * ((((atGo ((ofFrac (U := U) 1 3).mul (ofFrac (U := U) 1 3)) 0 (ofFrac (U := U) 1 3) ⟨0, 0⟩ J).1.hi : ℕ) : ℝ) / U) := by
                  gcongr; exact hp.2
              _ = ((((atGo ((ofFrac (U := U) 1 3).mul (ofFrac (U := U) 1 3)) 0 (ofFrac (U := U) 1 3) ⟨0, 0⟩ J).1.hi * 9 : ℕ) : ℝ) / 4) / U := by
                  push_cast; ring
              _ ≤ _ := div_le_div_of_nonneg_right (cd_real _ (by norm_num)) hU.le
      _ = _ := by ring

end Iv

namespace Iv

/-- **The enclosure of `log q`**: `q = 2^e·(1+z)/(1−z)` with
`z = (q − 2^e)/(q + 2^e) < 1/3`, so `log q = e·log 2 + 2·atanh z`. -/
def logE (L2 : Iv U) (q J : ℕ) : Iv U :=
  let e := Nat.log2 q
  let z : Iv U := ofFrac (q - 2 ^ e) (q + 2 ^ e)
  let o := atGo (z.mul z) 0 z ⟨0, 0⟩ J
  ⟨e * L2.lo + 2 * o.2.lo, e * L2.hi + 2 * o.2.hi + cd (o.1.hi * 9) 4⟩

theorem mem_logE {L2 : Iv U} (hL2 : L2.Mem (Real.log 2)) {q : ℕ} (hq : 0 < q) (J : ℕ) :
    (logE L2 q J).Mem (Real.log q) := by
  have hU := U_real_pos (U := U)
  set e := Nat.log2 q with he
  have hle : 2 ^ e ≤ q := Nat.log2_self_le hq.ne'
  have hlt : q < 2 ^ (e + 1) := Nat.lt_log2_self
  have hb : 0 < q + 2 ^ e := by positivity
  have hz := mem_ofFrac (U := U) (q - 2 ^ e) hb
  set z : ℝ := ((q - 2 ^ e : ℕ) : ℝ) / ((q + 2 ^ e : ℕ) : ℝ) with hzdef
  have hqR : (2 : ℝ) ^ e ≤ q := by exact_mod_cast hle
  have hqR' : (q : ℝ) < 2 ^ (e + 1) := by exact_mod_cast hlt
  have hz0 : 0 ≤ z := by positivity
  have hz1 : z ≤ 1 / 3 := by
    rw [hzdef, div_le_iff₀ (by positivity)]
    push_cast [Nat.cast_sub hle]
    rw [pow_succ] at hqR'
    linarith
  have hz2 : ((ofFrac (U := U) (q - 2 ^ e) (q + 2 ^ e)).mul (ofFrac (U := U) (q - 2 ^ e) (q + 2 ^ e))).Mem (z ^ 2) := by
    rw [sq]; exact mem_mul hz hz
  have h0 : (⟨0, 0⟩ : Iv U).Mem (∑ i ∈ Finset.range 0, z ^ (2 * i + 1) / (2 * i + 1 : ℕ)) := by simp [Mem]
  obtain ⟨hp, hacc⟩ := atGo_mem hz2 J 0 _ ⟨0, 0⟩ (by simpa using hz) h0
  simp only [zero_add] at hp hacc
  obtain ⟨hlo, hhi⟩ := log_atanh_bounds hz0 hz1 J
  have hdecomp : Real.log q = e * Real.log 2 + (Real.log (1 + z) - Real.log (1 - z)) := by
    have h1 : 1 + z = 2 * q / ((q + 2 ^ e : ℕ) : ℝ) := by
      rw [hzdef]; field_simp; push_cast [Nat.cast_sub hle]; ring
    have h2 : 1 - z = 2 * 2 ^ e / ((q + 2 ^ e : ℕ) : ℝ) := by
      rw [hzdef]; field_simp; push_cast [Nat.cast_sub hle]; ring
    rw [h1, h2, ← Real.log_div (by positivity) (by positivity)]
    rw [show 2 * (q : ℝ) / ((q + 2 ^ e : ℕ) : ℝ) / (2 * 2 ^ e / ((q + 2 ^ e : ℕ) : ℝ)) = q / 2 ^ e by
      field_simp]
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
    ring
  have hl2lo := hL2.1
  have hl2hi := hL2.2
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold logE Mem
  rw [hdecomp]
  push_cast
  constructor
  · rw [add_div, mul_div_assoc, mul_div_assoc]
    have : (e : ℝ) * ((L2.lo : ℝ) / U) ≤ e * Real.log 2 := by gcongr
    linarith [hacc.1]
  · rw [add_div, add_div, mul_div_assoc, mul_div_assoc]
    have h1 : (e : ℝ) * Real.log 2 ≤ e * ((L2.hi : ℝ) / U) := by gcongr
    have h3 : 9 / 4 * z ^ (2 * J + 1) ≤ ((cd ((atGo ((ofFrac (U := U) (q - 2 ^ e) (q + 2 ^ e)).mul
        (ofFrac (U := U) (q - 2 ^ e) (q + 2 ^ e))) 0 (ofFrac (U := U) (q - 2 ^ e) (q + 2 ^ e)) ⟨0, 0⟩ J).1.hi * 9) 4 : ℕ) : ℝ) / U := by
      calc 9 / 4 * z ^ (2 * J + 1)
          ≤ 9 / 4 * ((((atGo ((ofFrac (U := U) (q - 2 ^ e) (q + 2 ^ e)).mul (ofFrac (U := U) (q - 2 ^ e) (q + 2 ^ e))) 0
              (ofFrac (U := U) (q - 2 ^ e) (q + 2 ^ e)) ⟨0, 0⟩ J).1.hi : ℕ) : ℝ) / U) := by gcongr; exact hp.2
        _ = (((((atGo ((ofFrac (U := U) (q - 2 ^ e) (q + 2 ^ e)).mul (ofFrac (U := U) (q - 2 ^ e) (q + 2 ^ e))) 0
              (ofFrac (U := U) (q - 2 ^ e) (q + 2 ^ e)) ⟨0, 0⟩ J).1.hi * 9 : ℕ) : ℝ) / 4) / U) := by push_cast; ring
        _ ≤ _ := div_le_div_of_nonneg_right (cd_real _ (by norm_num)) hU.le
    linarith [hacc.2]

end Iv

/-! ## One Dirichlet term -/

/-- A signed interval: the value is `x` (or `−x` when `neg`), `x ∈ iv`. -/
structure SIv (U : ℕ) where
  neg : Bool
  iv : Iv U
deriving DecidableEq

/-- Membership of a signed interval. -/
def SIv.Mem (a : SIv U) (x : ℝ) : Prop := if a.neg then a.iv.Mem (-x) else a.iv.Mem x

/-- Quadrant reduction of `cos`. -/
theorem cos_quadrant (r : ℕ) (φ : ℝ) :
    Real.cos (r * (Real.pi / 2) + φ) =
      match r % 4 with
      | 0 => Real.cos φ
      | 1 => -Real.sin φ
      | 2 => -Real.cos φ
      | _ => Real.sin φ := by
  have hr : (r : ℝ) * (Real.pi / 2) + φ = ((r % 4 : ℕ) : ℝ) * (Real.pi / 2) + φ + (r / 4 : ℕ) * (2 * Real.pi) := by
    have := Nat.div_add_mod r 4
    have hc : (r : ℝ) = 4 * (r / 4 : ℕ) + (r % 4 : ℕ) := by exact_mod_cast this.symm
    rw [hc]; ring
  rw [hr, Real.cos_add_nat_mul_two_pi]
  have hm : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
  rcases hm with h | h | h | h <;> simp only [h] <;> push_cast
  · simp
  · rw [one_mul, add_comm, Real.cos_add_pi_div_two]
  · rw [show (2 : ℝ) * (Real.pi / 2) + φ = φ + Real.pi by ring, Real.cos_add_pi]
  · rw [show (3 : ℝ) * (Real.pi / 2) + φ = φ + Real.pi / 2 + Real.pi by ring, Real.cos_add_pi,
      Real.cos_add_pi_div_two, neg_neg]

/-- Quadrant reduction of `sin`. -/
theorem sin_quadrant (r : ℕ) (φ : ℝ) :
    Real.sin (r * (Real.pi / 2) + φ) =
      match r % 4 with
      | 0 => Real.sin φ
      | 1 => Real.cos φ
      | 2 => -Real.sin φ
      | _ => -Real.cos φ := by
  have hr : (r : ℝ) * (Real.pi / 2) + φ = ((r % 4 : ℕ) : ℝ) * (Real.pi / 2) + φ + (r / 4 : ℕ) * (2 * Real.pi) := by
    have := Nat.div_add_mod r 4
    have hc : (r : ℝ) = 4 * (r / 4 : ℕ) + (r % 4 : ℕ) := by exact_mod_cast this.symm
    rw [hc]; ring
  rw [hr, Real.sin_add_nat_mul_two_pi]
  have hm : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
  rcases hm with h | h | h | h <;> simp only [h] <;> push_cast
  · simp
  · rw [one_mul, add_comm, Real.sin_add_pi_div_two]
  · rw [show (2 : ℝ) * (Real.pi / 2) + φ = φ + Real.pi by ring, Real.sin_add_pi]
  · rw [show (3 : ℝ) * (Real.pi / 2) + φ = φ + Real.pi / 2 + Real.pi by ring, Real.sin_add_pi,
      Real.sin_add_pi_div_two]

/-- `cos` and `sin` of a reduced angle `φ ∈ [0, π/2)`: directly when `φ ≤ 1`,
else through the complement `π/2 − φ`. -/
def quadCS (P2 φ : Iv U) (nC : ℕ) : Option (Iv U × Iv U) :=
  if φ.hi ≤ U then some (φ.cisE nC)
  else if φ.hi ≤ P2.lo ∧ P2.hi - φ.lo ≤ U then
    let c := (⟨P2.lo - φ.hi, P2.hi - φ.lo⟩ : Iv U).cisE nC
    some (c.2, c.1)
  else none

/-- The quadrant signs: `e^{−iθ}` for `θ = r·π/2 + φ`, scaled by `mag`. -/
def assemble (r : ℕ) (mag c s L : Iv U) : SIv U × SIv U × Iv U :=
  match r % 4 with
  | 0 => (⟨false, mag.mul c⟩, ⟨true, mag.mul s⟩, L)
  | 1 => (⟨true, mag.mul s⟩, ⟨true, mag.mul c⟩, L)
  | 2 => (⟨true, mag.mul c⟩, ⟨false, mag.mul s⟩, L)
  | _ => (⟨false, mag.mul s⟩, ⟨false, mag.mul c⟩, L)

/-- **The Dirichlet term at a grid point** `z₀ = (2 − D₀/U) + i·T₀/U`: enclosures of
`Re`, `Im` of `q^{−z₀}` and of `log q` — or `none` if a side condition fails. -/
def termE (L2 P2 : Iv U) (D0 T0 q J nE nC : ℕ) : Option (SIv U × SIv U × Iv U) :=
  let L := Iv.logE L2 q J
  let x := (Iv.pt D0).mul L
  if U < x.hi then none else
  let mag := (x.expE nE).divN (q * q)
  let th := (Iv.pt T0).mul L
  let r := th.lo / P2.hi
  match quadCS P2 ⟨th.lo - r * P2.hi, th.hi - r * P2.lo⟩ nC with
  | none => none
  | some (c, s) => some (assemble r mag c s L)

theorem mem_pt_mul {a : Iv U} {x : ℝ} (ha : a.Mem x) (n : ℕ) :
    ((Iv.pt n).mul a).Mem ((n : ℝ) / U * x) := Iv.mem_mul (Iv.mem_pt n) ha

theorem le_one_of_mem {a : Iv U} {x : ℝ} (ha : a.Mem x) (h : a.hi ≤ U) : x ≤ 1 := by
  have := ha.2
  have hU := U_real_pos (U := U)
  calc x ≤ (a.hi : ℝ) / U := this
    _ ≤ 1 := by rw [div_le_one hU]; exact_mod_cast h

theorem lo_le_hi {a : Iv U} {x : ℝ} (ha : a.Mem x) : a.lo ≤ a.hi := by
  have h := ha.1.trans ha.2
  rw [div_le_div_iff_of_pos_right (U_real_pos (U := U))] at h
  exact_mod_cast h

theorem mem_quadCS {P2 φ : Iv U} {φr : ℝ} (hP2 : P2.Mem (Real.pi / 2)) (hφ : φ.Mem φr) {nC : ℕ}
    (hnC : 0 < nC) {c s : Iv U} (h : quadCS P2 φ nC = some (c, s)) :
    c.Mem (Real.cos φr) ∧ s.Mem (Real.sin φr) := by
  unfold quadCS at h
  by_cases hb1 : φ.hi ≤ U
  · rw [ite_eq_left hb1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact Iv.mem_cisE hφ (le_one_of_mem hφ hb1) hnC
  · rw [ite_eq_right hb1] at h
    by_cases hb2 : φ.hi ≤ P2.lo ∧ P2.hi - φ.lo ≤ U
    · rw [ite_eq_left hb2] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hφle := lo_le_hi hφ
      have hP2le := lo_le_hi hP2
      have hψ : (⟨P2.lo - φ.hi, P2.hi - φ.lo⟩ : Iv U).Mem (Real.pi / 2 - φr) := by
        constructor
        · show ((P2.lo - φ.hi : ℕ) : ℝ) / U ≤ Real.pi / 2 - φr
          rw [Nat.cast_sub hb2.1, sub_div]
          linarith [hP2.1, hφ.2]
        · show Real.pi / 2 - φr ≤ ((P2.hi - φ.lo : ℕ) : ℝ) / U
          rw [Nat.cast_sub (le_trans hφle (hb2.1.trans hP2le)), sub_div]
          linarith [hP2.2, hφ.1]
      obtain ⟨hc, hs⟩ := Iv.mem_cisE hψ (le_one_of_mem hψ hb2.2) hnC
      rw [Real.cos_pi_div_two_sub] at hc
      rw [Real.sin_pi_div_two_sub] at hs
      exact ⟨hs, hc⟩
    · rw [ite_eq_right hb2] at h
      exact absurd h (by simp)

theorem mem_assemble {r : ℕ} {mag c s L : Iv U} {m φr l : ℝ} (hmag : mag.Mem m)
    (hc : c.Mem (Real.cos φr)) (hs : s.Mem (Real.sin φr)) (hL : L.Mem l) :
    (assemble r mag c s L).1.Mem (m * Real.cos (r * (Real.pi / 2) + φr)) ∧
    (assemble r mag c s L).2.1.Mem (-(m * Real.sin (r * (Real.pi / 2) + φr))) ∧
    (assemble r mag c s L).2.2.Mem l := by
  have hmc := Iv.mem_mul hmag hc
  have hms := Iv.mem_mul hmag hs
  rw [cos_quadrant, sin_quadrant]
  have hm : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
  unfold assemble
  rcases hm with h4 | h4 | h4 | h4 <;> simp only [h4] <;> refine ⟨?_, ?_, hL⟩ <;>
    simp only [SIv.Mem, ite_true, ite_false, Bool.false_eq_true, mul_neg, neg_neg] <;> assumption

/-- **Soundness of one Dirichlet term**. -/
theorem mem_termE {L2 P2 : Iv U} (hL2 : L2.Mem (Real.log 2)) (hP2 : P2.Mem (Real.pi / 2))
    {D0 T0 q J nE nC : ℕ} (hq : 0 < q) (hnE : 0 < nE) (hnC : 0 < nC) {re im : SIv U} {L : Iv U}
    (h : termE L2 P2 D0 T0 q J nE nC = some (re, im, L)) :
    re.Mem ((q : ℝ) ^ (-(2 - (D0 : ℝ) / U)) * Real.cos ((T0 : ℝ) / U * Real.log q)) ∧
    im.Mem (-((q : ℝ) ^ (-(2 - (D0 : ℝ) / U)) * Real.sin ((T0 : ℝ) / U * Real.log q))) ∧
    L.Mem (Real.log q) := by
  have hU := U_real_pos (U := U)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hL := Iv.mem_logE hL2 hq J
  have hx := mem_pt_mul hL D0
  unfold termE at h
  by_cases hbig : U < ((Iv.pt D0).mul (Iv.logE L2 q J)).hi
  · rw [ite_eq_left hbig] at h; exact absurd h (by simp)
  rw [ite_eq_right hbig] at h
  dsimp only at h
  have hx1 := le_one_of_mem hx (not_lt.mp hbig)
  have hmag := Iv.mem_divN (Iv.mem_expE hx hx1 hnE) (Nat.mul_pos hq hq)
  have hmag_eq : Real.exp ((D0 : ℝ) / U * Real.log q) / ((q * q : ℕ) : ℝ) =
      (q : ℝ) ^ (-(2 - (D0 : ℝ) / U)) := by
    rw [Real.rpow_def_of_pos hqR]
    push_cast
    rw [show Real.log q * -(2 - (D0 : ℝ) / U) = (D0 : ℝ) / U * Real.log q - 2 * Real.log q by ring,
      Real.exp_sub, show 2 * Real.log q = Real.log q + Real.log q by ring, Real.exp_add,
      Real.exp_log hqR]
  rw [hmag_eq] at hmag
  have hth := mem_pt_mul hL T0
  set th := (Iv.pt T0).mul (Iv.logE L2 q J) with hthv
  set r := th.lo / P2.hi with hr
  set φr := (T0 : ℝ) / U * Real.log q - r * (Real.pi / 2) with hφr
  have hrle : r * P2.hi ≤ th.lo := Nat.div_mul_le_self _ _
  have hP2le := lo_le_hi hP2
  have hthle := lo_le_hi hth
  have hrle2 : r * P2.lo ≤ th.hi := le_trans (Nat.mul_le_mul_left r hP2le) (hrle.trans hthle)
  have hφ : (⟨th.lo - r * P2.hi, th.hi - r * P2.lo⟩ : Iv U).Mem φr := by
    constructor
    · show ((th.lo - r * P2.hi : ℕ) : ℝ) / U ≤ φr
      rw [Nat.cast_sub hrle, sub_div, hφr]
      push_cast
      have h1 := hth.1
      have h2 : (r : ℝ) * (Real.pi / 2) ≤ r * ((P2.hi : ℝ) / U) :=
        mul_le_mul_of_nonneg_left hP2.2 (Nat.cast_nonneg r)
      rw [mul_div_assoc]
      linarith
    · show φr ≤ ((th.hi - r * P2.lo : ℕ) : ℝ) / U
      rw [Nat.cast_sub hrle2, sub_div, hφr]
      push_cast
      have h1 := hth.2
      have h2 : (r : ℝ) * ((P2.lo : ℝ) / U) ≤ r * (Real.pi / 2) :=
        mul_le_mul_of_nonneg_left hP2.1 (Nat.cast_nonneg r)
      rw [mul_div_assoc]
      linarith
  have htl : (T0 : ℝ) / U * Real.log q = r * (Real.pi / 2) + φr := by rw [hφr]; ring
  rw [htl]
  cases hcs : quadCS P2 ⟨th.lo - r * P2.hi, th.hi - r * P2.lo⟩ nC with
  | none => rw [hcs] at h; exact absurd h (by simp)
  | some cs =>
    obtain ⟨c, s⟩ := cs
    rw [hcs] at h
    obtain ⟨hc, hs⟩ := mem_quadCS hP2 hφ hnC hcs
    have := mem_assemble (r := r) hmag hc hs hL
    rw [Option.some.inj h] at this
    exact this

/-! ## Accumulation over the lattice box -/

/-- Engine parameters: the constants and series lengths. -/
structure Params (U : ℕ) where
  L2 : Iv U
  P2 : Iv U
  D0 : ℕ
  T0 : ℕ
  Dm : ℕ
  J : ℕ
  nE : ℕ
  nC : ℕ

/-- Running enclosures: positive and negative parts of `Re`, `Im` of `∑ q^{−z₀}` and
of `∑ −log q·q^{−z₀}`, and an upper bound for `∑ (log q)²·q^{−σm}`. -/
structure Acc (U : ℕ) where
  ok : Bool
  rp : Iv U
  rn : Iv U
  ip : Iv U
  inn : Iv U
  drp : Iv U
  drn : Iv U
  dip : Iv U
  dinn : Iv U
  b2 : ℕ
deriving DecidableEq

def Acc.zero : Acc U := ⟨true, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, 0⟩

/-- Add a signed value into a (positive, negative) pair. -/
def sadd (p n : Iv U) (a : SIv U) : Iv U × Iv U := if a.neg then (p, n.add a.iv) else (p.add a.iv, n)

/-- `−L·v` for a signed `v`. -/
def dS (L : Iv U) (a : SIv U) : SIv U := ⟨!a.neg, L.mul a.iv⟩

/-- The step for a successful term: a range check on the second exponential, then the
signed additions. -/
def Acc.stepSome (P : Params U) (a : Acc U) (q : ℕ) (re im : SIv U) (L : Iv U) : Acc U :=
  if U < ((Iv.pt P.Dm).mul L).hi then { a with ok := false } else
    let m2 := (((Iv.pt P.Dm).mul L).expE P.nE).divN (q * q)
    let r := sadd a.rp a.rn re
    let i := sadd a.ip a.inn im
    let dr := sadd a.drp a.drn (dS L re)
    let di := sadd a.dip a.dinn (dS L im)
    ⟨a.ok, r.1, r.2, i.1, i.2, dr.1, dr.2, di.1, di.2, a.b2 + ((L.mul L).mul m2).hi⟩

def Acc.step (P : Params U) (a : Acc U) (q : ℕ) : Acc U :=
  match termE P.L2 P.P2 P.D0 P.T0 q P.J P.nE P.nC with
  | none => { a with ok := false }
  | some (re, im, L) => a.stepSome P q re im L

omit [Fact (0 < U)] in
theorem Acc.step_of_none {P : Params U} {a : Acc U} {q : ℕ}
    (h : termE P.L2 P.P2 P.D0 P.T0 q P.J P.nE P.nC = none) :
    a.step P q = { a with ok := false } := by
  simp only [Acc.step, h]

omit [Fact (0 < U)] in
theorem Acc.step_of_some {P : Params U} {a : Acc U} {q : ℕ} {re im : SIv U} {L : Iv U}
    (h : termE P.L2 P.P2 P.D0 P.T0 q P.J P.nE P.nC = some (re, im, L)) :
    a.step P q = a.stepSome P q re im L := by
  simp only [Acc.step, h]

/-- A real number is a difference of members of a (positive, negative) pair. -/
def PairMem (p n : Iv U) (x : ℝ) : Prop := ∃ P N, p.Mem P ∧ n.Mem N ∧ x = P - N

/-- The invariant: the five running sums are enclosed. -/
def Acc.Holds (a : Acc U) (v : ℝ × ℝ × ℝ × ℝ × ℝ) : Prop :=
  a.ok = true → PairMem a.rp a.rn v.1 ∧ PairMem a.ip a.inn v.2.1 ∧
    PairMem a.drp a.drn v.2.2.1 ∧ PairMem a.dip a.dinn v.2.2.2.1 ∧ v.2.2.2.2 ≤ (a.b2 : ℝ) / U

omit [Fact (0 < U)] in
theorem Acc.holds_zero : (Acc.zero (U := U)).Holds 0 := by
  intro _
  have hz : PairMem (U := U) ⟨0, 0⟩ ⟨0, 0⟩ 0 := ⟨0, 0, by simp [Iv.Mem], by simp [Iv.Mem], by ring⟩
  exact ⟨hz, hz, hz, hz, by simp [Acc.zero]⟩

omit [Fact (0 < U)] in
theorem pairMem_sadd {p n : Iv U} {x : ℝ} (h : PairMem p n x) {a : SIv U} {y : ℝ} (ha : a.Mem y) :
    PairMem (sadd p n a).1 (sadd p n a).2 (x + y) := by
  obtain ⟨P, N, hP, hN, rfl⟩ := h
  unfold sadd
  unfold SIv.Mem at ha
  split_ifs at ha ⊢ with hneg
  · exact ⟨P, N + -y, hP, Iv.mem_add hN ha, by ring⟩
  · exact ⟨P + y, N, Iv.mem_add hP ha, hN, by ring⟩

theorem mem_dS {L : Iv U} {l : ℝ} (hL : L.Mem l) {a : SIv U} {y : ℝ} (ha : a.Mem y) :
    (dS L a).Mem (-(l * y)) := by
  unfold dS SIv.Mem at *
  cases hneg : a.neg <;> simp only [hneg, Bool.not_false, Bool.not_true, ite_true, ite_false,
    Bool.false_eq_true] at ha ⊢
  · simpa [neg_neg] using Iv.mem_mul hL ha
  · simpa [mul_neg] using Iv.mem_mul hL ha

/-- The real value of one term: `(Re, Im)` of `q^{−z₀}`, of `−log q·q^{−z₀}`, and
`(log q)²·q^{−σm}`. -/
noncomputable def termVal (P : Params U) (q : ℕ) : ℝ × ℝ × ℝ × ℝ × ℝ :=
  let σ := 2 - (P.D0 : ℝ) / U
  let t := (P.T0 : ℝ) / U
  let re := (q : ℝ) ^ (-σ) * Real.cos (t * Real.log q)
  let im := -((q : ℝ) ^ (-σ) * Real.sin (t * Real.log q))
  (re, im, -(Real.log q * re), -(Real.log q * im),
    Real.log q ^ 2 * (q : ℝ) ^ (-(2 - (P.Dm : ℝ) / U)))

theorem Acc.holds_step {P : Params U} (hL2 : P.L2.Mem (Real.log 2)) (hP2 : P.P2.Mem (Real.pi / 2))
    (hnE : 0 < P.nE) (hnC : 0 < P.nC) {a : Acc U} {v : ℝ × ℝ × ℝ × ℝ × ℝ} (ha : a.Holds v)
    {q : ℕ} (hq : 0 < q) : (a.step P q).Holds (v + termVal P q) := by
  cases ht : termE P.L2 P.P2 P.D0 P.T0 q P.J P.nE P.nC with
  | none =>
    rw [Acc.step_of_none ht]
    intro h
    exact absurd h (by simp)
  | some t =>
    obtain ⟨re, im, L⟩ := t
    rw [Acc.step_of_some ht]
    unfold Acc.stepSome
    by_cases hbig : U < ((Iv.pt P.Dm).mul L).hi
    · rw [ite_eq_left hbig]; intro h; exact absurd h (by simp)
    rw [ite_eq_right hbig]
    intro hok
    obtain ⟨hre, him, hL⟩ := mem_termE hL2 hP2 hq hnE hnC ht
    obtain ⟨h1, h2, h3, h4, h5⟩ := ha hok
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hx2 := mem_pt_mul hL P.Dm
    have hm2 := Iv.mem_divN (Iv.mem_expE hx2 (le_one_of_mem hx2 (not_lt.mp hbig)) hnE)
      (Nat.mul_pos hq hq)
    have hm2eq : Real.exp ((P.Dm : ℝ) / U * Real.log q) / ((q * q : ℕ) : ℝ) =
        (q : ℝ) ^ (-(2 - (P.Dm : ℝ) / U)) := by
      rw [Real.rpow_def_of_pos hqR]
      push_cast
      rw [show Real.log q * -(2 - (P.Dm : ℝ) / U) = (P.Dm : ℝ) / U * Real.log q - 2 * Real.log q by ring,
        Real.exp_sub, show 2 * Real.log q = Real.log q + Real.log q by ring, Real.exp_add,
        Real.exp_log hqR]
    rw [hm2eq] at hm2
    have hb := Iv.mem_mul (Iv.mem_mul hL hL) hm2
    refine ⟨pairMem_sadd h1 hre, pairMem_sadd h2 him, pairMem_sadd h3 (mem_dS hL hre),
      pairMem_sadd h4 (mem_dS hL him), ?_⟩
    have hv : (v + termVal P q).2.2.2.2 =
        v.2.2.2.2 + Real.log q ^ 2 * (q : ℝ) ^ (-(2 - (P.Dm : ℝ) / U)) := rfl
    rw [hv]
    have hcast : (((a.b2 + ((L.mul L).mul ((((Iv.pt P.Dm).mul L).expE P.nE).divN (q * q))).hi : ℕ) : ℝ) / U)
        = (a.b2 : ℝ) / U + (((L.mul L).mul ((((Iv.pt P.Dm).mul L).expE P.nE).divN (q * q))).hi : ℝ) / U := by
      push_cast; rw [add_div]
    refine le_trans ?_ (le_of_eq hcast.symm)
    rw [sq]
    linarith [hb.2]

omit [Fact (0 < U)] in
/-- **Generic fold soundness**: a step that carries `Holds v` to `Holds (v + w n)`
carries it through any fold over `range n`. -/
theorem holds_foldl_gen (f : Acc U → ℕ → Acc U) (w : ℕ → ℝ × ℝ × ℝ × ℝ × ℝ)
    (hf : ∀ a v n, a.Holds v → (f a n).Holds (v + w n)) :
    ∀ (n : ℕ) (a : Acc U) (v : ℝ × ℝ × ℝ × ℝ × ℝ), a.Holds v →
      ((List.range n).foldl f a).Holds (v + ∑ k ∈ Finset.range n, w k) := by
  intro n
  induction n with
  | zero => intro a v ha; simpa using ha
  | succ n ih =>
    intro a v ha
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← add_assoc]
    simp only [List.foldl_cons, List.foldl_nil]
    exact hf _ _ n (ih a v ha)

/-- The engine's sweep of the box `[−B, B]²`, keeping the points with `0 < Q ≤ N`. -/
def boxAcc (P : Params U) (Q : ℤ → ℤ → ℕ) (B N : ℕ) : Acc U :=
  (List.range (2 * B + 1)).foldl (fun (a : Acc U) (i : ℕ) =>
    (List.range (2 * B + 1)).foldl (fun (a : Acc U) (j : ℕ) =>
      let q := Q ((i : ℤ) - B) ((j : ℤ) - B)
      if q != 0 && q ≤ N then a.step P q else a) a) Acc.zero

/-- **Box soundness**: the sweep encloses the five real sums over the box. -/
theorem boxAcc_holds {P : Params U} (hL2 : P.L2.Mem (Real.log 2)) (hP2 : P.P2.Mem (Real.pi / 2))
    (hnE : 0 < P.nE) (hnC : 0 < P.nC) (Q : ℤ → ℤ → ℕ) (B N : ℕ) :
    (boxAcc P Q B N).Holds (∑ i ∈ Finset.range (2 * B + 1), ∑ j ∈ Finset.range (2 * B + 1),
      if (Q ((i : ℤ) - B) ((j : ℤ) - B) != 0 && Q ((i : ℤ) - B) ((j : ℤ) - B) ≤ N) = true then
        termVal P (Q ((i : ℤ) - B) ((j : ℤ) - B)) else 0) := by
  have inner : ∀ (i : ℕ) (a : Acc U) (v : ℝ × ℝ × ℝ × ℝ × ℝ), a.Holds v →
      ((List.range (2 * B + 1)).foldl (fun (a : Acc U) (j : ℕ) =>
        let q := Q ((i : ℤ) - B) ((j : ℤ) - B)
        if q != 0 && q ≤ N then a.step P q else a) a).Holds
        (v + ∑ j ∈ Finset.range (2 * B + 1),
          if (Q ((i : ℤ) - B) ((j : ℤ) - B) != 0 && Q ((i : ℤ) - B) ((j : ℤ) - B) ≤ N) = true then
            termVal P (Q ((i : ℤ) - B) ((j : ℤ) - B)) else 0) := by
    intro i
    refine holds_foldl_gen _ _ (fun a v j ha => ?_) (2 * B + 1)
    dsimp only
    split_ifs with hc
    · have hq : 0 < Q ((i : ℤ) - B) ((j : ℤ) - B) := by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
        exact Nat.pos_of_ne_zero hc.1
      exact Acc.holds_step hL2 hP2 hnE hnC ha hq
    · simpa using ha
  have := holds_foldl_gen _ _ (fun a v i ha => inner i a v ha) (2 * B + 1) Acc.zero 0 Acc.holds_zero
  rw [zero_add] at this
  exact this

end Engine

end Meno
