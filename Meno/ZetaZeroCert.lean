import Meno.ZetaZeroSweep
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The certificate bridge

The engine's sweep of the square encloses the finite part of `Z`, `Z'` and the
second-derivative majorant at a rational centre; the shell tails bound the rest; the
Newton criterion turns the numbers into a zero. -/

namespace Meno

namespace Engine

open Epstein Finset Metric

variable {U : ℕ} [Fact (0 < U)]

omit [Fact (0 < U)] in
/-- An integer interval as a shifted range. -/
theorem sum_Icc_int {M : Type*} [AddCommMonoid M] (φ : ℤ → M) (B : ℕ) :
    ∑ x ∈ Icc (-(B : ℤ)) B, φ x = ∑ i ∈ range (2 * B + 1), φ ((i : ℤ) - B) := by
  refine Finset.sum_nbij' (fun x => (x + B).toNat) (fun i => (i : ℤ) - B) ?_ ?_ ?_ ?_ ?_
  · intro x hx; simp only [mem_Icc, mem_range] at hx ⊢; omega
  · intro i hi; simp only [mem_Icc, mem_range] at hi ⊢; omega
  · intro x hx; simp only [mem_Icc] at hx; omega
  · intro i hi; simp
  · intro x hx
    simp only [mem_Icc] at hx
    congr 1
    omega

omit [Fact (0 < U)] in
/-- The square `[−B, B]²` as the engine's double sweep. -/
theorem sum_Icc_prod {M : Type*} [AddCommMonoid M] (g : ℤ × ℤ → M) (B : ℕ) :
    ∑ k ∈ Icc (-(B : ℤ × ℤ)) B, g k =
      ∑ i ∈ range (2 * B + 1), ∑ j ∈ range (2 * B + 1), g ((i : ℤ) - B, (j : ℤ) - B) := by
  rw [Finset.Icc_prod_def, Finset.sum_product]
  simp only [Prod.fst_neg, Prod.snd_neg, Prod.fst_natCast, Prod.snd_natCast]
  rw [sum_Icc_int]
  exact Finset.sum_congr rfl fun i _ => sum_Icc_int _ B

/-- `(Re, Im)` of `q^{−(σ + it)}`. -/
theorem cpow_neg_re_im {q : ℕ} (hq : 0 < q) (σ t : ℝ) :
    ((q : ℂ) ^ (-(⟨σ, t⟩ : ℂ))).re = (q : ℝ) ^ (-σ) * Real.cos (t * Real.log q) ∧
    ((q : ℂ) ^ (-(⟨σ, t⟩ : ℂ))).im = -((q : ℝ) ^ (-σ) * Real.sin (t * Real.log q)) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Complex.cpow_def_of_ne_zero hq0, ← Complex.natCast_log, Complex.exp_re, Complex.exp_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, zero_mul, sub_zero, add_zero]
  rw [Real.rpow_def_of_pos hqR, show Real.log q * -t = -(t * Real.log q) by ring,
    Real.cos_neg, Real.sin_neg, show Real.log q * -σ = Real.log q * -σ from rfl]
  exact ⟨rfl, by ring⟩

/-- The engine's five components at a lattice point inside the cutoff. -/
noncomputable def boxTerm (P : Params U) (F : BinForm) (N : ℕ) (k : ℤ × ℤ) :
    ℝ × ℝ × ℝ × ℝ × ℝ :=
  if (F.q k != 0 && F.q k ≤ N) = true then termVal P (F.q k) else 0

/-- The engine's centre `2 − D0/U + i·T0/U`. -/
noncomputable def centre (P : Params U) : ℂ := ⟨2 - (P.D0 : ℝ) / U, (P.T0 : ℝ) / U⟩

omit [Fact (0 < U)] in
theorem boxTerm_eq (P : Params U) (F : BinForm) (N : ℕ) (k : ℤ × ℤ) :
    (if F.q k ≤ N then term F (centre P) k else 0).re = (boxTerm P F N k).1 ∧
    (if F.q k ≤ N then term F (centre P) k else 0).im = (boxTerm P F N k).2.1 ∧
    (if F.q k ≤ N then dterm F (centre P) k else 0).re = (boxTerm P F N k).2.2.1 ∧
    (if F.q k ≤ N then dterm F (centre P) k else 0).im = (boxTerm P F N k).2.2.2.1 ∧
    (if F.q k ≤ N then lmaj F 2 (2 - (P.Dm : ℝ) / U) k else 0) = (boxTerm P F N k).2.2.2.2 := by
  unfold boxTerm
  by_cases h0 : F.q k = 0
  · simp [h0, term, dterm, lmaj]
  by_cases hN : F.q k ≤ N
  · have hc : (F.q k != 0 && F.q k ≤ N) = true := by simp [h0, hN]
    obtain ⟨hre, him⟩ := cpow_neg_re_im (Nat.pos_of_ne_zero h0) (2 - (P.D0 : ℝ) / U)
      ((P.T0 : ℝ) / U)
    simp only [ite_eq_left hN, ite_eq_left hc, term, dterm, lmaj, ite_eq_right h0, termVal, centre]
    refine ⟨hre, him, ?_, ?_, trivial⟩
    · rw [neg_mul, Complex.neg_re, Complex.re_ofReal_mul, hre]
    · rw [neg_mul, Complex.neg_im, Complex.im_ofReal_mul, him]
  · simp [hN]

/-- `|x − c|` for `x` enclosed by a (positive, negative) pair. -/
noncomputable def pdev (p n : Iv U) (c : ℝ) : ℝ :=
  max |((p.lo : ℝ) - n.hi) / U - c| |((p.hi : ℝ) - n.lo) / U - c|

omit [Fact (0 < U)] in
theorem PairMem.abs_sub_le {p n : Iv U} {x : ℝ} (h : PairMem p n x) (c : ℝ) :
    |x - c| ≤ pdev p n c := by
  obtain ⟨P, N, ⟨hP1, hP2⟩, ⟨hN1, hN2⟩, rfl⟩ := h
  unfold pdev
  rw [sub_div, sub_div]
  refine abs_le.mpr ⟨?_, ?_⟩
  · have := neg_abs_le ((p.lo : ℝ) / U - (n.hi : ℝ) / U - c)
    linarith [le_max_left |(p.lo : ℝ) / U - (n.hi : ℝ) / U - c|
      |(p.hi : ℝ) / U - (n.lo : ℝ) / U - c|]
  · have := le_abs_self ((p.hi : ℝ) / U - (n.lo : ℝ) / U - c)
    linarith [le_max_right |(p.lo : ℝ) / U - (n.hi : ℝ) / U - c|
      |(p.hi : ℝ) / U - (n.lo : ℝ) / U - c|]

omit [Fact (0 < U)] in
theorem pdev_le {p n : Iv U} {c b : ℝ}
    (h1 : -b ≤ ((p.lo : ℝ) - n.hi) / U - c) (h2 : ((p.lo : ℝ) - n.hi) / U - c ≤ b)
    (h3 : -b ≤ ((p.hi : ℝ) - n.lo) / U - c) (h4 : ((p.hi : ℝ) - n.lo) / U - c ≤ b) :
    pdev p n c ≤ b :=
  max_le (abs_le.mpr ⟨h1, h2⟩) (abs_le.mpr ⟨h3, h4⟩)

/-- **THE CERTIFICATE BRIDGE**: an engine sweep that stays `ok`, three tail bounds and
two scalar inequalities place a zero of `Z` within `(Dm − D0)/U` of the engine's
centre. -/
theorem exists_zero_of_acc {F : BinForm} {lN lD hi : ℕ} (hF : Coercive F lN lD hi)
    {P : Params U} (hL2 : P.L2.Mem (Real.log 2)) (hP2 : P.P2.Mem (Real.pi / 2))
    (hnE : 0 < P.nE) (hnC : 0 < P.nC) {B N : ℕ} (hB : lD * N < lN * (B + 1) ^ 2)
    (hDm : P.D0 < P.Dm) (hσ : 1 < 2 - (P.Dm : ℝ) / U) {T₀ T₁ T₂ : ℝ}
    (hT₀ : ∑' k, (if N < F.q k then lmaj F 0 (2 - (P.D0 : ℝ) / U) k else 0) ≤ T₀)
    (hT₁ : ∑' k, (if N < F.q k then lmaj F 1 (2 - (P.D0 : ℝ) / U) k else 0) ≤ T₁)
    (hT₂ : ∑' k, (if N < F.q k then lmaj F 2 (2 - (P.Dm : ℝ) / U) k else 0) ≤ T₂)
    {c : ℂ} {cn q : ℝ} (hcn : 0 < cn) (hc : cn ≤ ‖c‖) (hq0 : 0 ≤ q) (hq : q < 1)
    (hok : (boxAcc P (fun x y => F.q (x, y)) B N).ok = true)
    (hval : pdev (boxAcc P (fun x y => F.q (x, y)) B N).rp
        (boxAcc P (fun x y => F.q (x, y)) B N).rn 0
      + pdev (boxAcc P (fun x y => F.q (x, y)) B N).ip
        (boxAcc P (fun x y => F.q (x, y)) B N).inn 0 + T₀
      ≤ (1 - q) * (((P.Dm : ℝ) - P.D0) / U) * cn)
    (hder : pdev (boxAcc P (fun x y => F.q (x, y)) B N).drp
        (boxAcc P (fun x y => F.q (x, y)) B N).drn c.re
      + pdev (boxAcc P (fun x y => F.q (x, y)) B N).dip
        (boxAcc P (fun x y => F.q (x, y)) B N).dinn c.im + T₁
      + ((P.Dm : ℝ) - P.D0) / U * (((boxAcc P (fun x y => F.q (x, y)) B N).b2 : ℝ) / U + T₂)
      ≤ q * cn) :
    ∃ z ∈ closedBall (centre P) (((P.Dm : ℝ) - P.D0) / U), Z F z = 0 := by
  set a := boxAcc P (fun x y => F.q (x, y)) B N with ha
  set ρ := ((P.Dm : ℝ) - P.D0) / U with hρdef
  have hU := U_real_pos (U := U)
  have hρ : 0 < ρ := div_pos (by rw [sub_pos]; exact_mod_cast hDm) hU
  have hσ0 : (centre P).re - ρ = 2 - (P.Dm : ℝ) / U := by
    simp only [centre, hρdef]; ring
  have hσ1 : 1 < (centre P).re := by linarith
  -- the engine's enclosures, as sums over the square
  set V := ∑ k ∈ Icc (-(B : ℤ × ℤ)) B, boxTerm P F N k with hV
  have hH : a.Holds V := by
    have := boxAcc_holds hL2 hP2 hnE hnC (fun x y => F.q (x, y)) B N
    rw [hV, sum_Icc_prod]
    exact this
  obtain ⟨h1, h2, h3, h4, h5⟩ := hH hok
  have hcomp := fun k => boxTerm_eq P F N k
  have hSre : (∑ k ∈ Icc (-(B : ℤ × ℤ)) B,
      (if F.q k ≤ N then term F (centre P) k else 0)).re = V.1 := by
    rw [Complex.re_sum, hV, Prod.fst_sum]; exact sum_congr rfl fun k _ => (hcomp k).1
  have hSim : (∑ k ∈ Icc (-(B : ℤ × ℤ)) B,
      (if F.q k ≤ N then term F (centre P) k else 0)).im = V.2.1 := by
    rw [Complex.im_sum, hV, Prod.snd_sum, Prod.fst_sum]
    exact sum_congr rfl fun k _ => (hcomp k).2.1
  have hDre : (∑ k ∈ Icc (-(B : ℤ × ℤ)) B,
      (if F.q k ≤ N then dterm F (centre P) k else 0)).re = V.2.2.1 := by
    rw [Complex.re_sum, hV, Prod.snd_sum, Prod.snd_sum, Prod.fst_sum]
    exact sum_congr rfl fun k _ => (hcomp k).2.2.1
  have hDim : (∑ k ∈ Icc (-(B : ℤ × ℤ)) B,
      (if F.q k ≤ N then dterm F (centre P) k else 0)).im = V.2.2.2.1 := by
    rw [Complex.im_sum, hV, Prod.snd_sum, Prod.snd_sum, Prod.snd_sum, Prod.fst_sum]
    exact sum_congr rfl fun k _ => (hcomp k).2.2.2.1
  have hL : ∑ k ∈ Icc (-(B : ℤ × ℤ)) B,
      (if F.q k ≤ N then lmaj F 2 (2 - (P.Dm : ℝ) / U) k else 0) = V.2.2.2.2 := by
    rw [hV, Prod.snd_sum, Prod.snd_sum, Prod.snd_sum, Prod.snd_sum]
    exact sum_congr rfl fun k _ => (hcomp k).2.2.2.2
  -- the three splits
  have hZ := hF.tsum_split hB (f := fun k => term F (centre P) k)
    (fun k => (norm_term _ k).le) (hF.summable_maj hσ1)
  have hZd := hF.tsum_split hB (f := fun k => dterm F (centre P) k)
    (fun k => (norm_dterm _ k).le) (hF.summable_lmaj 1 hσ1)
  have hσm : 1 < 2 - (P.Dm : ℝ) / U := hσ
  have hZ2 := hF.tsum_split hB (f := fun k => lmaj F 2 (2 - (P.Dm : ℝ) / U) k)
    (fun k => by rw [Real.norm_of_nonneg (lmaj_nonneg 2 _ k)]) (hF.summable_lmaj 2 hσm)
  have ht0 := norm_tsum_ite_le (F := F) (fun k => (norm_term (centre P) k).le)
    (hF.summable_maj hσ1) (maj_nonneg _) N
  have ht1 := norm_tsum_ite_le (F := F) (fun k => (norm_dterm (centre P) k).le)
    (hF.summable_lmaj 1 hσ1) (lmaj_nonneg 1 _) N
  have hre : (centre P).re = 2 - (P.D0 : ℝ) / U := rfl
  simp only [← lmaj_zero, hre] at ht0
  rw [hre] at ht1
  have hcn' : ‖c‖ ≠ 0 := (hcn.trans_le hc).ne'
  refine hF.exists_zero hρ hq (norm_ne_zero_iff.mp hcn') (by rw [hσ0]; exact hσ)
    (B₂ := (a.b2 : ℝ) / U + T₂) ?_ ?_ ?_
  · rw [hσ0, hZ2, hL]
    have : ∑' k, (if N < F.q k then lmaj F 2 (2 - (P.Dm : ℝ) / U) k else 0) ≤ T₂ := hT₂
    linarith
  · rw [Z, hZ]
    refine (norm_add_le _ _).trans ?_
    have hS := Complex.norm_le_abs_re_add_abs_im (∑ k ∈ Icc (-(B : ℤ × ℤ)) B,
      (if F.q k ≤ N then term F (centre P) k else 0))
    rw [hSre, hSim] at hS
    have e1 := h1.abs_sub_le 0
    have e2 := h2.abs_sub_le 0
    rw [sub_zero] at e1 e2
    have hm : (1 - q) * ρ * cn ≤ (1 - q) * ρ * ‖c‖ :=
      mul_le_mul_of_nonneg_left hc (mul_nonneg (by linarith) hρ.le)
    linarith
  · rw [Zd, hZd]
    have hS := Complex.norm_le_abs_re_add_abs_im ((∑ k ∈ Icc (-(B : ℤ × ℤ)) B,
      (if F.q k ≤ N then dterm F (centre P) k else 0)) - c)
    rw [Complex.sub_re, Complex.sub_im, hDre, hDim] at hS
    have e3 := h3.abs_sub_le c.re
    have e4 := h4.abs_sub_le c.im
    have hn := norm_add_le ((∑ k ∈ Icc (-(B : ℤ × ℤ)) B,
      (if F.q k ≤ N then dterm F (centre P) k else 0)) - c)
      (∑' k, (if N < F.q k then dterm F (centre P) k else 0))
    rw [show (∑ k ∈ Icc (-(B : ℤ × ℤ)) B, (if F.q k ≤ N then dterm F (centre P) k else 0)) - c
      + ∑' k, (if N < F.q k then dterm F (centre P) k else 0)
      = (∑ k ∈ Icc (-(B : ℤ × ℤ)) B, (if F.q k ≤ N then dterm F (centre P) k else 0)
      + ∑' k, (if N < F.q k then dterm F (centre P) k else 0)) - c by ring] at hn
    have hm : q * cn ≤ q * ‖c‖ := mul_le_mul_of_nonneg_left hc hq0
    have hb2 : ρ * V.2.2.2.2 ≤ ρ * ((a.b2 : ℝ) / U) := mul_le_mul_of_nonneg_left h5 hρ.le
    nlinarith

end Engine

/-! ## The Davenport–Heilbronn zero -/

namespace DH

open Engine Epstein Metric

theorem val_eq (k : ℤ × ℤ) : F.val k = 3 * k.1 ^ 2 - 2 * k.1 * k.2 + 2 * k.2 ^ 2 := by
  simp only [BinForm.val, F]; ring

theorem q_cast (k : ℤ × ℤ) : (F.q k : ℤ) = 3 * k.1 ^ 2 - 2 * k.1 * k.2 + 2 * k.2 ^ 2 := by
  rw [BinForm.q, Int.toNat_of_nonneg, val_eq]
  rw [val_eq]; nlinarith [sq_nonneg (3 * k.1 - k.2), sq_nonneg k.2]

theorem supNorm_cast (k : ℤ × ℤ) : (supNorm k : ℤ) = max |k.1| |k.2| := by
  simp [supNorm]

/-- `(5/3)·‖k‖² ≤ Q(k) ≤ 7·‖k‖²` in the sup norm. -/
theorem coercive : Coercive F 5 3 7 where
  lN_pos := by norm_num
  lD_pos := by norm_num
  lower k := by
    zify
    rw [q_cast, supNorm_cast]
    rcases le_total |k.1| |k.2| with h | h
    · rw [max_eq_right h, sq_abs]; nlinarith [sq_nonneg (3 * k.1 - k.2)]
    · rw [max_eq_left h, sq_abs]; nlinarith [sq_nonneg (4 * k.1 - 3 * k.2), sq_nonneg k.2]
  upper k := by
    zify
    rw [q_cast, supNorm_cast]
    have h1 : k.1 ^ 2 ≤ max |k.1| |k.2| ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) 2
    have h2 : k.2 ^ 2 ≤ max |k.1| |k.2| ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) 2
    nlinarith [sq_nonneg (k.1 + k.2)]

/-- A rational power from a natural one: `x^p ≤ b^q ⇒ x^{p/q} ≤ b`. -/
theorem rpow_div_le {x b : ℝ} (hx : 0 ≤ x) (hb : 0 ≤ b) {p q : ℕ} (hq : 0 < q)
    (h : x ^ p ≤ b ^ q) : x ^ ((p : ℝ) / q) ≤ b := by
  rw [div_eq_mul_inv, Real.rpow_mul hx, Real.rpow_natCast]
  calc (x ^ p) ^ (q : ℝ)⁻¹ ≤ (b ^ q) ^ (q : ℝ)⁻¹ :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = b := Real.pow_rpow_inv_natCast hb hq.ne'

/-- The shell bound at a rational `σ' = a/b` with `2σ' − 2 = p/q`, from
`(3/5)^a ≤ A^b` and `(1/37)^p ≤ C^q`. -/
theorem shell_le {σ' A C : ℝ} {a b p q : ℕ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hb : 0 < b) (hq : 0 < q)
    (hp : 0 < p) (hσa : σ' = (a : ℝ) / b) (hσp : 2 * σ' - 2 = (p : ℝ) / q)
    (hA' : (3 / 5 : ℝ) ^ a ≤ A ^ b) (hC' : (1 / 37 : ℝ) ^ p ≤ C ^ q) :
    8 * ((3 : ℝ) / 5) ^ σ' * (((38 : ℝ) - 1) ^ (2 - 2 * σ') / (2 * σ' - 2))
      ≤ 8 * A * (C / ((p : ℝ) / q)) := by
  have h1 : ((3 : ℝ) / 5) ^ σ' ≤ A := by rw [hσa]; exact rpow_div_le (by norm_num) hA hb hA'
  have h2 : ((38 : ℝ) - 1) ^ (2 - 2 * σ') ≤ C := by
    rw [show (38 : ℝ) - 1 = 37 by norm_num, show 2 - 2 * σ' = -((p : ℝ) / q) by linarith,
      Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]
    simpa [one_div] using rpow_div_le (x := 1 / 37) (by norm_num) hC hq hC'
  rw [hσp]
  have hpq : 0 < (p : ℝ) / q := by positivity
  gcongr

/-- **The tails of `F`** past `10⁴`: the log-weighted shell bound, with
`e > 2.7182818283`. -/
theorem tail_le (j : ℕ) {σ τ σ' A C : ℝ} {a b p q : ℕ} (hτ : 0 < τ) (hσ' : 1 < σ')
    (hσσ' : σ' ≤ σ - j * τ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hb : 0 < b) (hq : 0 < q) (hp : 0 < p)
    (hσa : σ' = (a : ℝ) / b) (hσp : 2 * σ' - 2 = (p : ℝ) / q)
    (hA' : (3 / 5 : ℝ) ^ a ≤ A ^ b) (hC' : (1 / 37 : ℝ) ^ p ≤ C ^ q) :
    ∑' k, (if 10000 < F.q k then lmaj F j σ k else 0)
      ≤ (1 / (2.7182818283 * τ)) ^ j * (8 * A * (C / ((p : ℝ) / q))) := by
  refine (coercive.ltail_le j hτ hσ' hσσ' (m₀ := 38) (by norm_num) (by norm_num)).trans ?_
  simp only [Nat.cast_ofNat]
  refine mul_le_mul (pow_le_pow_left₀ (by positivity) ?_ j)
    (shell_le hA hC hb hq hp hσa hσp hA' hC') ?_ (by positivity)
  · exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_right Real.exp_one_gt_d9.le hτ.le)
  · have : (0 : ℝ) < 2 * σ' - 2 := by linarith
    have : 0 ≤ ((38 : ℝ) - 1) ^ (2 - 2 * σ') := Real.rpow_nonneg (by norm_num) _
    positivity

theorem mem_L2 : P.L2.Mem (Real.log 2) := log2_eq ▸ Iv.mem_log2E 40

theorem mem_P2 : P.P2.Mem (Real.pi / 2) := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  simp only [Iv.Mem, P, U, Nat.cast_ofNat]
  constructor <;> linarith

/-- The Newton constant `c ≈ Z'(z₀)`. -/
noncomputable def c : ℂ := ⟨-24820751 / 10 ^ 8, 10054197 / 10 ^ 8⟩

theorem norm_c : 2677 / 10000 ≤ ‖c‖ := by
  rw [Complex.norm_def, Real.le_sqrt (by norm_num) (Complex.normSq_nonneg _), c,
    Complex.normSq_mk]
  norm_num

/-- **A DAVENPORT–HEILBRONN ZERO**, kernel-checked: the Epstein zeta of
`3x² − 2xy + 2y²` vanishes within `0.03` of the engine's centre
`≈ 1.993941 + 23.019605i`. -/
theorem exists_zero : ∃ z ∈ closedBall (centre P) (((P.Dm : ℝ) - P.D0) / U), Z F z = 0 := by
  set a := boxAcc P (fun x y => F.q (x, y)) 78 10000 with ha
  have hok : a.ok = true := by rw [ha, sweep]
  have e1 : pdev a.rp a.rn 0 ≤ 66 / 10 ^ 7 := by
    rw [ha, sweep]
    exact pdev_le (by norm_num [U]) (by norm_num [U]) (by norm_num [U]) (by norm_num [U])
  have e2 : pdev a.ip a.inn 0 ≤ 7 / 10 ^ 7 := by
    rw [ha, sweep]
    exact pdev_le (by norm_num [U]) (by norm_num [U]) (by norm_num [U]) (by norm_num [U])
  have e3 : pdev a.drp a.drn c.re ≤ 1 / 10 ^ 8 := by
    rw [ha, sweep]
    exact pdev_le (by norm_num [U, c]) (by norm_num [U, c]) (by norm_num [U, c])
      (by norm_num [U, c])
  have e4 : pdev a.dip a.dinn c.im ≤ 1 / 10 ^ 8 := by
    rw [ha, sweep]
    exact pdev_le (by norm_num [U, c]) (by norm_num [U, c]) (by norm_num [U, c])
      (by norm_num [U, c])
  have e5 : a.b2 = 60119912310279762518 := by rw [ha, sweep]
  refine exists_zero_of_acc coercive mem_L2 mem_P2 (by decide) (by decide) (B := 78)
    (N := 10000) (by norm_num) (by decide) (by norm_num [P, U])
    (tail_le 0 one_pos (σ' := 199 / 100) (a := 199) (b := 100) (p := 99) (q := 50)
      (A := 3619 / 10000) (C := 786 / 10 ^ 6) (by norm_num) (by norm_num [P, U]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))
    (tail_le 1 (τ := 1 / 10) (by norm_num) (σ' := 189 / 100) (a := 189) (b := 100) (p := 89)
      (q := 50) (A := 3809 / 10000) (C := 1618 / 10 ^ 6) (by norm_num) (by norm_num [P, U])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num))
    (tail_le 2 (τ := 1 / 10) (by norm_num) (σ' := 176 / 100) (a := 44) (b := 25) (p := 38)
      (q := 25) (A := 4070 / 10000) (C := 4136 / 10 ^ 6) (by norm_num) (by norm_num [P, U])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num))
    (c := c) (cn := 2677 / 10000) (q := 1 / 2) (by norm_num) norm_c (by norm_num) (by norm_num)
    (by rw [← ha]; exact hok) ?_ ?_
  · rw [← ha]
    norm_num [P, U]
    linarith
  · rw [← ha, e5]
    norm_num [P, U]
    linarith

end DH

end Meno
