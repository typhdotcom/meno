import Meno.PeriodLattice
import Meno.InfoRatchet

/-! # Resolution Counting: the Keystone's Counting Shadows (K1–K3)

The finite-resolution corollaries stated in PLAN (Phase 24), derived
from the ℤ-form keystone (`Meno/PeriodLattice.lean`). Fix a
resolution `q ≥ 1`: descriptions are cochains `ι → ZMod q`,
neighbor-local re-descriptions are mod-`q` gradients. Then:

* **K1** (`card_quotient`): the compression residue counts exactly
  `q ^ b₁` — the incompressible content is `b₁` resolution-digits.
* **K2** (`log_card_split`): `log |C_q| = log |G_q| + b₁ · log q` —
  total description cost = gauge freedom + incompressible residue,
  in `InfoRatchet`'s literal log-cardinality vocabulary.
* **K3** (`card_fiber`): every fiber of the compression map has
  cardinality `|G_q|` — what a section must add back is pure gauge;
  `fiberInfoCost_mk` states this through `fiberInfoCost` itself.

**No new fields.** The mod-`q` layer derives entirely from the
ℤ-form's two fields: surjectivity by reducing an integer witness, and
exactness by the *lift-and-correct* argument — lift `ω` to `ℤ`
through `ZMod.val`; its integer periods are divisible by `q`, say
`q·m`; subtract `q·τ` where `τ` realizes `m` (`periods_onto`); the
corrected cochain has zero integer periods, hence an integer
potential (`integral_potentials`), and the correction vanishes
mod `q`. Total unimodularity by another name: no resolution is bad. -/

namespace Meno

open scoped BigOperators
open Matrix

universe u v

namespace IntegralCyclePresentation

variable {V : Type u} {ι : Type v} [Fintype V] [Fintype ι] [DecidableEq V]
variable (Q : IntegralCyclePresentation V ι)
variable (q : ℕ) [NeZero q]

/-- The mod-`q` cycle basis. -/
def cyclesQ : Fin Q.r → ι → ZMod q :=
  fun j e => ((Q.cyclesZ j e : ℤ) : ZMod q)

private lemma cast_val_int (a : ZMod q) : ((a.val : ℤ) : ZMod q) = a := by
  rw [Int.cast_natCast]
  exact ZMod.natCast_rightInverse a

/-- Casting a dot product, in applied form: pointwise cast
compatibility on both factors transfers the product. -/
private lemma dot_cast_eq (x y : ι → ℤ) (x' y' : ι → ZMod q)
    (hx : ∀ e, ((x e : ℤ) : ZMod q) = x' e)
    (hy : ∀ e, ((y e : ℤ) : ZMod q) = y' e) :
    ((x ⬝ᵥ y : ℤ) : ZMod q) = x' ⬝ᵥ y' := by
  show ((∑ e, x e * y e : ℤ) : ZMod q) = ∑ e, x' e * y' e
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hx e, hy e]

/-- Mod-`q` Stokes: mod-`q` gradients have zero mod-`q` periods.
Derived from integer Stokes by lifting the potential. -/
theorem gradQ_period (g : V → ZMod q) (j : Fin Q.r) :
    (fun e => g (Q.tgt e) - g (Q.src e)) ⬝ᵥ Q.cyclesQ q j = 0 := by
  have hint := Q.gradZ_period (fun v => ((g v).val : ℤ)) j
  have hdot := dot_cast_eq (q := q)
    (fun e => ((g (Q.tgt e)).val : ℤ) - ((g (Q.src e)).val : ℤ))
    (Q.cyclesZ j)
    (fun e => g (Q.tgt e) - g (Q.src e))
    (Q.cyclesQ q j)
    (fun e => by rw [Int.cast_sub, cast_val_int, cast_val_int])
    (fun e => rfl)
  rw [← hdot, hint, Int.cast_zero]

/-- Mod-`q` period realizability, by reducing an integer witness. -/
theorem periodsQ_onto (k : Fin Q.r → ZMod q) :
    ∃ ω : ι → ZMod q, ∀ j, ω ⬝ᵥ Q.cyclesQ q j = k j := by
  obtain ⟨ωZ, hω⟩ := Q.periods_onto (fun j => ((k j).val : ℤ))
  refine ⟨fun e => ((ωZ e : ℤ) : ZMod q), fun j => ?_⟩
  have hdot := dot_cast_eq (q := q) ωZ (Q.cyclesZ j)
    (fun e => ((ωZ e : ℤ) : ZMod q)) (Q.cyclesQ q j)
    (fun e => rfl) (fun e => rfl)
  rw [← hdot, hω j]
  exact cast_val_int q (k j)

/-- **Mod-`q` exactness by lift-and-correct**: a mod-`q` cochain with
zero mod-`q` periods is a mod-`q` gradient. -/
theorem exists_potentialQ (ω : ι → ZMod q)
    (h : ∀ j, ω ⬝ᵥ Q.cyclesQ q j = 0) :
    ∃ g : V → ZMod q, (fun e => g (Q.tgt e) - g (Q.src e)) = ω := by
  -- Lift to ℤ.
  set ωZ : ι → ℤ := fun e => ((ω e).val : ℤ) with hωZ
  -- Integer periods are divisible by q.
  have hdvd : ∀ j, (q : ℤ) ∣ ωZ ⬝ᵥ Q.cyclesZ j := by
    intro j
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hdot := dot_cast_eq (q := q) ωZ (Q.cyclesZ j) ω (Q.cyclesQ q j)
      (fun e => cast_val_int q (ω e)) (fun e => rfl)
    rw [hdot]
    exact h j
  choose m hm using hdvd
  -- Correct by an integer realization of m.
  obtain ⟨τ, hτ⟩ := Q.periods_onto m
  have hper : ∀ j, (fun e => ωZ e - q * τ e) ⬝ᵥ Q.cyclesZ j = 0 := by
    intro j
    have hsplit : (fun e => ωZ e - q * τ e) ⬝ᵥ Q.cyclesZ j
        = ωZ ⬝ᵥ Q.cyclesZ j - q * (τ ⬝ᵥ Q.cyclesZ j) := by
      show ∑ e, (ωZ e - q * τ e) * Q.cyclesZ j e = _
      rw [show (∑ e, (ωZ e - q * τ e) * Q.cyclesZ j e)
          = ∑ e, (ωZ e * Q.cyclesZ j e - q * (τ e * Q.cyclesZ j e)) from
        Finset.sum_congr rfl fun e _ => by ring]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rfl
    rw [hsplit, hτ j, hm j]
    ring
  obtain ⟨g, hg⟩ := Q.integral_potentials (fun e => ωZ e - q * τ e) hper
  refine ⟨fun v => ((g v : ℤ) : ZMod q), funext fun e => ?_⟩
  have hge : g (Q.tgt e) - g (Q.src e) = ωZ e - q * τ e := congrFun hg e
  show ((g (Q.tgt e) : ℤ) : ZMod q) - ((g (Q.src e) : ℤ) : ZMod q) = ω e
  rw [← Int.cast_sub, hge, Int.cast_sub, Int.cast_mul,
    show ((q : ℤ) : ZMod q) = 0 from by
      push_cast
      exact ZMod.natCast_self q,
    zero_mul, sub_zero]
  exact cast_val_int q (ω e)

/-! ## The quotient at resolution `q` -/

/-- The mod-`q` gradient as a linear map. -/
noncomputable def gradLinQ : (V → ZMod q) →ₗ[ZMod q] (ι → ZMod q) where
  toFun g := fun e => g (Q.tgt e) - g (Q.src e)
  map_add' f g := funext fun e => by
    show (f + g) (Q.tgt e) - (f + g) (Q.src e)
      = (f (Q.tgt e) - f (Q.src e)) + (g (Q.tgt e) - g (Q.src e))
    simp only [Pi.add_apply]
    ring
  map_smul' c f := funext fun e => by
    show (c • f) (Q.tgt e) - (c • f) (Q.src e)
      = c * (f (Q.tgt e) - f (Q.src e))
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- The mod-`q` period map as a linear map. -/
noncomputable def periodLinQ : (ι → ZMod q) →ₗ[ZMod q] (Fin Q.r → ZMod q) where
  toFun ω := fun j => ω ⬝ᵥ Q.cyclesQ q j
  map_add' ω η := funext fun j => add_dotProduct ω η (Q.cyclesQ q j)
  map_smul' c ω := funext fun j => smul_dotProduct c ω (Q.cyclesQ q j)

theorem range_gradLinQ_eq_ker_periodLinQ :
    LinearMap.range (Q.gradLinQ q) = LinearMap.ker (Q.periodLinQ q) := by
  ext ω
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨g, rfl⟩
    funext j
    exact Q.gradQ_period q g j
  · intro h
    exact Q.exists_potentialQ q ω (fun j => congrFun h j)

theorem periodLinQ_surjective : Function.Surjective (Q.periodLinQ q) := by
  intro k
  obtain ⟨ω, hω⟩ := Q.periodsQ_onto q k
  exact ⟨ω, funext hω⟩

/-- The keystone at resolution `q`: mod-`q` descriptions modulo
mod-`q` local re-description are the mod-`q` period space. -/
noncomputable def latticeQuotEquivQ :
    ((ι → ZMod q) ⧸ LinearMap.range (Q.gradLinQ q))
      ≃ₗ[ZMod q] (Fin Q.r → ZMod q) :=
  (Submodule.quotEquivOfEq _ _ (Q.range_gradLinQ_eq_ker_periodLinQ q)).trans
    ((Q.periodLinQ q).quotKerEquivOfSurjective (Q.periodLinQ_surjective q))

/-! ## K1–K3 -/

/-- **K1 — the residue counts `q ^ b₁`**: at any resolution, the
incompressible content of a description is exactly `b₁`
resolution-digits. -/
theorem card_quotient :
    Nat.card ((ι → ZMod q) ⧸ LinearMap.range (Q.gradLinQ q)) = q ^ Q.r := by
  rw [Nat.card_congr (Q.latticeQuotEquivQ q).toEquiv]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- **K2 — the description-cost split**: total description cost =
gauge freedom + incompressible residue, in `InfoRatchet`'s literal
log-cardinality vocabulary. -/
theorem log_card_split :
    Real.log (Nat.card (ι → ZMod q))
      = Real.log (Nat.card (LinearMap.range (Q.gradLinQ q)))
        + Q.r * Real.log q := by
  have hLag : Nat.card (ι → ZMod q)
      = Nat.card ((ι → ZMod q) ⧸ LinearMap.range (Q.gradLinQ q))
        * Nat.card (LinearMap.range (Q.gradLinQ q)) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      (LinearMap.range (Q.gradLinQ q)).toAddSubgroup
  rw [Q.card_quotient q] at hLag
  have hGpos : 0 < Nat.card (LinearMap.range (Q.gradLinQ q)) := Nat.card_pos
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [hLag, Nat.cast_mul, Nat.cast_pow,
    Real.log_mul (pow_ne_zero _ (by exact_mod_cast hq.ne'))
      (by exact_mod_cast hGpos.ne'),
    Real.log_pow]
  ring

omit [NeZero q] in
/-- **K3 — fiber uniformity**: every fiber of the compression map has
exactly `|G_q|` descriptions — specifying a description given its
class is pure gauge choice. -/
theorem card_fiber (x : (ι → ZMod q) ⧸ LinearMap.range (Q.gradLinQ q)) :
    Nat.card {y : ι → ZMod q //
        (Submodule.Quotient.mk y :
          (ι → ZMod q) ⧸ LinearMap.range (Q.gradLinQ q)) = x}
      = Nat.card (LinearMap.range (Q.gradLinQ q)) := by
  obtain ⟨x₀, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine Nat.card_congr
    ⟨fun y => ⟨y.val - x₀, by
        have hy := y.prop
        rwa [Submodule.Quotient.eq] at hy⟩,
      fun g => ⟨x₀ + g.val, by
        rw [eq_comm, Submodule.Quotient.eq]
        have : x₀ - (x₀ + g.val) = -g.val := by abel
        rw [this]
        exact (LinearMap.range (Q.gradLinQ q)).neg_mem g.prop⟩,
      fun y => by
        apply Subtype.ext
        show x₀ + (y.val - x₀) = y.val
        abel,
      fun g => by
        apply Subtype.ext
        show (x₀ + g.val) - x₀ = g.val
        abel⟩

/-- K3 through `fiberInfoCost` itself: the fiber information of the
compression map is `q ^ b₁` classes' worth of pure gauge. -/
theorem fiberInfoCost_mk
    [Fintype ((ι → ZMod q) ⧸ LinearMap.range (Q.gradLinQ q))]
    [DecidableEq ((ι → ZMod q) ⧸ LinearMap.range (Q.gradLinQ q))] :
    fiberInfoCost (fun y : ι → ZMod q =>
        (Submodule.Quotient.mk y :
          (ι → ZMod q) ⧸ LinearMap.range (Q.gradLinQ q)))
      = (q : ℝ) ^ Q.r
        * Real.log (Nat.card (LinearMap.range (Q.gradLinQ q))) := by
  unfold fiberInfoCost
  have hterm : ∀ b : (ι → ZMod q) ⧸ LinearMap.range (Q.gradLinQ q),
      Real.log ((Nat.card ((fun y : ι → ZMod q =>
          (Submodule.Quotient.mk y :
            (ι → ZMod q) ⧸ LinearMap.range (Q.gradLinQ q))) ⁻¹' {b}) : ℕ) : ℝ)
        = Real.log (Nat.card (LinearMap.range (Q.gradLinQ q))) := by
    intro b
    congr 2
    exact Q.card_fiber q b
  rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, Q.card_quotient q,
    nsmul_eq_mul]
  push_cast
  ring

end IntegralCyclePresentation

end Meno
