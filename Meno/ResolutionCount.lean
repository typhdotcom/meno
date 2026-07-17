import Meno.PeriodLattice
import Meno.InfoRatchet

/-! # Resolution Counting: the Keystone's Counting Shadows (K1–K3)

The finite-resolution corollaries stated in PLAN (Phase 24), derived
from the ℤ-form keystone (`Meno/PeriodLattice.lean`). Fix a
resolution `q ≥ 1`: descriptions are cochains `G.E → ZMod q`,
neighbor-local re-descriptions are mod-`q` gradients — `G.gradLin
(ZMod q)`, the *same* graph-level gradient as the real and integer
layers (C1: defined once). Then:

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

variable {G : IncidenceGraph.{u, v}} (Q : IntegralCyclePresentation G)
variable (q : ℕ) [NeZero q]

/-- The mod-`q` cycle basis. -/
def cyclesQ : Fin Q.r → G.E → ZMod q :=
  fun j e => ((Q.cyclesZ j e : ℤ) : ZMod q)

private lemma cast_val_int (a : ZMod q) : ((a.val : ℤ) : ZMod q) = a := by
  rw [Int.cast_natCast]
  exact ZMod.natCast_rightInverse a

omit [NeZero q] in
/-- Casting a dot product, in applied form: pointwise cast
compatibility on both factors transfers the product. -/
private lemma dot_cast_eq (x y : G.E → ℤ) (x' y' : G.E → ZMod q)
    (hx : ∀ e, ((x e : ℤ) : ZMod q) = x' e)
    (hy : ∀ e, ((y e : ℤ) : ZMod q) = y' e) :
    ((x ⬝ᵥ y : ℤ) : ZMod q) = x' ⬝ᵥ y' := by
  show ((∑ e, x e * y e : ℤ) : ZMod q) = ∑ e, x' e * y' e
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hx e, hy e]

/-- Mod-`q` Stokes: mod-`q` gradients have zero mod-`q` periods.
Derived from integer Stokes by lifting the potential. -/
theorem gradQ_period (g : G.V → ZMod q) (j : Fin Q.r) :
    G.grad g ⬝ᵥ Q.cyclesQ q j = 0 := by
  show (fun e => g (G.tgt e) - g (G.src e)) ⬝ᵥ Q.cyclesQ q j = 0
  have hint : (fun e => ((g (G.tgt e)).val : ℤ) - ((g (G.src e)).val : ℤ))
      ⬝ᵥ Q.cyclesZ j = 0 :=
    Q.gradZ_period (fun v => ((g v).val : ℤ)) j
  have hdot := dot_cast_eq (q := q)
    (fun e => ((g (G.tgt e)).val : ℤ) - ((g (G.src e)).val : ℤ))
    (Q.cyclesZ j)
    (fun e => g (G.tgt e) - g (G.src e))
    (Q.cyclesQ q j)
    (fun e => by rw [Int.cast_sub, cast_val_int, cast_val_int])
    (fun e => rfl)
  rw [← hdot, hint, Int.cast_zero]

/-- Mod-`q` period realizability, by reducing an integer witness. -/
theorem periodsQ_onto (k : Fin Q.r → ZMod q) :
    ∃ ω : G.E → ZMod q, ∀ j, ω ⬝ᵥ Q.cyclesQ q j = k j := by
  obtain ⟨ωZ, hω⟩ := Q.periods_onto (fun j => ((k j).val : ℤ))
  refine ⟨fun e => ((ωZ e : ℤ) : ZMod q), fun j => ?_⟩
  have hdot := dot_cast_eq (q := q) ωZ (Q.cyclesZ j)
    (fun e => ((ωZ e : ℤ) : ZMod q)) (Q.cyclesQ q j)
    (fun e => rfl) (fun e => rfl)
  rw [← hdot, hω j]
  exact cast_val_int q (k j)

/-- **Mod-`q` exactness by lift-and-correct**: a mod-`q` cochain with
zero mod-`q` periods is a mod-`q` gradient. -/
theorem exists_potentialQ (ω : G.E → ZMod q)
    (h : ∀ j, ω ⬝ᵥ Q.cyclesQ q j = 0) :
    ∃ g : G.V → ZMod q, G.grad g = ω := by
  -- Lift to ℤ.
  set ωZ : G.E → ℤ := fun e => ((ω e).val : ℤ) with hωZ
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
  have hge : g (G.tgt e) - g (G.src e) = ωZ e - q * τ e := congrFun hg e
  show ((g (G.tgt e) : ℤ) : ZMod q) - ((g (G.src e) : ℤ) : ZMod q) = ω e
  rw [← Int.cast_sub, hge, Int.cast_sub, Int.cast_mul,
    show ((q : ℤ) : ZMod q) = 0 from by
      push_cast
      exact ZMod.natCast_self q,
    zero_mul, sub_zero]
  exact cast_val_int q (ω e)

/-! ## The quotient at resolution `q` -/

/-- The mod-`q` period map as a linear map. -/
noncomputable def periodLinQ : (G.E → ZMod q) →ₗ[ZMod q] (Fin Q.r → ZMod q) where
  toFun ω := fun j => ω ⬝ᵥ Q.cyclesQ q j
  map_add' ω η := funext fun j => add_dotProduct ω η (Q.cyclesQ q j)
  map_smul' c ω := funext fun j => smul_dotProduct c ω (Q.cyclesQ q j)

theorem range_gradLinQ_eq_ker_periodLinQ :
    LinearMap.range (G.gradLin (ZMod q)) = LinearMap.ker (Q.periodLinQ q) := by
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
mod-`q` local re-description are the mod-`q` period space. The
quotient depends only on the graph. -/
noncomputable def latticeQuotEquivQ :
    ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
      ≃ₗ[ZMod q] (Fin Q.r → ZMod q) :=
  (Submodule.quotEquivOfEq _ _ (Q.range_gradLinQ_eq_ker_periodLinQ q)).trans
    ((Q.periodLinQ q).quotKerEquivOfSurjective (Q.periodLinQ_surjective q))

/-! ## K1–K3 -/

/-- **K1 — the residue counts `q ^ b₁`**: at any resolution, the
incompressible content of a description is exactly `b₁`
resolution-digits. -/
theorem card_quotient :
    Nat.card ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
      = q ^ Q.r := by
  rw [Nat.card_congr (Q.latticeQuotEquivQ q).toEquiv]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- **K2 — the description-cost split**: total description cost =
gauge freedom + incompressible residue, in `InfoRatchet`'s literal
log-cardinality vocabulary. -/
theorem log_card_split :
    Real.log (Nat.card (G.E → ZMod q))
      = Real.log (Nat.card (LinearMap.range (G.gradLin (ZMod q))))
        + Q.r * Real.log q := by
  have hLag : Nat.card (G.E → ZMod q)
      = Nat.card ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
        * Nat.card (LinearMap.range (G.gradLin (ZMod q))) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      (LinearMap.range (G.gradLin (ZMod q))).toAddSubgroup
  rw [Q.card_quotient q] at hLag
  have hGpos : 0 < Nat.card (LinearMap.range (G.gradLin (ZMod q))) :=
    Nat.card_pos
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
theorem card_fiber
    (x : (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) :
    Nat.card {y : G.E → ZMod q //
        (Submodule.Quotient.mk y :
          (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) = x}
      = Nat.card (LinearMap.range (G.gradLin (ZMod q))) := by
  obtain ⟨x₀, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine Nat.card_congr
    ⟨fun y => ⟨y.val - x₀, by
        have hy := y.prop
        rwa [Submodule.Quotient.eq] at hy⟩,
      fun g => ⟨x₀ + g.val, by
        rw [eq_comm, Submodule.Quotient.eq]
        have : x₀ - (x₀ + g.val) = -g.val := by abel
        rw [this]
        exact (LinearMap.range (G.gradLin (ZMod q))).neg_mem g.prop⟩,
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
    [Fintype ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))]
    [DecidableEq ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))] :
    fiberInfoCost (fun y : G.E → ZMod q =>
        (Submodule.Quotient.mk y :
          (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))))
      = (q : ℝ) ^ Q.r
        * Real.log (Nat.card (LinearMap.range (G.gradLin (ZMod q)))) := by
  unfold fiberInfoCost
  have hterm : ∀ b : (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)),
      Real.log ((Nat.card ((fun y : G.E → ZMod q =>
          (Submodule.Quotient.mk y :
            (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))))
              ⁻¹' {b}) : ℕ) : ℝ)
        = Real.log (Nat.card (LinearMap.range (G.gradLin (ZMod q)))) := by
    intro b
    congr 2
    exact card_fiber (G := G) q b
  rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, Q.card_quotient q,
    nsmul_eq_mul]
  push_cast
  ring

end IntegralCyclePresentation

end Meno
