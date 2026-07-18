import Meno.GraphHomology
import Meno.InfoRatchet
import Meno.UniformAction
import Meno.BasisIndependence
import Mathlib.Algebra.Module.ZMod

/-! # Resolution Counting: the Keystone's Counting Shadows (K1–K3)

The finite-resolution corollaries stated in PLAN (Phase 24), derived
from the ℤ-form keystone (`Meno/GraphHomology.lean`). Fix a
resolution `q ≥ 1`: descriptions are cochains `G.E → ZMod q`,
neighbor-local re-descriptions are mod-`q` gradients — `G.gradLin
(ZMod q)`, the *same* graph-level gradient as the real and integer
layers (C1: defined once). Then, through any lattice basis
`B : Module.Basis (Fin n) ℤ G.cycleLattice` (review #5 — no
presentation structure, no stored fields):

* **K1** (`card_quotient`): the compression residue counts exactly
  `q ^ b₁` — the incompressible content is `b₁` resolution-digits.
* **K2** (`log_card_split`): `log |C_q| = log |G_q| + b₁ · log q` —
  total description cost = gauge freedom + incompressible residue,
  in `InfoRatchet`'s literal log-cardinality vocabulary.
* **K3** (`card_fiber`): every fiber of the compression map has
  cardinality `|G_q|` — what a section must add back is pure gauge;
  `fiberInfoCost_mk` states this through `fiberInfoCost` itself.

The mod-`q` layer derives entirely from the basis's theorems:
surjectivity by reducing an integer witness (`periods_onto`), and
exactness by the *lift-and-correct* argument — lift `ω` to `ℤ`
through `ZMod.val`; its integer periods are divisible by `q`, say
`q·m`; subtract `q·τ` where `τ` realizes `m`; the corrected cochain
has zero integer periods, hence an integer potential
(`integral_potentials`), and the correction vanishes mod `q`. Total
unimodularity by another name: no resolution is bad. -/

namespace Meno

open scoped BigOperators
open Matrix

universe u v

/-- **The one fiber-to-kernel equivalence** (review #9): the fiber of a
linear map over any attained value is a coset of its kernel — shift by
a chosen preimage. Every K3 fiber statement below (`card_fiber`,
`compressionFiberEquivGauge`, `carrierFiberEquivGauge`) derives from
this single construction. -/
def fiberEquivKer {R : Type*} {M : Type*} {N : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) {y : N} (x₀ : M) (hx₀ : f x₀ = y) :
    {x : M // f x = y} ≃ LinearMap.ker f where
  toFun x := ⟨x.val - x₀, by
    rw [LinearMap.mem_ker, map_sub, x.prop, hx₀, sub_self]⟩
  invFun g := ⟨x₀ + g.val, by
    rw [map_add, hx₀, LinearMap.mem_ker.mp g.prop, add_zero]⟩
  left_inv x := Subtype.ext (by
    show x₀ + (x.val - x₀) = x.val
    abel)
  right_inv g := Subtype.ext (by
    show (x₀ + g.val) - x₀ = g.val
    abel)

namespace IncidenceGraph

variable (G : IncidenceGraph.{u, v})
variable {n : ℕ} (B : Module.Basis (Fin n) ℤ G.cycleLattice)
variable (q : ℕ) [NeZero q]

/-- The mod-`q` cycle basis of a lattice basis. -/
noncomputable def cyclesQ : Fin n → G.E → ZMod q :=
  fun j e => ((G.cyclesZ B j e : ℤ) : ZMod q)

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
theorem gradQ_period (g : G.V → ZMod q) (j : Fin n) :
    G.grad g ⬝ᵥ G.cyclesQ B q j = 0 := by
  show (fun e => g (G.tgt e) - g (G.src e)) ⬝ᵥ G.cyclesQ B q j = 0
  have hint : (fun e => ((g (G.tgt e)).val : ℤ) - ((g (G.src e)).val : ℤ))
      ⬝ᵥ G.cyclesZ B j = 0 :=
    G.gradZ_period B (fun v => ((g v).val : ℤ)) j
  have hdot := G.dot_cast_eq (q := q)
    (fun e => ((g (G.tgt e)).val : ℤ) - ((g (G.src e)).val : ℤ))
    (G.cyclesZ B j)
    (fun e => g (G.tgt e) - g (G.src e))
    (G.cyclesQ B q j)
    (fun e => by rw [Int.cast_sub, cast_val_int, cast_val_int])
    (fun e => rfl)
  rw [← hdot, hint, Int.cast_zero]

/-- Mod-`q` period realizability, by reducing an integer witness. -/
theorem periodsQ_onto (k : Fin n → ZMod q) :
    ∃ ω : G.E → ZMod q, ∀ j, ω ⬝ᵥ G.cyclesQ B q j = k j := by
  obtain ⟨ωZ, hω⟩ := G.periods_onto B (fun j => ((k j).val : ℤ))
  refine ⟨fun e => ((ωZ e : ℤ) : ZMod q), fun j => ?_⟩
  have hdot := G.dot_cast_eq (q := q) ωZ (G.cyclesZ B j)
    (fun e => ((ωZ e : ℤ) : ZMod q)) (G.cyclesQ B q j)
    (fun e => rfl) (fun e => rfl)
  rw [← hdot, hω j]
  exact cast_val_int q (k j)

/-- **Mod-`q` exactness by lift-and-correct**: a mod-`q` cochain with
zero mod-`q` periods is a mod-`q` gradient. -/
theorem exists_potentialQ (ω : G.E → ZMod q)
    (h : ∀ j, ω ⬝ᵥ G.cyclesQ B q j = 0) :
    ∃ g : G.V → ZMod q, G.grad g = ω := by
  -- Lift to ℤ.
  set ωZ : G.E → ℤ := fun e => ((ω e).val : ℤ) with hωZ
  -- Integer periods are divisible by q.
  have hdvd : ∀ j, (q : ℤ) ∣ ωZ ⬝ᵥ G.cyclesZ B j := by
    intro j
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hdot := G.dot_cast_eq (q := q) ωZ (G.cyclesZ B j) ω (G.cyclesQ B q j)
      (fun e => cast_val_int q (ω e)) (fun e => rfl)
    rw [hdot]
    exact h j
  choose m hm using hdvd
  -- Correct by an integer realization of m.
  obtain ⟨τ, hτ⟩ := G.periods_onto B m
  have hper : ∀ j, (fun e => ωZ e - q * τ e) ⬝ᵥ G.cyclesZ B j = 0 := by
    intro j
    have hsplit : (fun e => ωZ e - q * τ e) ⬝ᵥ G.cyclesZ B j
        = ωZ ⬝ᵥ G.cyclesZ B j - q * (τ ⬝ᵥ G.cyclesZ B j) := by
      show ∑ e, (ωZ e - q * τ e) * G.cyclesZ B j e = _
      rw [show (∑ e, (ωZ e - q * τ e) * G.cyclesZ B j e)
          = ∑ e, (ωZ e * G.cyclesZ B j e - q * (τ e * G.cyclesZ B j e)) from
        Finset.sum_congr rfl fun e _ => by ring]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rfl
    rw [hsplit, hτ j, hm j]
    ring
  obtain ⟨g, hg⟩ := G.integral_potentials B (fun e => ωZ e - q * τ e) hper
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
noncomputable def periodLinQ :
    (G.E → ZMod q) →ₗ[ZMod q] (Fin n → ZMod q) where
  toFun ω := fun j => ω ⬝ᵥ G.cyclesQ B q j
  map_add' ω η := funext fun j => add_dotProduct ω η (G.cyclesQ B q j)
  map_smul' c ω := funext fun j => smul_dotProduct c ω (G.cyclesQ B q j)

theorem range_gradLinQ_eq_ker_periodLinQ :
    LinearMap.range (G.gradLin (ZMod q))
      = LinearMap.ker (G.periodLinQ B q) := by
  ext ω
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨g, rfl⟩
    funext j
    exact G.gradQ_period B q g j
  · intro h
    exact G.exists_potentialQ B q ω (fun j => congrFun h j)

theorem periodLinQ_surjective : Function.Surjective (G.periodLinQ B q) := by
  intro k
  obtain ⟨ω, hω⟩ := G.periodsQ_onto B q k
  exact ⟨ω, funext hω⟩

/-- The keystone at resolution `q`: mod-`q` descriptions modulo
mod-`q` local re-description are the mod-`q` period space. The
quotient depends only on the graph. -/
noncomputable def latticeQuotEquivQ :
    ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
      ≃ₗ[ZMod q] (Fin n → ZMod q) :=
  (Submodule.quotEquivOfEq _ _
    (G.range_gradLinQ_eq_ker_periodLinQ B q)).trans
    ((G.periodLinQ B q).quotKerEquivOfSurjective
      (G.periodLinQ_surjective B q))

/-! ## K1–K3 -/

include B in
/-- **K1 — the residue counts `q ^ n` (= `q ^ b₁`)**: at any
resolution, the incompressible content of a description is exactly
`b₁` resolution-digits. -/
theorem card_quotient :
    Nat.card ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
      = q ^ n := by
  rw [Nat.card_congr (G.latticeQuotEquivQ B q).toEquiv]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

include B in
/-- **K2 — the description-cost split**: total description cost =
gauge freedom + incompressible residue, in `InfoRatchet`'s literal
log-cardinality vocabulary. -/
theorem log_card_split :
    Real.log (Nat.card (G.E → ZMod q))
      = Real.log (Nat.card (LinearMap.range (G.gradLin (ZMod q))))
        + n * Real.log q := by
  have hLag : Nat.card (G.E → ZMod q)
      = Nat.card ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
        * Nat.card (LinearMap.range (G.gradLin (ZMod q))) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      (LinearMap.range (G.gradLin (ZMod q))).toAddSubgroup
  rw [G.card_quotient B q] at hLag
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
class is pure gauge choice. Derived from the one fiber-to-kernel
equivalence (review #9): the class map is `Submodule.mkQ`, whose
kernel is the gauge group. -/
theorem card_fiber
    (x : (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) :
    Nat.card {y : G.E → ZMod q //
        (Submodule.Quotient.mk y :
          (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) = x}
      = Nat.card (LinearMap.range (G.gradLin (ZMod q))) := by
  obtain ⟨x₀, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h := Nat.card_congr (fiberEquivKer
    (Submodule.mkQ (LinearMap.range (G.gradLin (ZMod q)))) x₀ rfl)
  rw [Submodule.ker_mkQ] at h
  exact h

include B in
/-- K3 through `fiberInfoCost` itself: the fiber information of the
compression map is `q ^ b₁` classes' worth of pure gauge. -/
theorem fiberInfoCost_mk
    [Fintype ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))]
    [DecidableEq ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))] :
    fiberInfoCost (fun y : G.E → ZMod q =>
        (Submodule.Quotient.mk y :
          (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))))
      = (q : ℝ) ^ n
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
    exact G.card_fiber q b
  rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, G.card_quotient B q,
    nsmul_eq_mul]
  push_cast
  ring

/-! ## C8: the section count of the compression map

The keystone's counting shadows meet the coding theorem
(`Meno/InfoRatchet.lean`): a *section* of the mod-`q` compression map is
a gauge-fixing — a choice of description for each class. There are
`|G_q|^{q^{b₁}}` of them, and the log of that count is exactly the fiber
information `fiberInfoCost_mk` (K3). Reversing compression is genuinely
costly, and the cost is now *counted*, not defined. -/

include B in
/-- **The gauge group is `q^{|E|−b₁}`**: the mod-`q` local
re-descriptions number exactly `q` per non-cycle edge. Together with K1
(`q^{b₁}` classes) this is Euler's `|E| = (|E|−b₁) + b₁` read as a
count. -/
theorem card_gauge :
    Nat.card (LinearMap.range (G.gradLin (ZMod q)))
      = q ^ (Fintype.card G.E - n) := by
  have hLag : Nat.card (G.E → ZMod q)
      = Nat.card ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
        * Nat.card (LinearMap.range (G.gradLin (ZMod q))) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      (LinearMap.range (G.gradLin (ZMod q))).toAddSubgroup
  rw [G.card_quotient B q] at hLag
  have hE : Nat.card (G.E → ZMod q) = q ^ Fintype.card G.E := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := ZMod q), ZMod.card,
      Nat.card_eq_fintype_card (α := G.E)]
  rw [hE] at hLag
  have hsplit := G.card_edges_eq_finrank_gauge_add B
  have hr : n ≤ Fintype.card G.E := by omega
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hpow : q ^ n * q ^ (Fintype.card G.E - n) = q ^ Fintype.card G.E := by
    rw [← pow_add, Nat.add_sub_cancel' hr]
  rw [← hpow] at hLag
  exact (Nat.eq_of_mul_eq_mul_left (pow_pos hq n) hLag).symm

include B in
/-- **The number of gauge-fixings** (C8, closed form): a section of the
compression map chooses a representative per class, and there are
`|G_q|^{q^{b₁}}` of them — `|G_q|` gauge choices, independently, for each
of the `q^{b₁}` incompressible classes. -/
theorem card_compression_sections :
    Nat.card {s : ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
        → (G.E → ZMod q) //
        ∀ x, (Submodule.Quotient.mk (s x) :
          (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) = x}
      = Nat.card (LinearMap.range (G.gradLin (ZMod q))) ^ (q ^ n) := by
  haveI : Finite ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  haveI := Fintype.ofFinite
    ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
  have hfib : ∀ x, Nat.card ((fun y : G.E → ZMod q =>
        (Submodule.Quotient.mk y :
          (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))) ⁻¹' {x})
      = Nat.card (LinearMap.range (G.gradLin (ZMod q))) :=
    fun x => G.card_fiber q x
  rw [card_sections (fun y : G.E → ZMod q => Submodule.Quotient.mk y),
    Finset.prod_congr rfl (fun x _ => hfib x),
    Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    G.card_quotient B q]

/-- **The per-class recovery cost**: recovering which description
produced *one* class costs `log |G_q|` — the fiber ambiguity of a
single output (K3 in `recoveryCost` form). `[NeZero q]` is load-bearing
(review #3): at `q = 0` the fibers are infinite and the numerical cost
API refuses them. -/
theorem recoveryCost_compression
    (x : (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) :
    recoveryCost (fun y : G.E → ZMod q =>
        (Submodule.Quotient.mk y :
          (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))) x
      = Real.log (Nat.card (LinearMap.range (G.gradLin (ZMod q)))) := by
  unfold recoveryCost
  congr 2
  exact G.card_fiber q x

include B in
/-- **The global gauge-fixing cost** (the decoder-*table* cost, not the
per-class cost): a section fixes a representative for *every* class at
once, so its log-count is the aggregate `q^{b₁} · log |G_q|` — the
fiber information (`fiberInfoCost_mk`) realized as the log-count of
sections (`log_card_sections`). Recovering a *single* class costs only
`log |G_q|` (`recoveryCost_compression`). -/
theorem sectionCost_compression :
    sectionCost (fun y : G.E → ZMod q =>
        (Submodule.Quotient.mk y :
          (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))))
      = (q : ℝ) ^ n
        * Real.log (Nat.card (LinearMap.range (G.gradLin (ZMod q)))) := by
  haveI : Finite ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  haveI := Fintype.ofFinite
    ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
  haveI : DecidableEq ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) :=
    Classical.decEq _
  have hsurj : Function.Surjective (fun y : G.E → ZMod q =>
      (Submodule.Quotient.mk y :
        (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))) :=
    Submodule.Quotient.mk_surjective _
  rw [log_card_sections hsurj, G.fiberInfoCost_mk B q]

/-- **K1 for every finite graph**: at every resolution `q ≥ 1`, the
compression residue counts exactly `q ^ b₁` — through the fundamental
basis, with no per-graph hypotheses. -/
theorem card_quotient_eq :
    Nat.card ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
      = q ^ G.b1 :=
  G.card_quotient G.cycleBasis q

/-! ## The information face on the sector-action carrier

The bridge review #5 (finding 5) demanded: the finite-resolution
residue is not merely *counted* — it inhabits the thesis's advertised
carrier, a sector lattice with its action. The compression residue,
the description space, and the gauge group are each a **uniform
sector action** (`Meno/UniformAction.lean`: every state a sector,
every sector free), and:

* the residue's complexity is exactly `b₁ · log q`
  (`uniformAction_quotient_complexity`) — the incompressible content,
  as a sector-action complexity;
* K2 becomes a complexity identity of sector actions
  (`uniformComplexity_split`): description complexity = gauge
  complexity + residue complexity. -/

/-- The description quotient at a positive resolution is finite. -/
noncomputable instance descQuotFintype :
    Fintype ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) :=
  haveI : Finite ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  Fintype.ofFinite _

instance descQuotNonempty :
    Nonempty ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) :=
  ⟨0⟩

/-- The gauge group at a positive resolution is finite. -/
noncomputable instance gaugeFintype :
    Fintype ↥(LinearMap.range (G.gradLin (ZMod q))) :=
  haveI : Finite ↥(LinearMap.range (G.gradLin (ZMod q))) := Subtype.finite
  Fintype.ofFinite _

instance gaugeNonempty : Nonempty ↥(LinearMap.range (G.gradLin (ZMod q))) :=
  ⟨0⟩

/-- The compression residue's uniform partition function is `q^{b₁}`:
the Boltzmann sum over the residue simply counts the incompressible
classes. -/
theorem uniformAction_quotient_partFn :
    (uniformAction
        ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))).partFn
      = (q : ℝ) ^ G.b1 := by
  rw [uniformAction_partFn, ← Nat.card_eq_fintype_card, G.card_quotient_eq q]
  push_cast
  ring

/-- **The information face inhabits the carrier** (review #5,
finding 5): the compression residue, as a uniform sector action, has
complexity exactly `b₁ · log q` — the incompressible content of a
description is a sector-action complexity, not merely a count. -/
theorem uniformAction_quotient_complexity :
    (uniformAction
        ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))).complexity
      = G.b1 * Real.log q := by
  rw [uniformAction_complexity, ← Nat.card_eq_fintype_card,
    G.card_quotient_eq q]
  push_cast [Real.log_pow]
  ring

/-- **K2 on the sector-action carrier**: the description-cost split
`log |C_q| = log |G_q| + b₁ · log q` as an identity of uniform
sector-action complexities — description complexity = gauge
complexity + residue complexity. -/
theorem uniformComplexity_split :
    (uniformAction (G.E → ZMod q)).complexity
      = (uniformAction ↥(LinearMap.range (G.gradLin (ZMod q)))).complexity
        + (uniformAction
            ((G.E → ZMod q)
              ⧸ LinearMap.range (G.gradLin (ZMod q)))).complexity := by
  rw [uniformAction_complexity, uniformAction_complexity,
    G.uniformAction_quotient_complexity q, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card]
  exact G.log_card_split G.cycleBasis q

/-! ## The finite reduction of the intrinsic carrier

Review #6, finding 1: the residue is not merely a finite type sharing
the `uniformAction` API — it is the **finite reduction of the one
integral carrier**. The intrinsic carrier's lattice is
`H¹(G;ℤ) = (G.E → ℤ) ⧸ range ∂ᵀℤ` (the sector lattice of
`classSectorAction`, `Meno/BasisIndependence.lean`, definitionally by
`classSectorAction_Λ`). Coefficient reduction `h1Res` maps it onto the
resolution-`q` residue, its kernel is exactly `q·H¹(G;ℤ)`
(`ker_h1Res`), so the residue **is** `H¹(G;ℤ) ⧸ q·H¹(G;ℤ)`
(`h1ResQuotEquiv`), the coordinates commute with the keystones
(`latticeQuotEquivQ_h1Res`), and the uniform complexity and the K2
split are derived **through that reduction**
(`uniformAction_h1ResQuot_complexity`,
`uniformComplexity_split_carrier`). -/

omit [NeZero q] in
/-- Componentwise mod-`q` reduction of integer cochains, landing in
the resolution-`q` description quotient. -/
noncomputable def cochainResHom :
    (G.E → ℤ) →+ ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) where
  toFun τ := Submodule.Quotient.mk (fun e => ((τ e : ℤ) : ZMod q))
  map_zero' := by
    rw [show (fun e => (((0 : G.E → ℤ) e : ℤ) : ZMod q))
        = (0 : G.E → ZMod q) from funext fun e => by
      show ((0 : ℤ) : ZMod q) = 0
      exact Int.cast_zero]
    rfl
  map_add' τ σ := by
    rw [show (fun e => (((τ + σ) e : ℤ) : ZMod q))
        = (fun e => ((τ e : ℤ) : ZMod q)) + fun e => ((σ e : ℤ) : ZMod q) from
      funext fun e => by
        show ((τ e + σ e : ℤ) : ZMod q) = ((τ e : ℤ) : ZMod q) + ((σ e : ℤ) : ZMod q)
        push_cast
        rfl]
    exact Submodule.Quotient.mk_add _

omit [NeZero q] in
/-- Gradients reduce to gradients, so the reduction descends to the
intrinsic carrier's lattice `H¹(G;ℤ)`. -/
noncomputable def h1Res :
    ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) →ₗ[ℤ]
      ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) :=
  Submodule.liftQ _ (G.cochainResHom q).toIntLinearMap (by
    rintro τ ⟨g, rfl⟩
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (fun e => (((G.gradLin ℤ g) e : ℤ) : ZMod q))
      = (0 : (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨fun v => ((g v : ℤ) : ZMod q), ?_⟩
    funext e
    show ((g (G.tgt e) : ℤ) : ZMod q) - ((g (G.src e) : ℤ) : ZMod q)
      = ((g (G.tgt e) - g (G.src e) : ℤ) : ZMod q)
    push_cast
    rfl)

omit [NeZero q] in
theorem h1Res_mk (τ : G.E → ℤ) :
    G.h1Res q (Submodule.Quotient.mk τ)
      = Submodule.Quotient.mk (fun e => ((τ e : ℤ) : ZMod q)) := rfl

/-- The reduction is surjective: every mod-`q` class lifts through
`ZMod.val`. -/
theorem h1Res_surjective : Function.Surjective (G.h1Res q) := by
  intro x
  obtain ⟨ω, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine ⟨Submodule.Quotient.mk (fun e => ((ω e).val : ℤ)), ?_⟩
  rw [G.h1Res_mk q]
  exact congrArg _ (funext fun e => cast_val_int q (ω e))

/-- **The identification with the resolution keystone**: reducing a
class and reading mod-`q` coordinates equals reading integer
coordinates and reducing them — the square with `latticeQuotEquiv`
and `latticeQuotEquivQ` commutes, for every basis. -/
theorem latticeQuotEquivQ_h1Res
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :
    G.latticeQuotEquivQ B q (G.h1Res q κ)
      = fun j => (((G.latticeQuotEquiv B κ) j : ℤ) : ZMod q) := by
  obtain ⟨τ, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  funext j
  show (fun e => ((τ e : ℤ) : ZMod q)) ⬝ᵥ G.cyclesQ B q j
    = ((τ ⬝ᵥ G.cyclesZ B j : ℤ) : ZMod q)
  exact (G.dot_cast_eq q τ (G.cyclesZ B j)
    (fun e => ((τ e : ℤ) : ZMod q)) (G.cyclesQ B q j)
    (fun e => rfl) (fun e => rfl)).symm

/-- **The kernel is exactly `q·H¹(G;ℤ)`**: the reduction kills
precisely the `q`-th multiples of the integral carrier. -/
theorem ker_h1Res :
    LinearMap.ker (G.h1Res q)
      = LinearMap.range ((q : ℤ) •
          (LinearMap.id :
            ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) →ₗ[ℤ]
              ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)))) := by
  ext κ
  constructor
  · intro hκ
    rw [LinearMap.mem_ker] at hκ
    have hsq := G.latticeQuotEquivQ_h1Res G.cycleBasis q κ
    rw [hκ, map_zero] at hsq
    have hx : ∀ j, ((G.latticeQuotEquiv G.cycleBasis κ j : ℤ) : ZMod q) = 0 :=
      fun j => (congrFun hsq.symm j).symm ▸ rfl
    have hdvd : ∀ j, (q : ℤ) ∣ G.latticeQuotEquiv G.cycleBasis κ j := by
      intro j
      have h := hx j
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    choose y hy using hdvd
    rw [LinearMap.mem_range]
    refine ⟨(G.latticeQuotEquiv G.cycleBasis).symm y, ?_⟩
    show (q : ℤ) • ((G.latticeQuotEquiv G.cycleBasis).symm y) = κ
    apply (G.latticeQuotEquiv G.cycleBasis).injective
    rw [map_smul, LinearEquiv.apply_symm_apply]
    funext j
    show (q : ℤ) • y j = G.latticeQuotEquiv G.cycleBasis κ j
    rw [smul_eq_mul]
    exact (hy j).symm
  · rintro ⟨κ', hκ'⟩
    rw [LinearMap.mem_ker, ← hκ']
    show G.h1Res q ((q : ℤ) • κ') = 0
    rw [map_smul]
    generalize G.h1Res q κ' = x
    obtain ⟨ω, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hω : (q : ℤ) • ω = (0 : G.E → ZMod q) := by
      funext e
      show (q : ℤ) • ω e = 0
      rw [zsmul_eq_mul,
        show ((q : ℤ) : ZMod q) = 0 from by
          push_cast
          exact ZMod.natCast_self q,
        zero_mul]
    calc (q : ℤ) • (Submodule.Quotient.mk ω :
          (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
        = Submodule.Quotient.mk ((q : ℤ) • ω) :=
          (map_zsmul (Submodule.mkQ _) _ _).symm
      _ = Submodule.Quotient.mk (0 : G.E → ZMod q) := by rw [hω]
      _ = 0 := rfl

/-- **THE FINITE REDUCTION OF THE INTRINSIC CARRIER** (review #6,
finding 1): the resolution-`q` residue is exactly the integral
carrier's quotient by `q` — `H¹(G;ℤ) ⧸ q·H¹(G;ℤ) ≃ H¹(G;ZMod q)`.
One integral carrier; its finite reductions. -/
noncomputable def h1ResQuotEquiv :
    (((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))
        ⧸ LinearMap.range ((q : ℤ) •
          (LinearMap.id :
            ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) →ₗ[ℤ]
              ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)))))
      ≃ₗ[ℤ] ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) :=
  (Submodule.quotEquivOfEq _ _ (G.ker_h1Res q).symm).trans
    ((G.h1Res q).quotKerEquivOfSurjective (G.h1Res_surjective q))

noncomputable instance :
    Fintype (((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))
        ⧸ LinearMap.range ((q : ℤ) •
          (LinearMap.id :
            ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) →ₗ[ℤ]
              ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))))) :=
  Fintype.ofEquiv _ (G.h1ResQuotEquiv q).toEquiv.symm

instance :
    Nonempty (((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))
        ⧸ LinearMap.range ((q : ℤ) •
          (LinearMap.id :
            ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) →ₗ[ℤ]
              ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))))) :=
  ⟨0⟩

/-- **The uniform complexity, through the reduction**: the integral
carrier's mod-`q` quotient carries `b₁ · log q` of complexity — the
incompressible content at resolution `q` is a statement about
`H¹(G;ℤ) ⧸ q·H¹(G;ℤ)`. -/
theorem uniformAction_h1ResQuot_complexity :
    (uniformAction (((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))
        ⧸ LinearMap.range ((q : ℤ) •
          (LinearMap.id :
            ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) →ₗ[ℤ]
              ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)))))).complexity
      = G.b1 * Real.log q := by
  rw [uniformAction_complexity, ← Nat.card_eq_fintype_card,
    Nat.card_congr (G.h1ResQuotEquiv q).toEquiv, G.card_quotient_eq q]
  push_cast [Real.log_pow]
  ring

/-- **K2 through the intrinsic carrier's reduction** (review #6,
finding 1): description complexity splits as gauge complexity plus
the complexity of the integral carrier's mod-`q` reduction. Gravity,
matter, time, and uncertainty share one carrier — the sector lattice
`H¹(G;ℤ)` with its harmonic action (`classSectorAction`) — and the
information face is priced on that carrier's finite reductions. -/
theorem uniformComplexity_split_carrier :
    (uniformAction (G.E → ZMod q)).complexity
      = (uniformAction ↥(LinearMap.range (G.gradLin (ZMod q)))).complexity
        + (uniformAction (((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))
            ⧸ LinearMap.range ((q : ℤ) •
              (LinearMap.id :
                ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) →ₗ[ℤ]
                  ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)))))).complexity := by
  rw [G.uniformComplexity_split q, G.uniformAction_quotient_complexity q,
    G.uniformAction_h1ResQuot_complexity q]


/-! ## Gravity and time on the carrier's reduction (review #7)

`H1Reduction G q` **names** the finite reduction of the intrinsic
carrier; `carrierCompression` is the map that reads a resolution-`q`
description as a finite sector of the carrier. K3 is extracted as an
**equivalence** of every compression fiber with the gauge group
(`carrierFiberEquivGauge`), `gravity_complexity` is **applied** to the
self-pullback of `carrierCompression` (`carrier_gravity_complexity` —
pairs of descriptions representing the same finite sector), and the
gauge-fixing cost transports (`sectionCost_carrierCompression`). With
the intrinsic Gibbs fluctuation
(`classSectorAction_gibbsVariance_nonneg`,
`Meno/BasisIndependence.lean`), all four faces now consume the one
carrier. -/

/-- **The finite reduction of the intrinsic carrier, named**:
`H¹(G;ℤ) ⧸ q·H¹(G;ℤ)`. -/
abbrev H1Reduction (q : ℕ) [NeZero q] : Type v :=
  ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))
    ⧸ LinearMap.range ((q : ℤ) •
      (LinearMap.id :
        ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) →ₗ[ℤ]
          ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))))

/-- `H¹(G;ℤ) ⧸ q·H¹(G;ℤ)` is `q`-torsion. -/
theorem h1Reduction_nsmul_eq_zero (ξ : H1Reduction G q) : q • ξ = 0 := by
  obtain ⟨κ, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  have h : (q : ℤ) • (Submodule.Quotient.mk κ : H1Reduction G q)
      = Submodule.Quotient.mk ((q : ℤ) • κ) :=
    (map_zsmul (Submodule.mkQ _) _ _).symm
  have hz : (Submodule.Quotient.mk ((q : ℤ) • κ) : H1Reduction G q) = 0 := by
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨κ, rfl⟩
  calc q • (Submodule.Quotient.mk κ : H1Reduction G q)
      = (q : ℤ) • (Submodule.Quotient.mk κ : H1Reduction G q) :=
        (natCast_zsmul _ _).symm
    _ = 0 := h.trans hz

/-- **The reduction is a `ZMod q`-module** (review #8): the canonical
scalar structure on the `q`-torsion quotient. -/
noncomputable instance : Module (ZMod q) (H1Reduction G q) :=
  AddCommGroup.zmodModule (G.h1Reduction_nsmul_eq_zero q)

/-- The finite reduction, as a **`ZMod q`-linear** equivalence with
the resolution quotient (review #8 — the `ℤ`-linear `h1ResQuotEquiv`,
upgraded; `ZMod q`-linearity of an additive map between `ZMod q`
modules is automatic). -/
noncomputable def h1ResQuotEquivZMod :
    H1Reduction G q ≃ₗ[ZMod q]
      ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) :=
  { toFun := G.h1ResQuotEquiv q
    invFun := (G.h1ResQuotEquiv q).symm
    left_inv := (G.h1ResQuotEquiv q).left_inv
    right_inv := (G.h1ResQuotEquiv q).right_inv
    map_add' := map_add _
    map_smul' := ZMod.map_smul (G.h1ResQuotEquiv q).toLinearMap.toAddMonoidHom }

/-- **The reduction's rank-`b₁` basis** (review #8): the standard
basis of `(ZMod q)^{b₁}`, pulled back along the keystone at the
fundamental basis. -/
noncomputable def h1ReductionBasis :
    Module.Basis (Fin G.b1) (ZMod q) (H1Reduction G q) :=
  (Pi.basisFun (ZMod q) (Fin G.b1)).map
    ((G.h1ResQuotEquivZMod q).trans
      (G.latticeQuotEquivQ G.cycleBasis q)).symm

/-- **Reading a description as a finite sector of the carrier** — a
`ZMod q`-linear map (review #8): the class map followed by the
reduction identification. -/
noncomputable def carrierCompression :
    (G.E → ZMod q) →ₗ[ZMod q] H1Reduction G q :=
  (G.h1ResQuotEquivZMod q).symm.toLinearMap
    ∘ₗ Submodule.mkQ (LinearMap.range (G.gradLin (ZMod q)))

theorem carrierCompression_apply (ω : G.E → ZMod q) :
    G.carrierCompression q ω
      = (G.h1ResQuotEquivZMod q).symm (Submodule.Quotient.mk ω) := rfl

theorem carrierCompression_surjective :
    Function.Surjective (G.carrierCompression q) := fun ξ => by
  obtain ⟨ω, hω⟩ := Submodule.Quotient.mk_surjective _
    ((G.h1ResQuotEquivZMod q) ξ)
  exact ⟨ω, by
    rw [carrierCompression_apply, hω, LinearEquiv.symm_apply_apply]⟩

/-- **The kernel of the carrier reading is the gauge group** — the
linear-algebra form of K3 (review #8): fibers are cosets of this
kernel. -/
theorem ker_carrierCompression :
    LinearMap.ker (G.carrierCompression q)
      = LinearMap.range (G.gradLin (ZMod q)) := by
  ext ω
  rw [LinearMap.mem_ker, carrierCompression_apply]
  constructor
  · intro h
    have h0 : (Submodule.Quotient.mk ω :
        (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) = 0 := by
      have := congrArg (G.h1ResQuotEquivZMod q) h
      rwa [LinearEquiv.apply_symm_apply, map_zero] at this
    rwa [Submodule.Quotient.mk_eq_zero] at h0
  · intro h
    rw [show (Submodule.Quotient.mk ω :
        (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr h, map_zero]

/-- **K3, extracted as an equivalence** (review #7): every fiber of
the mod-`q` class map is the gauge group — the one fiber-to-kernel
equivalence (review #9) at the `Quotient.out` representative, with the
kernel read off by `Submodule.ker_mkQ`. -/
noncomputable def compressionFiberEquivGauge
    (x : (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) :
    {y : G.E → ZMod q // (Submodule.Quotient.mk y :
        (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) = x}
      ≃ ↥(LinearMap.range (G.gradLin (ZMod q))) :=
  (fiberEquivKer (Submodule.mkQ (LinearMap.range (G.gradLin (ZMod q))))
      (Quotient.out x) (Quotient.out_eq x)).trans
    (Equiv.subtypeEquivRight fun ω => by rw [Submodule.ker_mkQ])

/-- **Every `carrierCompression` fiber is the gauge group, by
kernel/cosets** (review #8): the one fiber-to-kernel equivalence
(review #9) at a chosen preimage, with the kernel identified by
`ker_carrierCompression`. -/
noncomputable def carrierFiberEquivGauge (ξ : H1Reduction G q) :
    SGD.Fiber (G.carrierCompression q) ξ
      ≃ ↥(LinearMap.range (G.gradLin (ZMod q))) :=
  (fiberEquivKer (G.carrierCompression q)
      (G.carrierCompression_surjective q ξ).choose
      (G.carrierCompression_surjective q ξ).choose_spec).trans
    (Equiv.subtypeEquivRight fun ω => by rw [G.ker_carrierCompression q])

theorem card_H1Reduction : Nat.card (H1Reduction G q) = q ^ G.b1 := by
  rw [Nat.card_congr (G.h1ResQuotEquiv q).toEquiv, G.card_quotient_eq q]

noncomputable instance : DecidableEq (H1Reduction G q) := Classical.decEq _

instance : Nonempty (SGD.Pullback (G.carrierCompression q)
    (G.carrierCompression q)) :=
  ⟨⟨(0, 0), rfl⟩⟩

/-- **GRAVITY ON THE CARRIER** (review #7): `gravity_complexity`
applied to the self-pullback of `carrierCompression` — pairs of
descriptions representing the **same finite sector of the intrinsic
carrier**, with the base the carrier's reduction. Sharing the sector
is worth exactly one copy of its complexity. -/
theorem carrier_gravity_complexity :
    (uniformAction (SGD.Pullback (G.carrierCompression q)
        (G.carrierCompression q))).complexity
      + (uniformAction (H1Reduction G q)).complexity
      = (uniformAction (G.E → ZMod q)).complexity
        + (uniformAction (G.E → ZMod q)).complexity :=
  gravity_complexity (G.carrierCompression q) (G.carrierCompression q)
    (G.carrierFiberEquivGauge q) (G.carrierFiberEquivGauge q)

/-- **The time face on the carrier, by transport** (review #8): the
gauge-fixing cost of `carrierCompression` is the gauge-fixing cost of
the class map — `sectionCost` is invariant under codomain relabeling
(`sectionCost_comp_equiv`), and the relabeling is `h1ResQuotEquivZMod`.
No fiber sum is recomputed. -/
theorem sectionCost_carrierCompression :
    sectionCost (G.carrierCompression q)
      = (q : ℝ) ^ G.b1
        * Real.log (Nat.card ↥(LinearMap.range (G.gradLin (ZMod q)))) := by
  have h := sectionCost_comp_equiv
    (fun y : G.E → ZMod q => (Submodule.Quotient.mk y :
      (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))))
    (G.h1ResQuotEquivZMod q).symm.toEquiv
  rw [show (⇑(G.carrierCompression q) : (G.E → ZMod q) → H1Reduction G q)
      = fun y => (G.h1ResQuotEquivZMod q).symm.toEquiv
        (Submodule.Quotient.mk y) from rfl,
    h, G.sectionCost_compression G.cycleBasis q]

/-! ## The Gibbs distribution through the reduction (review #9)

Gravity and time previously consumed only the carrier's underlying
quotient, through `uniformAction` — whose energy is identically zero.
Here the **intrinsic Gibbs distribution** of `classSectorAction`
(`Meno/BasisIndependence.lean`) is pushed through
`H¹(G;ℤ) → H1Reduction G q`:

* `residueMass` — the residue distribution: the total Gibbs mass of
  the integral classes over each finite sector. Positive
  (`residueMass_pos`), normalized (`residueMass_sum`), and computed by
  every basis chart (`residueMass_chart` — basis independence).
* `descriptionMass` — the uniform gauge lift through
  `carrierCompression`; `descriptionEntropy_split` is
  `H(description) = H(residue) + log |gauge|`.
* `pairDist` — the shared-pair **coupling** on the self-pullback
  (review #10): normalized (`pairMass_sum`), with **both marginals
  the description distribution** (`pairDist_fst`, `pairDist_snd`),
  and the pushforward of the description distribution recovering the
  residue distribution (`descriptionDist_map`) — all through the
  `FinDist` abstraction of `Meno/InfoRatchet.lean`.
* **`carrier_gravity_entropy`** — the four-term gravity identity
  `H(pair) + H(residue) = H(description) + H(description)`: the
  generic `FinDist.entropy_gravity`, instantiated at the Gibbs
  residue distribution. The same generic theorem instantiated at the
  uniform distribution gives
  `carrier_gravity_complexity_of_entropy` — a genuine specialization
  (review #10); the SGD-bridge proof of `carrier_gravity_complexity`
  stands as independent corroboration.
* `sectionCost_carrierCompression_div` — the time face: the
  per-sector gauge-fixing cost is the conditional entropy
  `H(description) − H(residue) = log |gauge|`. -/

/-- **The residue distribution** (review #9): the total intrinsic
Gibbs mass of the integral classes reducing to a given finite sector
of the carrier. -/
noncomputable def residueMass (ξ : H1Reduction G q) : ℝ :=
  ∑' κ : {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) //
      (Submodule.Quotient.mk κ : H1Reduction G q) = ξ},
    (G.classSectorAction).gibbsMass κ.val

theorem summable_residue (ξ : H1Reduction G q) :
    Summable (fun κ : {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) //
        (Submodule.Quotient.mk κ : H1Reduction G q) = ξ} =>
      (G.classSectorAction).gibbsMass κ.val) :=
  (G.classSectorAction).summable_gibbsMass.subtype _

/-- **Positivity**: every finite sector carries residue mass — its
fiber is nonempty and every Gibbs mass is positive. -/
theorem residueMass_pos (ξ : H1Reduction G q) : 0 < G.residueMass q ξ := by
  obtain ⟨κ₀, hκ₀⟩ := Submodule.Quotient.mk_surjective _ ξ
  exact (G.summable_residue q ξ).tsum_pos
    (fun κ => (G.classSectorAction).gibbsMass_nonneg κ.val)
    ⟨κ₀, hκ₀⟩ ((G.classSectorAction).gibbsMass_pos κ₀)

/-- **Normalization**: the residue distribution is a probability on
the finite reduction — the fibers partition `H¹(G;ℤ)` and the Gibbs
distribution sums to one. -/
theorem residueMass_sum :
    ∑ ξ : H1Reduction G q, G.residueMass q ξ = 1 := by
  have hsum : Summable (fun κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) =>
      (G.classSectorAction).gibbsMass κ) :=
    (G.classSectorAction).summable_gibbsMass
  have hσ := (Equiv.summable_iff (Equiv.sigmaFiberEquiv
    (fun κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) =>
      (Submodule.Quotient.mk κ : H1Reduction G q)))).mpr hsum
  calc ∑ ξ : H1Reduction G q, G.residueMass q ξ
      = ∑' ξ : H1Reduction G q, G.residueMass q ξ := (tsum_fintype _).symm
    _ = ∑' σ : Σ ξ : H1Reduction G q,
          {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) //
            (Submodule.Quotient.mk κ : H1Reduction G q) = ξ},
          (G.classSectorAction).gibbsMass σ.2.val := hσ.tsum_sigma.symm
    _ = ∑' κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ),
          (G.classSectorAction).gibbsMass κ :=
        Equiv.tsum_eq (Equiv.sigmaFiberEquiv _) _
    _ = 1 := (G.classSectorAction).tsum_gibbsMass_eq_one

/-- **Basis independence** (review #9): every lattice basis computes
the residue distribution — the `B`-coordinate Boltzmann sum over the
coset of coordinates reducing to `ξ`, divided by the graph's partition
function. The statement's left side never mentions a basis. -/
theorem residueMass_chart {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) (ξ : H1Reduction G q) :
    G.residueMass q ξ
      = (∑' k : {k : Fin n → ℤ //
            (Submodule.Quotient.mk ((G.latticeQuotEquiv B).symm k)
              : H1Reduction G q) = ξ},
          Real.exp (-(G.basisGramData B).energy k.val)) / G.partFn := by
  have h1 : ∀ κ : {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) //
      (Submodule.Quotient.mk κ : H1Reduction G q) = ξ},
      (G.classSectorAction).gibbsMass κ.val
        = Real.exp (-(G.harmonicEnergy κ.val)) / G.partFn := by
    intro κ
    show (G.classSectorAction).weight κ.val / (G.classSectorAction).partFn = _
    rw [G.classSectorAction_partFn]
    rfl
  rw [residueMass, tsum_congr h1, tsum_div_const]
  congr 1
  rw [← Equiv.tsum_eq (Equiv.subtypeEquiv
      ((G.latticeQuotEquiv B).toEquiv.symm) (fun k => Iff.rfl))
    (fun κ : {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) //
        (Submodule.Quotient.mk κ : H1Reduction G q) = ξ} =>
      Real.exp (-(G.harmonicEnergy κ.val)))]
  refine tsum_congr fun k => ?_
  congr 1
  rw [neg_inj]
  have h := G.basisGramData_energy_latticeQuot B
    ((G.latticeQuotEquiv B).symm k.val)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- **The residue distribution, bundled** (review #10): nonnegativity
and normalization carried by the structure, not asserted at use
sites. -/
noncomputable def residueDist : FinDist (H1Reduction G q) where
  mass := G.residueMass q
  nonneg ξ := (G.residueMass_pos q ξ).le
  sum_one := G.residueMass_sum q

@[simp] theorem residueDist_mass :
    (G.residueDist q).mass = G.residueMass q := rfl

theorem card_carrierCompression_fiber (ξ : H1Reduction G q) :
    Nat.card {ω : G.E → ZMod q // G.carrierCompression q ω = ξ}
      = Nat.card ↥(LinearMap.range (G.gradLin (ZMod q))) :=
  Nat.card_congr (G.carrierFiberEquivGauge q ξ)

/-- **The description distribution, bundled first** (review #11): the
uniform gauge lift of the residue distribution through
`carrierCompression` — normalization and nonnegativity come from the
`FinDist` structure, never recomputed. -/
noncomputable def descriptionDist : FinDist (G.E → ZMod q) :=
  (G.residueDist q).uniformLift (G.carrierCompression q)
    Nat.card_pos (G.card_carrierCompression_fiber q)

/-- **The description mass — the distribution's mass projection**
(review #11): each finite sector's residue mass divided evenly across
its gauge fiber. -/
noncomputable def descriptionMass : (G.E → ZMod q) → ℝ :=
  (G.descriptionDist q).mass

@[simp] theorem descriptionDist_mass :
    (G.descriptionDist q).mass = G.descriptionMass q := rfl

theorem descriptionMass_pos (ω : G.E → ZMod q) :
    0 < G.descriptionMass q ω := by
  show 0 < G.residueMass q (G.carrierCompression q ω)
    / (Nat.card ↥(LinearMap.range (G.gradLin (ZMod q))) : ℝ)
  exact div_pos (G.residueMass_pos q _) (by exact_mod_cast Nat.card_pos)

/-- Normalization — from the bundled distribution, not recomputed
(review #11). -/
theorem descriptionMass_sum :
    ∑ ω : G.E → ZMod q, G.descriptionMass q ω = 1 :=
  (G.descriptionDist q).sum_one

/-- **The lift pushforward law, on the carrier** (review #10): pushing
the description distribution forward through `carrierCompression`
recovers the residue distribution — `descriptionMass` genuinely
disintegrates `residueMass` over the gauge fibers. -/
theorem descriptionDist_map :
    (G.descriptionDist q).map (G.carrierCompression q) = G.residueDist q :=
  FinDist.map_uniformLift (G.carrierCompression q) Nat.card_pos
    (G.card_carrierCompression_fiber q) (G.residueDist q)

/-- **H(description) = H(residue) + log |gauge|** (review #9): the
entropy chain rule at the uniform gauge lift — a description prices a
finite sector of the carrier plus one free gauge choice. -/
theorem descriptionEntropy_split :
    shannonEntropy (G.descriptionMass q)
      = shannonEntropy (G.residueMass q)
        + Real.log (Nat.card ↥(LinearMap.range (G.gradLin (ZMod q)))) :=
  FinDist.entropy_uniformLift (G.carrierCompression q) Nat.card_pos
    (G.card_carrierCompression_fiber q) (G.residueDist q)

/-- **The shared-pair coupling, bundled** (review #10): the
shared-base coupling of two description lifts over the residue
distribution — a genuine coupling, by construction: it is nonnegative
and normalized (the `FinDist` structure), and **both marginals are
the description distribution** (`pairDist_fst`, `pairDist_snd`). -/
noncomputable def pairDist :
    FinDist (SGD.Pullback (G.carrierCompression q)
      (G.carrierCompression q)) :=
  (G.residueDist q).coupling (G.carrierCompression q)
    (G.carrierCompression q) Nat.card_pos Nat.card_pos
    (G.card_carrierCompression_fiber q) (G.card_carrierCompression_fiber q)

/-- The shared-pair mass — the coupling's mass function: each residue
mass split evenly across the `|gauge|²` pairs above it. -/
noncomputable def pairMass
    (p : SGD.Pullback (G.carrierCompression q) (G.carrierCompression q)) :
    ℝ :=
  (G.pairDist q).mass p

theorem pairMass_nonneg
    (p : SGD.Pullback (G.carrierCompression q) (G.carrierCompression q)) :
    0 ≤ G.pairMass q p :=
  (G.pairDist q).nonneg p

/-- **Normalization** (review #10): the shared-pair masses sum to
one. -/
theorem pairMass_sum :
    ∑ p : SGD.Pullback (G.carrierCompression q) (G.carrierCompression q),
      G.pairMass q p = 1 :=
  (G.pairDist q).sum_one

/-- **The first marginal is the description distribution**
(review #10). -/
theorem pairDist_fst :
    (G.pairDist q).map (fun p => p.val.1) = G.descriptionDist q :=
  FinDist.coupling_fst (G.carrierCompression q) (G.carrierCompression q)
    Nat.card_pos Nat.card_pos
    (G.card_carrierCompression_fiber q) (G.card_carrierCompression_fiber q)
    (G.residueDist q)

/-- **The second marginal is the description distribution**
(review #10). -/
theorem pairDist_snd :
    (G.pairDist q).map (fun p => p.val.2) = G.descriptionDist q :=
  FinDist.coupling_snd (G.carrierCompression q) (G.carrierCompression q)
    Nat.card_pos Nat.card_pos
    (G.card_carrierCompression_fiber q) (G.card_carrierCompression_fiber q)
    (G.residueDist q)

/-- The pair entropy splits as residue entropy plus two gauge logs —
Phase 45's identity, now a corollary of the coupling chain rule. -/
theorem pairEntropy_split :
    shannonEntropy (G.pairMass q)
      = shannonEntropy (G.residueMass q)
        + 2 * Real.log
            (Nat.card ↥(LinearMap.range (G.gradLin (ZMod q)))) := by
  have hg : ((Nat.card ↥(LinearMap.range (G.gradLin (ZMod q)))) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos).ne'
  have h := FinDist.entropy_coupling (G.carrierCompression q)
    (G.carrierCompression q) Nat.card_pos Nat.card_pos
    (G.card_carrierCompression_fiber q) (G.card_carrierCompression_fiber q)
    (G.residueDist q)
  rw [Nat.cast_mul, Real.log_mul hg hg] at h
  show (G.pairDist q).entropy
    = shannonEntropy (G.residueMass q) + 2 * Real.log _
  refine h.trans ?_
  show shannonEntropy (G.residueMass q) + (Real.log _ + Real.log _)
    = shannonEntropy (G.residueMass q) + 2 * Real.log _
  ring

/-- **GRAVITY ON THE CARRIER — the four-term identity** (review #10):
sharing one finite sector of the intrinsic carrier saves exactly one
copy of the residue entropy against two independent descriptions —

    H(pair) + H(residue) = H(description) + H(description)

— the generic entropy gravity identity (`FinDist.entropy_gravity`),
instantiated at the Gibbs residue distribution of the carrier. -/
theorem carrier_gravity_entropy :
    shannonEntropy (G.pairMass q) + shannonEntropy (G.residueMass q)
      = shannonEntropy (G.descriptionMass q)
        + shannonEntropy (G.descriptionMass q) :=
  FinDist.entropy_gravity (G.carrierCompression q) (G.carrierCompression q)
    Nat.card_pos Nat.card_pos
    (G.card_carrierCompression_fiber q) (G.card_carrierCompression_fiber q)
    (G.residueDist q)

/-- **The uniform identity is a genuine specialization** (review #10):
the SAME generic entropy gravity identity, instantiated at the uniform
distribution — the coupling and lift of the uniform are uniform, the
entropies are log-cardinalities, and the identity reads
`K(pullback) + K(base) = K(descriptions) + K(descriptions)`.
(`carrier_gravity_complexity`, the SGD-bridge derivation, stands as
the independent corroboration.) -/
theorem carrier_gravity_complexity_of_entropy :
    (uniformAction (SGD.Pullback (G.carrierCompression q)
        (G.carrierCompression q))).complexity
      + (uniformAction (H1Reduction G q)).complexity
      = (uniformAction (G.E → ZMod q)).complexity
        + (uniformAction (G.E → ZMod q)).complexity := by
  have h := FinDist.entropy_gravity (G.carrierCompression q)
    (G.carrierCompression q) Nat.card_pos Nat.card_pos
    (G.card_carrierCompression_fiber q) (G.card_carrierCompression_fiber q)
    (FinDist.uniform (H1Reduction G q))
  rw [FinDist.coupling_uniform (G.carrierCompression q)
      (G.carrierCompression q) Nat.card_pos Nat.card_pos
      (G.card_carrierCompression_fiber q)
      (G.card_carrierCompression_fiber q),
    FinDist.uniformLift_uniform (G.carrierCompression q) Nat.card_pos
      (G.card_carrierCompression_fiber q),
    FinDist.entropy_uniform, FinDist.entropy_uniform,
    FinDist.entropy_uniform] at h
  simp only [uniformAction_complexity]
  exact h

/-! ### The uniform entropy defect: pricing meets counting (review #11)

The Gibbs-priced and uniform-counting gravity identities were two
instances of one generic theorem; the **defect** `Δ = log|X| − H(P)`
is their numerical bridge. Because lifting and coupling preserve the
defect (`FinDist.defect_uniformLift`, `FinDist.defect_coupling`), the
*same* action-induced information deficit separates every uniform
complexity from its Gibbs entropy:

    K_uniform(residue)     = H(residue)     + Δ
    K_uniform(description) = H(description) + Δ
    K_uniform(pair)        = H(pair)        + Δ

— the uniform gravity identity is the Gibbs entropy gravity plus the
same deficit on both sides. -/

/-- **The action-induced information deficit** (review #11): how far
the Gibbs residue distribution sits below maximal ignorance on the
finite reduction. Nonnegative (`FinDist.defect_nonneg`); zero exactly
when the Gibbs law is uniform (`FinDist.defect_eq_zero_iff`). -/
noncomputable def residueDefect : ℝ := (G.residueDist q).defect

/-- `K_uniform(residue) = H(residue) + Δ`. -/
theorem uniformComplexity_residue_split :
    (uniformAction (H1Reduction G q)).complexity
      = shannonEntropy (G.residueMass q) + G.residueDefect q := by
  rw [uniformAction_complexity]
  show _ = shannonEntropy (G.residueMass q)
    + (Real.log (Fintype.card (H1Reduction G q))
        - shannonEntropy (G.residueMass q))
  ring

/-- `K_uniform(description) = H(description) + Δ` — **the same Δ**:
the uniform gauge lift preserves the deficit (review #11). -/
theorem uniformComplexity_description_split :
    (uniformAction (G.E → ZMod q)).complexity
      = shannonEntropy (G.descriptionMass q) + G.residueDefect q := by
  have h := FinDist.defect_uniformLift (G.carrierCompression q)
    Nat.card_pos (G.card_carrierCompression_fiber q) (G.residueDist q)
  rw [uniformAction_complexity]
  have h2 : Real.log (Fintype.card (G.E → ZMod q))
      = (G.descriptionDist q).entropy + (G.descriptionDist q).defect := by
    show _ = _ + (Real.log (Fintype.card (G.E → ZMod q))
      - (G.descriptionDist q).entropy)
    ring
  rw [h2]
  exact congrArg₂ (· + ·) rfl h

/-- `K_uniform(pair) = H(pair) + Δ` — **the same Δ**: the shared-base
coupling preserves the deficit (review #11). Together with the
previous two, the uniform gravity identity equals the Gibbs entropy
gravity identity plus the same action-induced deficit on both
sides — pricing and counting are two decompositions of one
quantity. -/
theorem uniformComplexity_pair_split :
    (uniformAction (SGD.Pullback (G.carrierCompression q)
        (G.carrierCompression q))).complexity
      = shannonEntropy (G.pairMass q) + G.residueDefect q := by
  have h := FinDist.defect_coupling (G.carrierCompression q)
    (G.carrierCompression q) Nat.card_pos Nat.card_pos
    (G.card_carrierCompression_fiber q) (G.card_carrierCompression_fiber q)
    (G.residueDist q)
  rw [uniformAction_complexity]
  have h2 : Real.log (Fintype.card (SGD.Pullback (G.carrierCompression q)
      (G.carrierCompression q)))
      = (G.pairDist q).entropy + (G.pairDist q).defect := by
    show _ = _ + (Real.log (Fintype.card (SGD.Pullback
        (G.carrierCompression q) (G.carrierCompression q)))
      - (G.pairDist q).entropy)
    ring
  rw [h2]
  exact congrArg₂ (· + ·) rfl h

/-- **The time face, as conditional entropy** (review #9): the
per-sector gauge-fixing cost of `carrierCompression` is exactly the
entropy gap `H(description) − H(residue) = log |gauge|`. -/
theorem sectionCost_carrierCompression_div :
    sectionCost (G.carrierCompression q) / Nat.card (H1Reduction G q)
      = shannonEntropy (G.descriptionMass q)
        - shannonEntropy (G.residueMass q) := by
  rw [G.sectionCost_carrierCompression q, G.descriptionEntropy_split q]
  have hD : ((Nat.card (H1Reduction G q) : ℕ) : ℝ) = (q : ℝ) ^ G.b1 := by
    rw [G.card_H1Reduction q]
    push_cast
    ring
  rw [hD]
  have hq : ((q : ℝ)) ^ G.b1 ≠ 0 := by
    have : (0 : ℝ) < q := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    positivity
  field_simp
  ring

end IncidenceGraph


end Meno
