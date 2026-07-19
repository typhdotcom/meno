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

noncomputable instance h1ReductionFintype :
    Fintype (((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))
        ⧸ LinearMap.range ((q : ℤ) •
          (LinearMap.id :
            ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) →ₗ[ℤ]
              ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))))) :=
  Fintype.ofEquiv _ (G.h1ResQuotEquiv q).toEquiv.symm

instance h1ReductionNonempty :
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
the intrinsic Gibbs fluctuation — unconditional and strict for the
energy observable, the moments being theorems
(`classSectorAction_gibbsVariance_energy_nonneg`,
`classSectorAction_gibbsVariance_energy_pos`,
`Meno/BasisIndependence.lean`, review #14) — all four faces now
consume the one carrier. -/

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

noncomputable instance h1ReductionDecEq : DecidableEq (H1Reduction G q) :=
  Classical.decEq _

instance carrierPullbackNonempty :
    Nonempty (SGD.Pullback (G.carrierCompression q)
      (G.carrierCompression q)) :=
  ⟨⟨(0, 0), rfl⟩⟩

noncomputable instance carrierPullbackFintype :
    Fintype (SGD.Pullback (G.carrierCompression q)
      (G.carrierCompression q)) :=
  inferInstance

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
  `H(pair) + H(residue) = H(description) + H(description)`: since
  review #14 a **corollary of the priced calculus**
  (`SectorAction.entropy_gravity` at the residue action), with the
  uniform complexity identity the priced identity plus the common
  deficit (`carrier_gravity_complexity_of_entropy`); the SGD-bridge
  proof of `carrier_gravity_complexity` stands as independent
  corroboration. Both live at the end of the priced section.
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

/-! ### The zero class is strictly modal (review #12)

The residue distribution is not merely positive and normalized — the
quadratic action **concentrates** it: the zero class carries strictly
more mass than every other class. In a lattice chart the fiber over a
class is a coset `k₀ + q·ℤⁿ`, its Boltzmann sum is the Gaussian
periodization of the harmonic Gram at the fractional shift `k₀/q`
(`residueMass_mk_eq_periodization`), and a nonzero class forces a
non-integer coordinate of the shift — where the strict modal bound of
the shifted Fourier expansion applies
(`periodization_lt_periodization_zero`, `Meno/SiegelPoisson.lean`). -/

/-- The residue mass of a charted class is the Gaussian periodization
of the scaled harmonic Gram at the fractional shift of any integer
representative, over the graph's partition function. -/
private lemma residueMass_mk_eq_periodization {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) (k₀ : Fin n → ℤ) :
    G.residueMass q
        (Submodule.Quotient.mk ((G.latticeQuotEquiv B).symm k₀))
      = periodization
          ((((q : ℕ) : ℝ) ^ 2 / Real.pi) • (gramOf (G.cyclesR B))⁻¹)
          (fun i => (k₀ i : ℝ) / ((q : ℕ) : ℝ)) / G.partFn := by
  classical
  rw [G.residueMass_chart q B]
  congr 1
  -- membership of the coset translates
  have hmem : ∀ c : Fin n → ℤ,
      (Submodule.Quotient.mk
          ((G.latticeQuotEquiv B).symm (k₀ + (q : ℤ) • c))
        : H1Reduction G q)
        = Submodule.Quotient.mk ((G.latticeQuotEquiv B).symm k₀) := by
    intro c
    rw [Submodule.Quotient.eq]
    refine LinearMap.mem_range.mpr ⟨(G.latticeQuotEquiv B).symm c, ?_⟩
    rw [LinearMap.smul_apply, LinearMap.id_apply, map_add, map_smul]
    abel
  -- the coset reindex `c ↦ k₀ + q·c` is a bijection onto the fiber
  have hbij : Function.Bijective (fun c : Fin n → ℤ =>
      (⟨k₀ + (q : ℤ) • c, hmem c⟩ : {k : Fin n → ℤ //
        (Submodule.Quotient.mk ((G.latticeQuotEquiv B).symm k)
          : H1Reduction G q)
          = Submodule.Quotient.mk ((G.latticeQuotEquiv B).symm k₀)})) := by
    constructor
    · intro c c' hcc'
      have h2 : (q : ℤ) • c = (q : ℤ) • c' :=
        add_left_cancel (congrArg Subtype.val hcc')
      exact smul_right_injective _
        (by exact_mod_cast (NeZero.ne q) : (q : ℤ) ≠ 0) h2
    · rintro ⟨k, hk⟩
      rw [Submodule.Quotient.eq] at hk
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hk
      rw [LinearMap.smul_apply, LinearMap.id_apply] at hy
      refine ⟨G.latticeQuotEquiv B y, ?_⟩
      apply Subtype.ext
      show k₀ + (q : ℤ) • (G.latticeQuotEquiv B) y = k
      have h3 := congrArg (G.latticeQuotEquiv B) hy
      rw [map_smul, map_sub, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply] at h3
      rw [h3]
      abel
  rw [← Equiv.tsum_eq (Equiv.ofBijective _ hbij)]
  simp only [periodization]
  refine tsum_congr fun c => ?_
  set A : Matrix (Fin n) (Fin n) ℝ := (gramOf (G.cyclesR B))⁻¹ with hA
  set y : Fin n → ℝ :=
    (fun i => (k₀ i : ℝ) / ((q : ℕ) : ℝ)) + fun i => (c i : ℝ) with hy
  have hqR : ((q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hvec : (fun i => (((k₀ + (q : ℤ) • c) i : ℤ) : ℝ))
      = ((q : ℕ) : ℝ) • y := by
    funext i
    show (((k₀ + (q : ℤ) • c) i : ℤ) : ℝ)
      = ((q : ℕ) : ℝ) * ((k₀ i : ℝ) / ((q : ℕ) : ℝ) + (c i : ℝ))
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp
  have henergy : (G.basisGramData B).energy
        ((Equiv.ofBijective _ hbij c).val)
      = (((q : ℕ) : ℝ) • y) ⬝ᵥ A.mulVec (((q : ℕ) : ℝ) • y) := by
    have h1 : (G.basisGramData B).energy (k₀ + (q : ℤ) • c)
        = (fun i => (((k₀ + (q : ℤ) • c) i : ℤ) : ℝ)) ⬝ᵥ
            A.mulVec (fun i => (((k₀ + (q : ℤ) • c) i : ℤ) : ℝ)) := by
      show ∑ i, ∑ j, A i j * (((k₀ + (q : ℤ) • c) i : ℤ) : ℝ)
          * (((k₀ + (q : ℤ) • c) j : ℤ) : ℝ) = _
      exact quadForm_dotProduct A _
    rw [show (Equiv.ofBijective _ hbij c).val = k₀ + (q : ℤ) • c from rfl,
      h1, hvec]
  show Real.exp (-(G.basisGramData B).energy ((Equiv.ofBijective _ hbij c).val))
    = gaussian ((((q : ℕ) : ℝ) ^ 2 / Real.pi) • A)
        ((fun i => (k₀ i : ℝ) / ((q : ℕ) : ℝ)) + fun i => (c i : ℝ))
  rw [henergy]
  show Real.exp (-((((q : ℕ) : ℝ) • y) ⬝ᵥ A.mulVec (((q : ℕ) : ℝ) • y)))
    = Real.exp (-Real.pi
        * (y ⬝ᵥ (((((q : ℕ) : ℝ) ^ 2 / Real.pi) • A).mulVec y)))
  congr 1
  rw [smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul,
    Matrix.smul_mulVec, dotProduct_smul]
  simp only [smul_eq_mul]
  field_simp

/-- **The zero class is strictly modal** (review #12): every nonzero
finite sector carries strictly less residue mass than the zero
sector — the quadratic action genuinely concentrates the residue
distribution. -/
theorem residueMass_lt_residueMass_zero {ξ : H1Reduction G q}
    (hξ : ξ ≠ 0) : G.residueMass q ξ < G.residueMass q 0 := by
  classical
  obtain ⟨κ₀, hκ₀⟩ := Submodule.Quotient.mk_surjective _ ξ
  set k₀ : Fin G.b1 → ℤ := G.latticeQuotEquiv G.cycleBasis κ₀ with hk₀
  have hmkξ : (Submodule.Quotient.mk
      ((G.latticeQuotEquiv G.cycleBasis).symm k₀) : H1Reduction G q) = ξ := by
    rw [hk₀, LinearEquiv.symm_apply_apply, hκ₀]
  -- a nonzero class has a representative coordinate `q` does not divide
  have hcoord : ∃ i, ¬ ((q : ℤ) ∣ k₀ i) := by
    by_contra hall
    push_neg at hall
    apply hξ
    choose f hf using fun i => hall i
    have hk : k₀ = (q : ℤ) • f := funext fun i => by
      rw [Pi.smul_apply, smul_eq_mul]; exact hf i
    rw [← hmkξ, hk, map_smul, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range.mpr
      ⟨(G.latticeQuotEquiv G.cycleBasis).symm f, by
        rw [LinearMap.smul_apply, LinearMap.id_apply]⟩
  obtain ⟨i₀, hi₀⟩ := hcoord
  have hq0 : (0 : ℝ) < ((q : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  set A : Matrix (Fin G.b1) (Fin G.b1) ℝ :=
    (gramOf (G.cyclesR G.cycleBasis))⁻¹ with hA
  have hApos : A.PosDef := posDef_inv (G.gramOf_cyclesR_posDef G.cycleBasis)
  have hMq : ((((q : ℕ) : ℝ) ^ 2 / Real.pi) • A).PosDef :=
    posDef_smul' hApos (div_pos (pow_pos hq0 2) Real.pi_pos)
  -- both masses, as periodizations
  have hmass0 : G.residueMass q 0
      = periodization ((((q : ℕ) : ℝ) ^ 2 / Real.pi) • A) 0 / G.partFn := by
    have h := G.residueMass_mk_eq_periodization q G.cycleBasis 0
    rw [map_zero] at h
    rw [show (Submodule.Quotient.mk (0 : (G.E → ℤ) ⧸
        LinearMap.range (G.gradLin ℤ)) : H1Reduction G q) = 0 from rfl] at h
    simp only [Pi.zero_apply, Int.cast_zero, zero_div] at h
    exact h
  have hmassξ : G.residueMass q ξ
      = periodization ((((q : ℕ) : ℝ) ^ 2 / Real.pi) • A)
          (fun i => (k₀ i : ℝ) / ((q : ℕ) : ℝ)) / G.partFn := by
    have h := G.residueMass_mk_eq_periodization q G.cycleBasis k₀
    rw [hmkξ] at h
    exact h
  -- the fractional shift misses the integers at `i₀`
  have hx : ∀ z : ℤ, (fun i => (k₀ i : ℝ) / ((q : ℕ) : ℝ)) i₀ ≠ (z : ℝ) := by
    intro z hz
    apply hi₀
    refine ⟨z, ?_⟩
    have h1 : (k₀ i₀ : ℝ) = (z : ℝ) * ((q : ℕ) : ℝ) :=
      (div_eq_iff (ne_of_gt hq0)).mp hz
    exact_mod_cast h1.trans (mul_comm _ _)
  -- the graph's partition function is positive
  have hZ : 0 < G.partFn := by
    have h := (G.classSectorAction).partFn_pos
    rwa [G.classSectorAction_partFn] at h
  rw [hmassξ, hmass0]
  exact (div_lt_div_iff_of_pos_right hZ).mpr
    (periodization_lt_periodization_zero hMq hx)

/-- **The residue distribution, bundled** (review #10): nonnegativity
and normalization carried by the structure, not asserted at use
sites. -/
noncomputable def residueDist : FinDist (H1Reduction G q) where
  mass := G.residueMass q
  nonneg ξ := (G.residueMass_pos q ξ).le
  sum_one := G.residueMass_sum q

@[simp] theorem residueDist_mass :
    (G.residueDist q).mass = G.residueMass q := rfl

/-- **The residue distribution is genuinely non-uniform** (review #12):
on any graph with cycles, at any resolution `1 < q`, the quadratic
action concentrates residue mass on the zero class — the Gibbs law is
never the counting law. -/
theorem residueDist_ne_uniform (hb : 0 < G.b1) (hq : 1 < q) :
    G.residueDist q ≠ FinDist.uniform (H1Reduction G q) := by
  intro h
  have hcard : 1 < Nat.card (H1Reduction G q) := by
    rw [G.card_H1Reduction q]
    exact Nat.one_lt_pow hb.ne' hq
  haveI : Nontrivial (H1Reduction G q) :=
    Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : H1Reduction G q)
  have hlt := G.residueMass_lt_residueMass_zero q hξ
  have hmass := congrArg FinDist.mass h
  have hξ0 : G.residueMass q ξ = G.residueMass q 0 := by
    have h1 := congrFun hmass ξ
    have h2 := congrFun hmass 0
    rw [residueDist_mass] at h1 h2
    rw [h1, h2]
    rfl
  exact absurd hξ0 (ne_of_lt hlt)

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

/-- **The deficit is strictly positive** (review #12): on any graph
with cycles, at any resolution `1 < q`, the quadratic action genuinely
changes finite-resolution information — the maximum-entropy bound is
never attained, because the Gibbs residue law concentrates on the zero
class (`residueDist_ne_uniform`, through the strict modal bound of the
shifted Gaussian Fourier expansion). -/
theorem residueDefect_pos (hb : 0 < G.b1) (hq : 1 < q) :
    0 < G.residueDefect q := by
  refine lt_of_le_of_ne (FinDist.defect_nonneg _) fun h => ?_
  exact G.residueDist_ne_uniform q hb hq
    ((FinDist.defect_eq_zero_iff _).mp h.symm)

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

/-! ### The residue action: coarse-graining the harmonic action (reviews #12, #13)

The `K_uniform = H + Δ` splits above become a genuine *pricing* bridge
once the residue distribution is exhibited as the Gibbs law of an
action — and the action itself must be the **coarse-graining of the
harmonic action**, not a reconstruction from the normalized masses
(review #13). The **unnormalized coset weight**
`W ξ = ∑_{κ mod q = ξ} exp(−harmonicEnergy κ)` (`residueWeight`)
satisfies `residueMass ξ = W ξ / Z` (`residueMass_eq_residueWeight_div`);
the **residue action** is `classSectorAction.coarseGrain` at the
quotient map, so its energy is the effective free-energy difference
`F ξ − F 0` with `F = −log W` (`residueAction_E_freeEnergy`), the
partition function factorizes as `Z = W 0 · Z_residue`
(`classPartFn_eq_residueWeight_mul`), and the complexity decomposes
(`classComplexity_residue_split`). Its Gibbs mass **is** the residue
distribution (`residueAction_gibbsMass`), the Gibbs entropy split
gives `H(residue) = K + ⟨E⟩` (`residueAction_entropy_split`), and the
uniform complexity decomposes as
`K_uniform = K(residueAction) + ⟨E⟩ + Δ`
(`uniformComplexity_residue_bridge`) — complexity `log Z` and expected
energy on one side, maximal ignorance on the other, the deficit
between them. -/

/-- The residue mass is maximal at the zero class — the weak form of
the strict modal bound. -/
theorem residueMass_le_residueMass_zero (ξ : H1Reduction G q) :
    G.residueMass q ξ ≤ G.residueMass q 0 := by
  by_cases hξ : ξ = 0
  · rw [hξ]
  · exact (G.residueMass_lt_residueMass_zero q hξ).le

/-- **The unnormalized coset weight** (review #13):
`W ξ = ∑_{κ mod q = ξ} exp(−harmonicEnergy κ)` — the harmonic
action's coarse weight at the quotient map onto the finite
reduction. -/
noncomputable def residueWeight (ξ : H1Reduction G q) : ℝ :=
  (G.classSectorAction).coarseWeight
    (fun κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) =>
      (Submodule.Quotient.mk κ : H1Reduction G q)) ξ

/-- Every coset weight is positive — the fiber is nonempty. -/
theorem residueWeight_pos (ξ : H1Reduction G q) :
    0 < G.residueWeight q ξ := by
  obtain ⟨κ₀, hκ₀⟩ := Submodule.Quotient.mk_surjective _ ξ
  exact SectorAction.coarseWeight_pos (G.classSectorAction) ⟨κ₀, hκ₀⟩

/-- **The residue mass is the coset weight over the partition
function** (review #13): the normalized masses of `residueMass` are
the coarse Boltzmann weights of the harmonic action, divided by its
partition function. -/
theorem residueMass_eq_residueWeight_div (ξ : H1Reduction G q) :
    G.residueMass q ξ
      = G.residueWeight q ξ / (G.classSectorAction).partFn := by
  show (∑' κ : {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) //
      (Submodule.Quotient.mk κ : H1Reduction G q) = ξ},
    (G.classSectorAction).weight κ.val / (G.classSectorAction).partFn) = _
  rw [tsum_div_const]
  rfl

/-- The zero coset is modal at the weight level. -/
theorem residueWeight_le_residueWeight_zero (ξ : H1Reduction G q) :
    G.residueWeight q ξ ≤ G.residueWeight q 0 := by
  have hZ : (0 : ℝ) < (G.classSectorAction).partFn :=
    (G.classSectorAction).partFn_pos
  have h := G.residueMass_le_residueMass_zero q ξ
  rw [G.residueMass_eq_residueWeight_div q ξ,
    G.residueMass_eq_residueWeight_div q 0] at h
  have h2 := mul_le_mul_of_nonneg_right h hZ.le
  rwa [div_mul_cancel₀ _ hZ.ne', div_mul_cancel₀ _ hZ.ne'] at h2

/-- **The residue action** (reviews #12, #13): the coarse-graining of
the harmonic action at the quotient map onto the finite reduction —
the generic `SectorAction.coarseGrain`, with the zero class as the
modal ground state. Its energy is the coset free-energy difference,
its partition function divides the harmonic one, and its Gibbs mass
is the residue distribution. -/
noncomputable def residueAction : SectorAction.{v} :=
  (G.classSectorAction).coarseGrain
    (fun κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) =>
      (Submodule.Quotient.mk κ : H1Reduction G q)) 0
    (G.residueWeight_pos q) (G.residueWeight_le_residueWeight_zero q)

noncomputable instance : Fintype (G.residueAction q).Λ :=
  inferInstanceAs (Fintype (H1Reduction G q))

noncomputable instance : DecidableEq (G.residueAction q).Λ :=
  inferInstanceAs (DecidableEq (H1Reduction G q))

/-- The residue action's energy, in terms of the normalized masses —
the partition function cancels out of the weight ratio (the retired
definition of review #12, now a theorem). -/
theorem residueAction_E (ξ : H1Reduction G q) :
    (G.residueAction q).E ξ
      = Real.log (G.residueMass q 0) - Real.log (G.residueMass q ξ) := by
  have hZ : (0 : ℝ) < (G.classSectorAction).partFn :=
    (G.classSectorAction).partFn_pos
  show Real.log (G.residueWeight q 0) - Real.log (G.residueWeight q ξ) = _
  rw [G.residueMass_eq_residueWeight_div q 0,
    G.residueMass_eq_residueWeight_div q ξ,
    Real.log_div (G.residueWeight_pos q 0).ne' hZ.ne',
    Real.log_div (G.residueWeight_pos q ξ).ne' hZ.ne']
  ring

/-- **The effective free energy of a finite sector** (review #13):
`F ξ = −log W ξ`. -/
noncomputable def residueFreeEnergy (ξ : H1Reduction G q) : ℝ :=
  -Real.log (G.residueWeight q ξ)

/-- **The residue energy is the free-energy difference**
(review #13): `E ξ = F ξ − F 0`. -/
theorem residueAction_E_freeEnergy (ξ : H1Reduction G q) :
    (G.residueAction q).E ξ
      = G.residueFreeEnergy q ξ - G.residueFreeEnergy q 0 := by
  show Real.log (G.residueWeight q 0) - Real.log (G.residueWeight q ξ)
    = -Real.log (G.residueWeight q ξ) - -Real.log (G.residueWeight q 0)
  ring

/-- **The harmonic partition function factorizes through the residue
action** (review #13): `Z = W 0 · Z_residue`. -/
theorem classPartFn_eq_residueWeight_mul :
    (G.classSectorAction).partFn
      = G.residueWeight q 0 * (G.residueAction q).partFn :=
  SectorAction.partFn_eq_coarseWeight_mul (G.classSectorAction) _ 0
    (G.residueWeight_pos q) (G.residueWeight_le_residueWeight_zero q)

/-- **The harmonic complexity decomposes through the residue action**
(review #13): `log Z = log W 0 + K(residueAction)`. -/
theorem classComplexity_residue_split :
    (G.classSectorAction).complexity
      = Real.log (G.residueWeight q 0) + (G.residueAction q).complexity :=
  SectorAction.complexity_eq_coarseGrain (G.classSectorAction) _ 0
    (G.residueWeight_pos q) (G.residueWeight_le_residueWeight_zero q)

/-- The residue action's Boltzmann weight is the mass ratio against
the modal class. -/
theorem residueAction_weight (ξ : H1Reduction G q) :
    (G.residueAction q).weight ξ
      = G.residueMass q ξ / G.residueMass q 0 := by
  show Real.exp (-(G.residueAction q).E ξ) = _
  rw [G.residueAction_E q ξ, neg_sub, Real.exp_sub,
    Real.exp_log (G.residueMass_pos q ξ),
    Real.exp_log (G.residueMass_pos q 0)]

/-- The residue action's partition function is the reciprocal modal
mass. -/
theorem residueAction_partFn :
    (G.residueAction q).partFn = (G.residueMass q 0)⁻¹ := by
  show (∑' ξ : H1Reduction G q, (G.residueAction q).weight ξ) = _
  rw [tsum_fintype, Finset.sum_congr rfl fun ξ _ => G.residueAction_weight q ξ,
    ← Finset.sum_div, G.residueMass_sum q, one_div]

/-- **The residue action's Gibbs mass is the residue distribution**
(review #12): the normalization cancels, leaving exactly the coset
Boltzmann masses. -/
theorem residueAction_gibbsMass :
    (G.residueAction q).gibbsMass = G.residueMass q := by
  funext ξ
  show (G.residueAction q).weight ξ / (G.residueAction q).partFn
    = G.residueMass q ξ
  rw [G.residueAction_weight q ξ, G.residueAction_partFn q]
  have h0 : G.residueMass q 0 ≠ 0 := ne_of_gt (G.residueMass_pos q 0)
  field_simp

/-- The residue action's complexity, in closed form: `-log` of the
modal mass. -/
theorem residueAction_complexity :
    (G.residueAction q).complexity = -Real.log (G.residueMass q 0) := by
  show Real.log (G.residueAction q).partFn = _
  rw [G.residueAction_partFn q, Real.log_inv]

/-- **`H(residue) = K(residueAction) + ⟨E⟩`** (review #12): the Gibbs
entropy split of `Meno/InfoRatchet.lean`, instantiated at the residue
action — the residue entropy *is* complexity plus expected energy. -/
theorem residueAction_entropy_split :
    shannonEntropy (G.residueMass q)
      = (G.residueAction q).complexity
        + (G.residueAction q).gibbsExpect (G.residueAction q).E := by
  have h := @SectorAction.entropy_gibbs (G.residueAction q)
    (inferInstanceAs (Fintype (H1Reduction G q)))
  rw [G.residueAction_gibbsMass q] at h
  exact h

/-- **THE PRICING–COUNTING BRIDGE** (review #12): uniform complexity
on the finite reduction is the residue action's complexity plus its
expected energy plus the deficit —

    K_uniform = K(residueAction) + ⟨E_residue⟩ + Δ

— the harmonic action's pricing (`log Z` and expected energy) on one
side, maximal ignorance on the other, and the strictly positive
deficit (`residueDefect_pos`) between them. -/
theorem uniformComplexity_residue_bridge :
    (uniformAction (H1Reduction G q)).complexity
      = (G.residueAction q).complexity
        + (G.residueAction q).gibbsExpect (G.residueAction q).E
        + G.residueDefect q := by
  rw [G.uniformComplexity_residue_split q, G.residueAction_entropy_split q]

/-- The residue action's Gibbs distribution, bundled: it **is** the
residue distribution (review #13). -/
theorem residueAction_gibbsDist :
    (G.residueAction q).gibbsDist = G.residueDist q := by
  refine @FinDist.ext (H1Reduction G q) _ _ _ ?_
  funext ξ
  show (G.residueAction q).gibbsMass ξ = (G.residueDist q).mass ξ
  rw [G.residueAction_gibbsMass q]
  rfl

/-! #### The strict theorems of the residue action (review #13)

The strict modal bound is fully cashed at the action level: energy is
zero exactly on the ground class and strictly positive exactly off
it; on any graph with cycles at any resolution `1 < q`, the residue
complexity and the expected energy are strictly positive, so the
pricing–counting bridge decomposes the uniform complexity into
**three strictly positive terms**. -/

/-- **Energy vanishes exactly at the zero class** (review #13). -/
theorem residueAction_E_eq_zero_iff (ξ : H1Reduction G q) :
    (G.residueAction q).E ξ = 0 ↔ ξ = 0 := by
  constructor
  · intro h
    by_contra hξ
    have hlt := G.residueMass_lt_residueMass_zero q hξ
    have hlog := Real.log_lt_log (G.residueMass_pos q ξ) hlt
    rw [G.residueAction_E q ξ] at h
    linarith
  · rintro rfl
    rw [G.residueAction_E q 0]
    exact sub_self _

/-- **Energy is strictly positive exactly off the zero class**
(review #13). -/
theorem residueAction_E_pos_iff (ξ : H1Reduction G q) :
    0 < (G.residueAction q).E ξ ↔ ξ ≠ 0 := by
  constructor
  · intro h hξ0
    exact absurd ((G.residueAction_E_eq_zero_iff q ξ).mpr hξ0) (ne_of_gt h)
  · intro hξ
    exact lt_of_le_of_ne ((G.residueAction q).E_nonneg ξ)
      (fun heq => hξ ((G.residueAction_E_eq_zero_iff q ξ).mp heq.symm))

/-- The modal mass is strictly below one on any graph with cycles at
any resolution `1 < q` — some other class carries positive mass. -/
theorem residueMass_zero_lt_one (hb : 0 < G.b1) (hq : 1 < q) :
    G.residueMass q 0 < 1 := by
  classical
  have hcard : 1 < Nat.card (H1Reduction G q) := by
    rw [G.card_H1Reduction q]
    exact Nat.one_lt_pow hb.ne' hq
  haveI : Nontrivial (H1Reduction G q) :=
    Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : H1Reduction G q)
  have hsub : G.residueMass q 0 + G.residueMass q ξ
      ≤ ∑ η : H1Reduction G q, G.residueMass q η := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({0, ξ} : Finset (H1Reduction G q)))
      (fun η _ _ => (G.residueMass_pos q η).le)
    rwa [Finset.sum_pair (Ne.symm hξ)] at h
  rw [G.residueMass_sum q] at hsub
  have hpos := G.residueMass_pos q ξ
  linarith

/-- **The residue complexity is strictly positive** (review #13):
`K(residueAction) = −log(residueMass 0) > 0`. -/
theorem residueAction_complexity_pos (hb : 0 < G.b1) (hq : 1 < q) :
    0 < (G.residueAction q).complexity := by
  rw [G.residueAction_complexity q]
  have h1 := G.residueMass_pos q 0
  have h2 := G.residueMass_zero_lt_one q hb hq
  have h3 := Real.log_neg h1 h2
  linarith

/-- **The expected residue energy is strictly positive**
(review #13): some class off the ground state carries positive Gibbs
mass at positive energy. -/
theorem residueAction_gibbsExpect_E_pos (hb : 0 < G.b1) (hq : 1 < q) :
    0 < (G.residueAction q).gibbsExpect (G.residueAction q).E := by
  classical
  have hcard : 1 < Nat.card (H1Reduction G q) := by
    rw [G.card_H1Reduction q]
    exact Nat.one_lt_pow hb.ne' hq
  haveI : Nontrivial (H1Reduction G q) :=
    Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : H1Reduction G q)
  show 0 < ∑' η : H1Reduction G q,
    (G.residueAction q).E η * (G.residueAction q).gibbsMass η
  rw [tsum_fintype]
  refine Finset.sum_pos'
    (fun η _ => mul_nonneg ((G.residueAction q).E_nonneg η)
      ((G.residueAction q).gibbsMass_nonneg η))
    ⟨ξ, Finset.mem_univ ξ, ?_⟩
  exact mul_pos ((G.residueAction_E_pos_iff q ξ).mpr hξ)
    ((G.residueAction q).gibbsMass_pos ξ)

/-- **THE BRIDGE, IN THREE STRICTLY POSITIVE TERMS** (review #13): on
any graph with cycles, at any resolution `1 < q`, the uniform
complexity decomposes as `K_uniform = K(residueAction) + ⟨E⟩ + Δ`
with every summand strictly positive — pricing genuinely carries
complexity, energy, and deficit, none of them degenerate. -/
theorem uniformComplexity_residue_bridge_pos (hb : 0 < G.b1) (hq : 1 < q) :
    (uniformAction (H1Reduction G q)).complexity
        = (G.residueAction q).complexity
          + (G.residueAction q).gibbsExpect (G.residueAction q).E
          + G.residueDefect q
      ∧ 0 < (G.residueAction q).complexity
      ∧ 0 < (G.residueAction q).gibbsExpect (G.residueAction q).E
      ∧ 0 < G.residueDefect q :=
  ⟨G.uniformComplexity_residue_bridge q,
    G.residueAction_complexity_pos q hb hq,
    G.residueAction_gibbsExpect_E_pos q hb hq,
    G.residueDefect_pos q hb hq⟩

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

/-! ### Priced gravity and time (review #13)

Descriptions and pairs were `FinDist` constructions — gravity and
time were measured by entropy but not priced by any action. Here they
become actions themselves: the **description action** is the priced
uniform lift of the residue action through `carrierCompression`, the
**pair action** its priced shared-base self-coupling. Their Gibbs
distributions are exactly the bundled distributions above
(`descriptionAction_gibbsDist`, `pairAction_gibbsDist`), expected
energy and variance transport untouched
(`descriptionAction_gibbsExpect_E`, …), **gravity holds at the level
of partition functions and complexities** (`carrier_gravity_partFn`,
`carrier_gravity_action`), the time face is the complexity difference
`K(description) − K(residue)`
(`sectionCost_carrierCompression_action`), and the pricing–counting
bridge extends to descriptions and pairs
(`uniformComplexity_description_bridge`,
`uniformComplexity_pair_bridge`). -/

/-- **The description action** (review #13): the priced uniform lift
of the residue action through the carrier compression — each
description prices as its finite sector, the gauge choice is free. -/
noncomputable def descriptionAction : SectorAction.{v} :=
  (G.residueAction q).uniformLift (G.carrierCompression q)
    Nat.card_pos (G.card_carrierCompression_fiber q)

noncomputable instance : Fintype (G.descriptionAction q).Λ :=
  inferInstanceAs (Fintype (G.E → ZMod q))

/-- **The pair action** (review #13): the priced shared-base coupling
of two description lifts over the residue action. -/
noncomputable def pairAction : SectorAction.{v} :=
  (G.residueAction q).coupling (G.carrierCompression q)
    (G.carrierCompression q) Nat.card_pos Nat.card_pos
    (G.card_carrierCompression_fiber q) (G.card_carrierCompression_fiber q)

noncomputable instance : Fintype (G.pairAction q).Λ :=
  inferInstanceAs
    (Fintype (SGD.Pullback (G.carrierCompression q) (G.carrierCompression q)))

/-- The description action's Gibbs mass is the description mass
(review #13). -/
theorem descriptionAction_gibbsMass :
    (G.descriptionAction q).gibbsMass = G.descriptionMass q := by
  funext ω
  have h : (G.descriptionAction q).gibbsMass ω
      = (G.residueAction q).gibbsMass (G.carrierCompression q ω)
        / (Nat.card ↥(LinearMap.range (G.gradLin (ZMod q))) : ℝ) :=
    SectorAction.uniformLift_gibbsMass (G.residueAction q)
      (G.carrierCompression q) Nat.card_pos
      (G.card_carrierCompression_fiber q) ω
  rw [h, G.residueAction_gibbsMass q]
  rfl

/-- **The description action's Gibbs distribution is the description
distribution** (review #13): the priced lift's Gibbs law is the
`FinDist` uniform lift of the residue distribution. -/
theorem descriptionAction_gibbsDist :
    (G.descriptionAction q).gibbsDist = G.descriptionDist q := by
  have h := SectorAction.uniformLift_gibbsDist (G.residueAction q)
    (G.carrierCompression q) Nat.card_pos (G.card_carrierCompression_fiber q)
  rw [G.residueAction_gibbsDist q] at h
  exact h

/-- The pair action's Gibbs mass is the shared-pair mass
(review #13). -/
theorem pairAction_gibbsMass :
    (G.pairAction q).gibbsMass = G.pairMass q := by
  funext p
  have h : (G.pairAction q).gibbsMass p
      = (G.residueAction q).gibbsMass (SGD.Pullback.base p)
        / ((Nat.card ↥(LinearMap.range (G.gradLin (ZMod q)))
            * Nat.card ↥(LinearMap.range (G.gradLin (ZMod q))) : ℕ) : ℝ) :=
    SectorAction.coupling_gibbsMass (G.residueAction q)
      (G.carrierCompression q) (G.carrierCompression q)
      Nat.card_pos Nat.card_pos (G.card_carrierCompression_fiber q)
      (G.card_carrierCompression_fiber q) p
  rw [h, G.residueAction_gibbsMass q]
  rfl

/-- **The pair action's Gibbs distribution is the shared-pair
coupling** (review #13): the priced coupling's Gibbs law is the
`FinDist` shared-base coupling of the residue distribution. -/
theorem pairAction_gibbsDist :
    (G.pairAction q).gibbsDist = G.pairDist q := by
  have h := SectorAction.coupling_gibbsDist (G.residueAction q)
    (G.carrierCompression q) (G.carrierCompression q)
    Nat.card_pos Nat.card_pos (G.card_carrierCompression_fiber q)
    (G.card_carrierCompression_fiber q)
  rw [G.residueAction_gibbsDist q] at h
  exact h

/-- `K(description) = K(residue) + log |gauge|` (review #13) — the
complexity chain rule at the priced lift. -/
theorem descriptionAction_complexity :
    (G.descriptionAction q).complexity
      = (G.residueAction q).complexity
        + Real.log (Nat.card ↥(LinearMap.range (G.gradLin (ZMod q)))) := by
  have h := SectorAction.uniformLift_complexity (G.residueAction q)
    (G.carrierCompression q) Nat.card_pos (G.card_carrierCompression_fiber q)
  exact h.trans (add_comm _ _)

/-- `K(pair) = K(residue) + 2·log |gauge|` (review #13). -/
theorem pairAction_complexity :
    (G.pairAction q).complexity
      = (G.residueAction q).complexity
        + 2 * Real.log (Nat.card ↥(LinearMap.range (G.gradLin (ZMod q)))) := by
  have h : (G.pairAction q).complexity
      = Real.log (Nat.card ↥(LinearMap.range (G.gradLin (ZMod q))))
        + Real.log (Nat.card ↥(LinearMap.range (G.gradLin (ZMod q))))
        + (G.residueAction q).complexity :=
    SectorAction.coupling_complexity (G.residueAction q)
      (G.carrierCompression q) (G.carrierCompression q)
      Nat.card_pos Nat.card_pos (G.card_carrierCompression_fiber q)
      (G.card_carrierCompression_fiber q)
  rw [h]
  ring

/-- **GRAVITY, PRICED — partition functions** (review #13): sharing
one finite sector multiplies out —
`Z(pair) · Z(residue) = Z(description) · Z(description)`. -/
theorem carrier_gravity_partFn :
    (G.pairAction q).partFn * (G.residueAction q).partFn
      = (G.descriptionAction q).partFn * (G.descriptionAction q).partFn :=
  SectorAction.partFn_gravity (G.residueAction q)
    (G.carrierCompression q) (G.carrierCompression q)
    Nat.card_pos Nat.card_pos (G.card_carrierCompression_fiber q)
    (G.card_carrierCompression_fiber q)

/-- **GRAVITY, PRICED — complexities** (review #13): the four-term
gravity identity at the level of `log Z`:
`K(pair) + K(residue) = K(description) + K(description)`. -/
theorem carrier_gravity_action :
    (G.pairAction q).complexity + (G.residueAction q).complexity
      = (G.descriptionAction q).complexity
        + (G.descriptionAction q).complexity :=
  SectorAction.complexity_gravity (G.residueAction q)
    (G.carrierCompression q) (G.carrierCompression q)
    Nat.card_pos Nat.card_pos (G.card_carrierCompression_fiber q)
    (G.card_carrierCompression_fiber q)

/-- **TIME, PRICED** (reviews #13, #14): the per-sector gauge-fixing
cost is the complexity difference of the priced actions —
`sectionCost / |sectors| = K(descriptionAction) − K(residueAction)` —
a **direct specialization** of the generic priced time law
(`SectorAction.sectionCost_uniformLift`), not a rewrite of the
entropy identity. -/
theorem sectionCost_carrierCompression_action :
    sectionCost (G.carrierCompression q) / Nat.card (H1Reduction G q)
      = (G.descriptionAction q).complexity
        - (G.residueAction q).complexity := by
  have h := SectorAction.sectionCost_uniformLift (G.residueAction q)
    (G.carrierCompression q) Nat.card_pos (G.card_carrierCompression_fiber q)
  rw [Nat.card_eq_fintype_card]
  exact h

/-- The description action's expected energy is the residue action's
(review #13): the free gauge choice carries no energy. -/
theorem descriptionAction_gibbsExpect_E :
    (G.descriptionAction q).gibbsExpect (G.descriptionAction q).E
      = (G.residueAction q).gibbsExpect (G.residueAction q).E :=
  SectorAction.uniformLift_gibbsExpect_E (G.residueAction q)
    (G.carrierCompression q) Nat.card_pos (G.card_carrierCompression_fiber q)

/-- The description action's energy variance is the residue action's
(review #13). -/
theorem descriptionAction_gibbsVariance_E :
    (G.descriptionAction q).gibbsVariance (G.descriptionAction q).E
      = (G.residueAction q).gibbsVariance (G.residueAction q).E :=
  SectorAction.uniformLift_gibbsVariance_E (G.residueAction q)
    (G.carrierCompression q) Nat.card_pos (G.card_carrierCompression_fiber q)

/-- The pair action's expected energy is the residue action's
(review #13). -/
theorem pairAction_gibbsExpect_E :
    (G.pairAction q).gibbsExpect (G.pairAction q).E
      = (G.residueAction q).gibbsExpect (G.residueAction q).E :=
  SectorAction.coupling_gibbsExpect_E (G.residueAction q)
    (G.carrierCompression q) (G.carrierCompression q)
    Nat.card_pos Nat.card_pos (G.card_carrierCompression_fiber q)
    (G.card_carrierCompression_fiber q)

/-- The pair action's energy variance is the residue action's
(review #13). -/
theorem pairAction_gibbsVariance_E :
    (G.pairAction q).gibbsVariance (G.pairAction q).E
      = (G.residueAction q).gibbsVariance (G.residueAction q).E :=
  SectorAction.coupling_gibbsVariance_E (G.residueAction q)
    (G.carrierCompression q) (G.carrierCompression q)
    Nat.card_pos Nat.card_pos (G.card_carrierCompression_fiber q)
    (G.card_carrierCompression_fiber q)

/-- `H(description) = K(descriptionAction) + ⟨E⟩` (review #13): the
Gibbs entropy split at the description action. -/
theorem descriptionAction_entropy_split :
    shannonEntropy (G.descriptionMass q)
      = (G.descriptionAction q).complexity
        + (G.descriptionAction q).gibbsExpect (G.descriptionAction q).E := by
  have h := SectorAction.entropy_gibbs (G.descriptionAction q)
  rw [G.descriptionAction_gibbsMass q] at h
  exact h

/-- **THE BRIDGE, ON DESCRIPTIONS** (review #13):
`K_uniform(description) = K(descriptionAction) + ⟨E⟩ + Δ` — the same
deficit as on the residue. -/
theorem uniformComplexity_description_bridge :
    (uniformAction (G.E → ZMod q)).complexity
      = (G.descriptionAction q).complexity
        + (G.descriptionAction q).gibbsExpect (G.descriptionAction q).E
        + G.residueDefect q := by
  rw [G.uniformComplexity_description_split q,
    G.descriptionAction_entropy_split q]

/-- `H(pair) = K(pairAction) + ⟨E⟩` (review #13): the Gibbs entropy
split at the pair action. -/
theorem pairAction_entropy_split :
    shannonEntropy (G.pairMass q)
      = (G.pairAction q).complexity
        + (G.pairAction q).gibbsExpect (G.pairAction q).E := by
  have h := SectorAction.entropy_gibbs (G.pairAction q)
  rw [G.pairAction_gibbsMass q] at h
  exact h

/-- **THE BRIDGE, ON PAIRS** (review #13):
`K_uniform(pair) = K(pairAction) + ⟨E⟩ + Δ` — the same deficit on all
three levels: the uniform gravity identity is the priced gravity
identity plus the one action-induced deficit on both sides. -/
theorem uniformComplexity_pair_bridge :
    (uniformAction (SGD.Pullback (G.carrierCompression q)
        (G.carrierCompression q))).complexity
      = (G.pairAction q).complexity
        + (G.pairAction q).gibbsExpect (G.pairAction q).E
        + G.residueDefect q := by
  rw [G.uniformComplexity_pair_split q, G.pairAction_entropy_split q]

/-- **GRAVITY ON THE CARRIER — the four-term identity** (reviews #10,
#14): sharing one finite sector of the intrinsic carrier saves
exactly one copy of the residue entropy against two independent
descriptions — `H(pair) + H(residue) = 2·H(description)` — now a
**corollary of the priced calculus**: the priced entropy gravity
identity (`SectorAction.entropy_gravity`, derived from the four Gibbs
entropy splits, complexity gravity, and the expectation transports),
instantiated at the residue action. -/
theorem carrier_gravity_entropy :
    shannonEntropy (G.pairMass q) + shannonEntropy (G.residueMass q)
      = shannonEntropy (G.descriptionMass q)
        + shannonEntropy (G.descriptionMass q) := by
  have h : shannonEntropy (G.pairAction q).gibbsMass
        + shannonEntropy (G.residueAction q).gibbsMass
      = shannonEntropy (G.descriptionAction q).gibbsMass
        + shannonEntropy (G.descriptionAction q).gibbsMass :=
    SectorAction.entropy_gravity (G.residueAction q)
      (G.carrierCompression q) (G.carrierCompression q)
      Nat.card_pos Nat.card_pos (G.card_carrierCompression_fiber q)
      (G.card_carrierCompression_fiber q)
  rw [G.pairAction_gibbsMass q, G.residueAction_gibbsMass q,
    G.descriptionAction_gibbsMass q] at h
  exact h

/-- **The uniform identity: the priced identity plus the common
deficit** (review #14): adding `Δ` to every term of the priced
entropy gravity identity yields the uniform complexity identity —
counting is pricing plus one deficit, on both sides. (Review #10's
derivation — the same generic distribution theorem at the uniform
law — is superseded by this priced route; the SGD-bridge derivation
`carrier_gravity_complexity` stands as independent corroboration.) -/
theorem carrier_gravity_complexity_of_entropy :
    (uniformAction (SGD.Pullback (G.carrierCompression q)
        (G.carrierCompression q))).complexity
      + (uniformAction (H1Reduction G q)).complexity
      = (uniformAction (G.E → ZMod q)).complexity
        + (uniformAction (G.E → ZMod q)).complexity := by
  have h := G.carrier_gravity_entropy q
  have h1 := G.uniformComplexity_pair_split q
  have h2 := G.uniformComplexity_residue_split q
  have h3 := G.uniformComplexity_description_split q
  linarith

/-! #### Strict fluctuation and the strict bridges (review #14)

The strict modal bound reaches the gravity branch: the residue
action's energy variance is strictly positive on any graph with
cycles (`residueAction_gibbsVariance_E_pos` — the finite strict
Gibbs-fluctuation law at the witness pair `0`, `ξ ≠ 0`), transported
untouched to descriptions and pairs, and the description and pair
bridges decompose into three strictly positive terms exactly as the
residue bridge does. -/

/-- **The residue action's energy variance is strictly positive**
(review #14). -/
theorem residueAction_gibbsVariance_E_pos (hb : 0 < G.b1) (hq : 1 < q) :
    0 < (G.residueAction q).gibbsVariance (G.residueAction q).E := by
  classical
  have hcard : 1 < Nat.card (H1Reduction G q) := by
    rw [G.card_H1Reduction q]
    exact Nat.one_lt_pow hb.ne' hq
  haveI : Nontrivial (H1Reduction G q) :=
    Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : H1Reduction G q)
  refine SectorAction.gibbsVariance_pos_of_ne (G.residueAction q)
    (G.residueAction q).E (k := ξ) (l := (0 : H1Reduction G q)) ?_
  have h0 : (G.residueAction q).E (0 : H1Reduction G q) = 0 :=
    (G.residueAction_E_eq_zero_iff q 0).mpr rfl
  rw [h0]
  exact ne_of_gt ((G.residueAction_E_pos_iff q ξ).mpr hξ)

/-- The description action's energy variance is strictly positive
(review #14) — transported from the residue action. -/
theorem descriptionAction_gibbsVariance_E_pos (hb : 0 < G.b1)
    (hq : 1 < q) :
    0 < (G.descriptionAction q).gibbsVariance (G.descriptionAction q).E := by
  rw [G.descriptionAction_gibbsVariance_E q]
  exact G.residueAction_gibbsVariance_E_pos q hb hq

/-- The pair action's energy variance is strictly positive
(review #14) — transported from the residue action. -/
theorem pairAction_gibbsVariance_E_pos (hb : 0 < G.b1) (hq : 1 < q) :
    0 < (G.pairAction q).gibbsVariance (G.pairAction q).E := by
  rw [G.pairAction_gibbsVariance_E q]
  exact G.residueAction_gibbsVariance_E_pos q hb hq

/-- The description action's complexity is strictly positive: the
residue complexity plus a nonnegative gauge log. -/
theorem descriptionAction_complexity_pos (hb : 0 < G.b1) (hq : 1 < q) :
    0 < (G.descriptionAction q).complexity := by
  rw [G.descriptionAction_complexity q]
  have h1 := G.residueAction_complexity_pos q hb hq
  have h2 : (1 : ℝ) ≤ (Nat.card ↥(LinearMap.range (G.gradLin (ZMod q))) : ℝ) :=
    Nat.one_le_cast.mpr Nat.card_pos
  have h3 := Real.log_nonneg h2
  linarith

/-- The description action's expected energy is strictly positive
(review #14). -/
theorem descriptionAction_gibbsExpect_E_pos (hb : 0 < G.b1) (hq : 1 < q) :
    0 < (G.descriptionAction q).gibbsExpect (G.descriptionAction q).E := by
  rw [G.descriptionAction_gibbsExpect_E q]
  exact G.residueAction_gibbsExpect_E_pos q hb hq

/-- **THE BRIDGE ON DESCRIPTIONS, IN THREE STRICTLY POSITIVE TERMS**
(review #14). -/
theorem uniformComplexity_description_bridge_pos (hb : 0 < G.b1)
    (hq : 1 < q) :
    (uniformAction (G.E → ZMod q)).complexity
        = (G.descriptionAction q).complexity
          + (G.descriptionAction q).gibbsExpect (G.descriptionAction q).E
          + G.residueDefect q
      ∧ 0 < (G.descriptionAction q).complexity
      ∧ 0 < (G.descriptionAction q).gibbsExpect (G.descriptionAction q).E
      ∧ 0 < G.residueDefect q :=
  ⟨G.uniformComplexity_description_bridge q,
    G.descriptionAction_complexity_pos q hb hq,
    G.descriptionAction_gibbsExpect_E_pos q hb hq,
    G.residueDefect_pos q hb hq⟩

/-- The pair action's complexity is strictly positive. -/
theorem pairAction_complexity_pos (hb : 0 < G.b1) (hq : 1 < q) :
    0 < (G.pairAction q).complexity := by
  rw [G.pairAction_complexity q]
  have h1 := G.residueAction_complexity_pos q hb hq
  have h2 : (1 : ℝ) ≤ (Nat.card ↥(LinearMap.range (G.gradLin (ZMod q))) : ℝ) :=
    Nat.one_le_cast.mpr Nat.card_pos
  have h3 := Real.log_nonneg h2
  linarith

/-- The pair action's expected energy is strictly positive
(review #14). -/
theorem pairAction_gibbsExpect_E_pos (hb : 0 < G.b1) (hq : 1 < q) :
    0 < (G.pairAction q).gibbsExpect (G.pairAction q).E := by
  rw [G.pairAction_gibbsExpect_E q]
  exact G.residueAction_gibbsExpect_E_pos q hb hq

/-- **THE BRIDGE ON PAIRS, IN THREE STRICTLY POSITIVE TERMS**
(review #14). -/
theorem uniformComplexity_pair_bridge_pos (hb : 0 < G.b1) (hq : 1 < q) :
    (uniformAction (SGD.Pullback (G.carrierCompression q)
        (G.carrierCompression q))).complexity
        = (G.pairAction q).complexity
          + (G.pairAction q).gibbsExpect (G.pairAction q).E
          + G.residueDefect q
      ∧ 0 < (G.pairAction q).complexity
      ∧ 0 < (G.pairAction q).gibbsExpect (G.pairAction q).E
      ∧ 0 < G.residueDefect q :=
  ⟨G.uniformComplexity_pair_bridge q,
    G.pairAction_complexity_pos q hb hq,
    G.pairAction_gibbsExpect_E_pos q hb hq,
    G.residueDefect_pos q hb hq⟩

/-! ### The resolution tower (review #14)

Coarse-grainings at different resolutions are not disconnected
snapshots. For `q ∣ q'` the finer reduction maps canonically onto the
coarser (`h1TowerMap` — commuting with the projection from the
integral carrier, `h1TowerMap_mk`), residue weights, masses, and the
Gibbs distribution push forward along it (`residueWeight_tower`,
`residueMass_tower`, `residueDist_tower`), the coarse residue action
**is** the coarse-graining of the finer one (`residueAction_tower` —
the generic composition law `SectorAction.coarseGrain_comp`), and the
partition-function factorization is transitive
(`residueWeight_factor_trans`, `classPartFn_tower`). -/

section Tower

variable (q' : ℕ) [NeZero q']

omit [NeZero q] [NeZero q'] in
private lemma range_qsmul_le (hdvd : q ∣ q') :
    LinearMap.range ((q' : ℤ) •
        (LinearMap.id :
          ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) →ₗ[ℤ]
            ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))))
      ≤ LinearMap.range ((q : ℤ) •
        (LinearMap.id :
          ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) →ₗ[ℤ]
            ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)))) := by
  rintro x ⟨y, rfl⟩
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨(c : ℤ) • y, ?_⟩
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [smul_smul, show ((q : ℤ)) * (c : ℤ) = ((q' : ℤ)) from by
    exact_mod_cast hc.symm]

/-- **The canonical reduction between resolutions** (review #14): for
`q ∣ q'`, the finer reduction `H¹⧸q'H¹` maps onto the coarser
`H¹⧸qH¹` — the identity of the carrier, descended to the
quotients. -/
noncomputable def h1TowerMap (hdvd : q ∣ q') :
    H1Reduction G q' →ₗ[ℤ] H1Reduction G q :=
  Submodule.mapQ _ _ LinearMap.id (G.range_qsmul_le q q' hdvd)

/-- The tower map commutes with the reduction projections from the
integral carrier — the projections `h1Res` factors through
(`h1ResQuotEquiv`). -/
@[simp] theorem h1TowerMap_mk (hdvd : q ∣ q')
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :
    G.h1TowerMap q q' hdvd (Submodule.Quotient.mk κ)
      = (Submodule.Quotient.mk κ : H1Reduction G q) :=
  rfl

/-- **Residue weights push forward through the tower** (review #14):
the coarse coset weight is the sum of the finer coset weights over
the tower fiber. -/
theorem residueWeight_tower (hdvd : q ∣ q') (ξ : H1Reduction G q) :
    G.residueWeight q ξ
      = ∑' η : {η : H1Reduction G q' // G.h1TowerMap q q' hdvd η = ξ},
          G.residueWeight q' η.val :=
  SectorAction.coarseWeight_comp (G.classSectorAction)
    (fun κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) =>
      (Submodule.Quotient.mk κ : H1Reduction G q'))
    (⇑(G.h1TowerMap q q' hdvd)) ξ

/-- **Residue masses push forward through the tower** (review #14). -/
theorem residueMass_tower (hdvd : q ∣ q') (ξ : H1Reduction G q) :
    G.residueMass q ξ
      = ∑' η : {η : H1Reduction G q' // G.h1TowerMap q q' hdvd η = ξ},
          G.residueMass q' η.val := by
  rw [G.residueMass_eq_residueWeight_div q ξ,
    G.residueWeight_tower q q' hdvd ξ, ← tsum_div_const]
  exact tsum_congr fun η =>
    (G.residueMass_eq_residueWeight_div q' η.val).symm

/-- **The residue Gibbs distribution pushes forward through the
tower** (review #14): the coarser Gibbs law is the pushforward of the
finer one along the tower map. -/
theorem residueDist_tower (hdvd : q ∣ q') :
    (G.residueDist q').map (⇑(G.h1TowerMap q q' hdvd))
      = G.residueDist q := by
  refine FinDist.ext ?_
  funext ξ
  show (∑ η ∈ Finset.univ.filter
      (fun η : H1Reduction G q' => G.h1TowerMap q q' hdvd η = ξ),
    G.residueMass q' η) = G.residueMass q ξ
  rw [Finset.sum_subtype
      (p := fun η : H1Reduction G q' => G.h1TowerMap q q' hdvd η = ξ)
      (Finset.univ.filter
        (fun η : H1Reduction G q' => G.h1TowerMap q q' hdvd η = ξ))
      (fun η => by simp) (G.residueMass q'),
    G.residueMass_tower q q' hdvd ξ, tsum_fintype]

/-- The finer residue action's coarse weight along the tower map: the
coarse coset weight over the finer modal weight. -/
theorem residueAction_tower_weight (hdvd : q ∣ q') (ξ : H1Reduction G q) :
    (G.residueAction q').coarseWeight (⇑(G.h1TowerMap q q' hdvd)) ξ
      = G.residueWeight q ξ / G.residueWeight q' 0 :=
  SectorAction.coarseGrain_coarseWeight (G.classSectorAction)
    (fun κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) =>
      (Submodule.Quotient.mk κ : H1Reduction G q')) 0
    (G.residueWeight_pos q') (G.residueWeight_le_residueWeight_zero q')
    (⇑(G.h1TowerMap q q' hdvd)) ξ

theorem residueAction_tower_weight_pos (hdvd : q ∣ q')
    (ξ : H1Reduction G q) :
    0 < (G.residueAction q').coarseWeight (⇑(G.h1TowerMap q q' hdvd)) ξ := by
  rw [G.residueAction_tower_weight q q' hdvd ξ]
  exact div_pos (G.residueWeight_pos q ξ) (G.residueWeight_pos q' 0)

theorem residueAction_tower_weight_le (hdvd : q ∣ q')
    (ξ : H1Reduction G q) :
    (G.residueAction q').coarseWeight (⇑(G.h1TowerMap q q' hdvd)) ξ
      ≤ (G.residueAction q').coarseWeight (⇑(G.h1TowerMap q q' hdvd)) 0 := by
  rw [G.residueAction_tower_weight q q' hdvd ξ,
    G.residueAction_tower_weight q q' hdvd 0]
  gcongr
  · exact (G.residueWeight_pos q' 0).le
  · exact G.residueWeight_le_residueWeight_zero q ξ

/-- **THE TOWER IDENTIFICATION** (review #14): the coarse residue
action is the coarse-graining of the finer residue action along the
tower map — the resolutions form a coherent tower, by the generic
composition law of coarse-grainings. -/
theorem residueAction_tower (hdvd : q ∣ q') :
    (G.residueAction q').coarseGrain (⇑(G.h1TowerMap q q' hdvd)) 0
        (G.residueAction_tower_weight_pos q q' hdvd)
        (G.residueAction_tower_weight_le q q' hdvd)
      = G.residueAction q :=
  SectorAction.coarseGrain_comp (G.classSectorAction)
    (fun κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) =>
      (Submodule.Quotient.mk κ : H1Reduction G q'))
    (⇑(G.h1TowerMap q q' hdvd)) 0 0
    (G.residueWeight_pos q') (G.residueWeight_le_residueWeight_zero q')
    (G.residueAction_tower_weight_pos q q' hdvd)
    (G.residueAction_tower_weight_le q q' hdvd)
    (G.residueWeight_pos q) (G.residueWeight_le_residueWeight_zero q)

/-- **The factorization is transitive** (review #14):
`W_q(0) = W_{q'}(0) · W_tower(0)` — the modal weight at the coarse
resolution factors through the finer one. -/
theorem residueWeight_factor_trans (hdvd : q ∣ q') :
    G.residueWeight q 0
      = G.residueWeight q' 0
        * (G.residueAction q').coarseWeight (⇑(G.h1TowerMap q q' hdvd)) 0 := by
  rw [G.residueAction_tower_weight q q' hdvd 0]
  have h0 : G.residueWeight q' 0 ≠ 0 := (G.residueWeight_pos q' 0).ne'
  field_simp

/-- **The partition function factors through the whole tower**
(review #14): `Z = W_{q'}(0) · (W_tower(0) · Z_q)` — consistent with
the one-step factorization at either resolution. -/
theorem classPartFn_tower (hdvd : q ∣ q') :
    (G.classSectorAction).partFn
      = G.residueWeight q' 0
        * ((G.residueAction q').coarseWeight (⇑(G.h1TowerMap q q' hdvd)) 0
            * (G.residueAction q).partFn) := by
  rw [G.classPartFn_eq_residueWeight_mul q,
    G.residueWeight_factor_trans q q' hdvd]
  ring

/-! #### The tower's laws (review #15)

The reduction maps genuinely form a tower: identity, composition,
independence of the divisibility witness, and surjectivity — with
the corresponding composition laws for residue weights,
distributions, and actions. -/

/-- **Identity law** (review #15): the tower map at `q ∣ q` is the
identity. -/
theorem h1TowerMap_id :
    G.h1TowerMap q q dvd_rfl = LinearMap.id := by
  refine LinearMap.ext fun ξ => ?_
  obtain ⟨κ, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rfl

/-- **Proof-witness independence** (review #15): the tower map does
not depend on the divisibility witness. -/
theorem h1TowerMap_proof_irrel (h₁ h₂ : q ∣ q') :
    G.h1TowerMap q q' h₁ = G.h1TowerMap q q' h₂ := rfl

/-- **Surjectivity** (review #15): every coarse class is hit — both
reductions are quotients of the same carrier. -/
theorem h1TowerMap_surjective (hdvd : q ∣ q') :
    Function.Surjective (G.h1TowerMap q q' hdvd) := by
  intro ξ
  obtain ⟨κ, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  exact ⟨Submodule.Quotient.mk κ, rfl⟩

end Tower

section TowerComp

variable (q' q'' : ℕ) [NeZero q'] [NeZero q'']

/-- **Composition law** (review #15): tower maps compose along
divisibility. -/
theorem h1TowerMap_comp (h₁ : q ∣ q') (h₂ : q' ∣ q'') :
    (G.h1TowerMap q q' h₁).comp (G.h1TowerMap q' q'' h₂)
      = G.h1TowerMap q q'' (h₁.trans h₂) := by
  refine LinearMap.ext fun ξ => ?_
  obtain ⟨κ, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rfl

/-- **Residue weights compose across the tower** (review #15):
pushing the finest weights forward in two steps agrees with the one
step — both compute the coarse coset weight. -/
theorem residueWeight_tower_trans (h₁ : q ∣ q') (h₂ : q' ∣ q'')
    (ξ : H1Reduction G q) :
    ∑' η : {η : H1Reduction G q' // G.h1TowerMap q q' h₁ η = ξ},
      (∑' ζ : {ζ : H1Reduction G q'' //
          G.h1TowerMap q' q'' h₂ ζ = η.val},
        G.residueWeight q'' ζ.val)
      = ∑' ζ : {ζ : H1Reduction G q'' //
          G.h1TowerMap q q'' (h₁.trans h₂) ζ = ξ},
          G.residueWeight q'' ζ.val :=
  calc ∑' η : {η : H1Reduction G q' // G.h1TowerMap q q' h₁ η = ξ},
        (∑' ζ : {ζ : H1Reduction G q'' //
            G.h1TowerMap q' q'' h₂ ζ = η.val},
          G.residueWeight q'' ζ.val)
      = ∑' η : {η : H1Reduction G q' // G.h1TowerMap q q' h₁ η = ξ},
          G.residueWeight q' η.val :=
        tsum_congr fun η => (G.residueWeight_tower q' q'' h₂ η.val).symm
    _ = G.residueWeight q ξ := (G.residueWeight_tower q q' h₁ ξ).symm
    _ = ∑' ζ : {ζ : H1Reduction G q'' //
          G.h1TowerMap q q'' (h₁.trans h₂) ζ = ξ},
          G.residueWeight q'' ζ.val :=
        G.residueWeight_tower q q'' (h₁.trans h₂) ξ

/-- **Residue distributions compose across the tower** (review #15):
the two-step pushforward of the finest Gibbs law equals the one-step
pushforward — both are the coarse residue distribution. -/
theorem residueDist_tower_trans (h₁ : q ∣ q') (h₂ : q' ∣ q'') :
    ((G.residueDist q'').map (⇑(G.h1TowerMap q' q'' h₂))).map
        (⇑(G.h1TowerMap q q' h₁))
      = (G.residueDist q'').map (⇑(G.h1TowerMap q q'' (h₁.trans h₂))) := by
  rw [G.residueDist_tower q' q'' h₂, G.residueDist_tower q q' h₁,
    G.residueDist_tower q q'' (h₁.trans h₂)]

/-- **Residue actions compose across the tower** (review #15):
coarse-graining the intermediate residue action and coarse-graining
the finest one agree at the coarse resolution — both are the coarse
residue action. -/
theorem residueAction_tower_trans (h₁ : q ∣ q') (h₂ : q' ∣ q'') :
    (G.residueAction q').coarseGrain (⇑(G.h1TowerMap q q' h₁)) 0
        (G.residueAction_tower_weight_pos q q' h₁)
        (G.residueAction_tower_weight_le q q' h₁)
      = (G.residueAction q'').coarseGrain
          (⇑(G.h1TowerMap q q'' (h₁.trans h₂))) 0
          (G.residueAction_tower_weight_pos q q'' (h₁.trans h₂))
          (G.residueAction_tower_weight_le q q'' (h₁.trans h₂)) := by
  rw [G.residueAction_tower q q' h₁, G.residueAction_tower q q'' (h₁.trans h₂)]

end TowerComp

/-! ### The price of resolution loss (review #15)

The tower is not free: dropping from resolution `q' = c·q` to
resolution `q` merges `c^{b₁}` fine classes into each coarse class
(`card_h1TowerMap_fiber`), reversing the merge costs `b₁·log c` per
coarse sector (`sectionCost_h1TowerMap` — the ratchet along the
tower), and under the Gibbs law the lost information is exactly the
conditional entropy of the tower map
(`residue_tower_entropy_chain`), which the two entropy splits read
as the difference of the `K + ⟨E⟩` decompositions
(`residue_tower_condEntropy_eq`). -/

section TowerCost

variable (q' c : ℕ) [NeZero q']

private noncomputable def towerFiberEquivKer (hdvd : q ∣ q') (ξ : H1Reduction G q)
    (η₀ : H1Reduction G q') (hη₀ : G.h1TowerMap q q' hdvd η₀ = ξ) :
    {η : H1Reduction G q' // G.h1TowerMap q q' hdvd η = ξ}
      ≃ {η : H1Reduction G q' // G.h1TowerMap q q' hdvd η = 0} where
  toFun η := ⟨η.val - η₀, by rw [map_sub, η.prop, hη₀, sub_self]⟩
  invFun η := ⟨η.val + η₀, by rw [map_add, η.prop, hη₀, zero_add]⟩
  left_inv η := Subtype.ext (sub_add_cancel _ _)
  right_inv η := Subtype.ext (add_sub_cancel_right _ _)

/-- **Every tower fiber has `c^{b₁}` classes** (review #15): dropping
one resolution step `q' = c·q` merges exactly `c^{b₁}` fine classes
into each coarse class. -/
theorem card_h1TowerMap_fiber (hdvd : q ∣ q') (hq' : q' = c * q)
    (ξ : H1Reduction G q) :
    Nat.card {η : H1Reduction G q' // G.h1TowerMap q q' hdvd η = ξ}
      = c ^ G.b1 := by
  classical
  have hfib : ∀ ζ : H1Reduction G q,
      Nat.card {η : H1Reduction G q' // G.h1TowerMap q q' hdvd η = ζ}
        = Nat.card {η : H1Reduction G q' //
            G.h1TowerMap q q' hdvd η = 0} := by
    intro ζ
    obtain ⟨η₁, hη₁⟩ := G.h1TowerMap_surjective q q' hdvd ζ
    exact Nat.card_congr (G.towerFiberEquivKer q q' hdvd ζ η₁ hη₁)
  have htot := card_eq_card_mul_of_fiber
    (fun η : H1Reduction G q' => G.h1TowerMap q q' hdvd η) hfib
  have hq : Nat.card (H1Reduction G q) = q ^ G.b1 := G.card_H1Reduction q
  have hq'' : Nat.card (H1Reduction G q') = q' ^ G.b1 :=
    G.card_H1Reduction q'
  rw [Nat.card_eq_fintype_card] at hq hq''
  rw [hq'', hq] at htot
  have hpow : q' ^ G.b1 = c ^ G.b1 * q ^ G.b1 := by
    rw [hq', mul_pow]
  have hqpos : 0 < q ^ G.b1 :=
    pow_pos (Nat.pos_of_ne_zero (NeZero.ne q)) _
  have hm : Nat.card {η : H1Reduction G q' //
      G.h1TowerMap q q' hdvd η = 0} = c ^ G.b1 := by
    refine Nat.eq_of_mul_eq_mul_left hqpos ?_
    calc q ^ G.b1 * Nat.card {η : H1Reduction G q' //
          G.h1TowerMap q q' hdvd η = 0}
        = q' ^ G.b1 := htot.symm
      _ = c ^ G.b1 * q ^ G.b1 := hpow
      _ = q ^ G.b1 * c ^ G.b1 := mul_comm _ _
  rw [hfib ξ, hm]

/-- **The ratchet along the tower** (review #15): reversing one
resolution step costs `b₁·log c` per coarse sector — the section
cost of the tower map, normalized. -/
theorem sectionCost_h1TowerMap (hdvd : q ∣ q') (hq' : q' = c * q) :
    sectionCost (⇑(G.h1TowerMap q q' hdvd)) / Nat.card (H1Reduction G q)
      = G.b1 * Real.log c := by
  classical
  have hcost : sectionCost (⇑(G.h1TowerMap q q' hdvd))
      = Fintype.card (H1Reduction G q) * Real.log ((c : ℝ) ^ G.b1) := by
    rw [sectionCost_eq_fiberInfoCost (G.h1TowerMap_surjective q q' hdvd)]
    unfold fiberInfoCost
    rw [Finset.sum_congr rfl fun ξ _ => by
      rw [show (Nat.card (⇑(G.h1TowerMap q q' hdvd) ⁻¹' {ξ}) : ℕ)
          = c ^ G.b1 from G.card_h1TowerMap_fiber q q' c hdvd hq' ξ]]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    push_cast
    ring
  have hcard : (0 : ℝ) < Fintype.card (H1Reduction G q) := by
    exact_mod_cast Fintype.card_pos
  rw [Nat.card_eq_fintype_card, hcost,
    mul_div_cancel_left₀ _ hcard.ne', Real.log_pow]

/-- **The Gibbs conditional-entropy chain across the tower**
(review #15): the fine residue entropy is the coarse residue entropy
plus the conditional entropy of the tower map under the fine Gibbs
law — what one resolution step forgets, priced by the Gibbs
distribution. -/
theorem residue_tower_entropy_chain (hdvd : q ∣ q') :
    shannonEntropy (G.residueMass q')
      = shannonEntropy (G.residueMass q)
        + (G.residueDist q').condEntropy (⇑(G.h1TowerMap q q' hdvd)) := by
  have h := FinDist.entropy_eq_map_add_condEntropy
    (⇑(G.h1TowerMap q q' hdvd)) (G.residueDist q')
    (fun η => G.residueMass_pos q' η)
  rw [G.residueDist_tower q q' hdvd] at h
  exact h

/-- **The lost information, priced** (review #15): the tower's
conditional entropy is the difference of the two residue actions'
`K + ⟨E⟩` decompositions — resolution loss is a difference of
pricings. -/
theorem residue_tower_condEntropy_eq (hdvd : q ∣ q') :
    (G.residueDist q').condEntropy (⇑(G.h1TowerMap q q' hdvd))
      = ((G.residueAction q').complexity
          + (G.residueAction q').gibbsExpect (G.residueAction q').E)
        - ((G.residueAction q).complexity
          + (G.residueAction q).gibbsExpect (G.residueAction q).E) := by
  have h1 := G.residueAction_entropy_split q
  have h2 := G.residueAction_entropy_split q'
  have h3 := G.residue_tower_entropy_chain q q' hdvd
  linarith

/-- **THE TWO PRICES IDENTIFIED** (review #16): the Gibbs price of
one resolution step is the uniform ratchet cost minus the deficit
gained — `H(q'|q) = b₁·log c − (Δ(q') − Δ(q))`. Counting and pricing
the same loss differ by exactly the action-induced information the
finer resolution carries. -/
theorem residue_tower_condEntropy_eq_defect (hdvd : q ∣ q')
    (hq' : q' = c * q) :
    (G.residueDist q').condEntropy (⇑(G.h1TowerMap q q' hdvd))
      = G.b1 * Real.log c - (G.residueDefect q' - G.residueDefect q) := by
  have hchain := G.residue_tower_entropy_chain q q' hdvd
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact (NeZero.ne q') (by rw [hq', zero_mul])
  have hq0 : q ≠ 0 := NeZero.ne q
  have hcard : Real.log (Fintype.card (H1Reduction G q'))
      = G.b1 * Real.log c + Real.log (Fintype.card (H1Reduction G q)) := by
    have h1 : Fintype.card (H1Reduction G q') = q' ^ G.b1 := by
      rw [← Nat.card_eq_fintype_card]
      exact G.card_H1Reduction q'
    have h2 : Fintype.card (H1Reduction G q) = q ^ G.b1 := by
      rw [← Nat.card_eq_fintype_card]
      exact G.card_H1Reduction q
    rw [h1, h2, hq']
    push_cast
    rw [mul_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
  have hΔ' : G.residueDefect q'
      = Real.log (Fintype.card (H1Reduction G q'))
        - shannonEntropy (G.residueMass q') := rfl
  have hΔ : G.residueDefect q
      = Real.log (Fintype.card (H1Reduction G q))
        - shannonEntropy (G.residueMass q) := rfl
  rw [hΔ', hΔ]
  linarith

/-- **THE STRICT PRICE OF ONE RESOLUTION STEP** (review #16): for a
graph with cycles and a genuine refinement (`b₁ > 0`, `c > 1`), the
Gibbs price is strictly positive and strictly below the uniform
ratchet cost, and the deficit strictly grows —
`0 < H(q'|q) < b₁·log c` and `Δ(q) < Δ(q')`. -/
theorem residue_tower_price_strict (hb : 0 < G.b1) (hc : 1 < c)
    (hdvd : q ∣ q') (hq' : q' = c * q) :
    0 < (G.residueDist q').condEntropy (⇑(G.h1TowerMap q q' hdvd))
      ∧ (G.residueDist q').condEntropy (⇑(G.h1TowerMap q q' hdvd))
          < G.b1 * Real.log c
      ∧ G.residueDefect q < G.residueDefect q' := by
  classical
  -- the zero fiber has c^{b₁} ≥ 2 classes
  have hcard : 1 < Nat.card {η : H1Reduction G q' //
      G.h1TowerMap q q' hdvd η = (0 : H1Reduction G q)} := by
    rw [G.card_h1TowerMap_fiber q q' c hdvd hq' 0]
    exact Nat.one_lt_pow hb.ne' hc
  haveI : Nontrivial {η : H1Reduction G q' //
      G.h1TowerMap q q' hdvd η = (0 : H1Reduction G q)} :=
    Finite.one_lt_card_iff_nontrivial.mp hcard
  have h0mem : G.h1TowerMap q q' hdvd (0 : H1Reduction G q') = 0 :=
    map_zero _
  obtain ⟨η, hη⟩ := exists_ne (⟨0, h0mem⟩ : {η : H1Reduction G q' //
      G.h1TowerMap q q' hdvd η = (0 : H1Reduction G q)})
  have hηne : η.val ≠ (0 : H1Reduction G q') :=
    fun h => hη (Subtype.ext h)
  -- strict positivity: two points in the zero fiber
  have hpos : 0 < (G.residueDist q').condEntropy
      (⇑(G.h1TowerMap q q' hdvd)) := by
    refine FinDist.condEntropy_pos _ _ (fun κ => G.residueMass_pos q' κ)
      (x := η.val) (y := (0 : H1Reduction G q')) hηne ?_
    rw [η.prop, h0mem]
  -- strict upper bound: the residue law is not fiber-uniform
  have hm : 0 < c ^ G.b1 := pow_pos (Nat.pos_of_ne_zero (by
    rintro rfl
    exact absurd hc (by norm_num))) _
  have hne : G.residueDist q'
      ≠ ((G.residueDist q').map
          (⇑(G.h1TowerMap q q' hdvd))).uniformLift
          (⇑(G.h1TowerMap q q' hdvd)) hm
          (G.card_h1TowerMap_fiber q q' c hdvd hq') := by
    intro heq
    have h1 := congrFun (congrArg FinDist.mass heq) (0 : H1Reduction G q')
    have h2 := congrFun (congrArg FinDist.mass heq) η.val
    have h3 : ((G.residueDist q').map
        (⇑(G.h1TowerMap q q' hdvd))).mass
          (G.h1TowerMap q q' hdvd (0 : H1Reduction G q'))
        = ((G.residueDist q').map (⇑(G.h1TowerMap q q' hdvd))).mass
          (G.h1TowerMap q q' hdvd η.val) := by
      rw [h0mem, η.prop]
    have h4 : G.residueMass q' 0 = G.residueMass q' η.val := by
      have h5 : (G.residueDist q').mass (0 : H1Reduction G q')
          = (G.residueDist q').mass η.val := by
        rw [h1, h2]
        show _ / _ = _ / _
        rw [h3]
      exact h5
    exact absurd h4.symm
      (ne_of_lt (G.residueMass_lt_residueMass_zero q' hηne))
  have hlt' : (G.residueDist q').condEntropy
      (⇑(G.h1TowerMap q q' hdvd)) < Real.log ((c : ℝ) ^ G.b1) := by
    have h := FinDist.condEntropy_lt_log (⇑(G.h1TowerMap q q' hdvd))
      hm (G.card_h1TowerMap_fiber q q' c hdvd hq') (G.residueDist q')
      (fun κ => G.residueMass_pos q' κ) hne
    rwa [show (((c ^ G.b1 : ℕ) : ℝ)) = (c : ℝ) ^ G.b1 from by push_cast; rfl]
      at h
  have hlt : (G.residueDist q').condEntropy
      (⇑(G.h1TowerMap q q' hdvd)) < G.b1 * Real.log c := by
    rwa [Real.log_pow] at hlt'
  have hid := G.residue_tower_condEntropy_eq_defect q q' c hdvd hq'
  exact ⟨hpos, hlt, by linarith⟩

end TowerCost

/-! ### The priced composition law (review #17)

The price is not only a one-step theorem: conditional entropies add
along the tower by the generic chain rule
(`residue_tower_condEntropy_trans` — `H(q″|q) = H(q″|q′) + H(q′|q)`),
section costs add (`sectionCost_h1TowerMap_trans`), and the deficit
increments telescope, so the two-step price identity is exactly the
sum of the one-step identities (`residue_tower_price_trans`). -/

section TowerPriceComp

variable (q' q'' c c' : ℕ) [NeZero q'] [NeZero q'']

/-- **Conditional entropies add along the tower** (review #17):
`H(q″|q) = H(q″|q′) + H(q′|q)` — the generic chain rule
`FinDist.condEntropy_comp` specialized to the tower maps, with the
intermediate pushforward identified as the intermediate residue
distribution. -/
theorem residue_tower_condEntropy_trans (h₁ : q ∣ q') (h₂ : q' ∣ q'') :
    (G.residueDist q'').condEntropy (⇑(G.h1TowerMap q q'' (h₁.trans h₂)))
      = (G.residueDist q'').condEntropy (⇑(G.h1TowerMap q' q'' h₂))
        + (G.residueDist q').condEntropy (⇑(G.h1TowerMap q q' h₁)) := by
  have hcomp : ⇑(G.h1TowerMap q q'' (h₁.trans h₂))
      = ⇑(G.h1TowerMap q q' h₁) ∘ ⇑(G.h1TowerMap q' q'' h₂) := by
    rw [← G.h1TowerMap_comp q q' q'' h₁ h₂]
    rfl
  rw [hcomp, FinDist.condEntropy_comp, G.residueDist_tower q' q'' h₂]

/-- **Section costs add along the tower** (review #17): reversing two
resolution steps costs the sum of the one-step ratchet costs. -/
theorem sectionCost_h1TowerMap_trans (h₁ : q ∣ q') (h₂ : q' ∣ q'')
    (hq' : q' = c * q) (hq'' : q'' = c' * q') :
    sectionCost (⇑(G.h1TowerMap q q'' (h₁.trans h₂)))
        / Nat.card (H1Reduction G q)
      = sectionCost (⇑(G.h1TowerMap q' q'' h₂))
            / Nat.card (H1Reduction G q')
        + sectionCost (⇑(G.h1TowerMap q q' h₁))
            / Nat.card (H1Reduction G q) := by
  have hc : c ≠ 0 := by
    rintro rfl
    exact (NeZero.ne q') (by rw [hq', zero_mul])
  have hc' : c' ≠ 0 := by
    rintro rfl
    exact (NeZero.ne q'') (by rw [hq'', zero_mul])
  have hqcomp : q'' = (c' * c) * q := by rw [hq'', hq', mul_assoc]
  rw [G.sectionCost_h1TowerMap q q' c h₁ hq',
    G.sectionCost_h1TowerMap q' q'' c' h₂ hq'',
    G.sectionCost_h1TowerMap q q'' (c' * c) (h₁.trans h₂) hqcomp,
    Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hc') (by exact_mod_cast hc)]
  ring

/-- **The deficit increments telescope** (review #17): the two-step
price identity is the sum of the one-step identities — the chain rule
adds the conditional entropies, the section costs add, and
`(Δ(q″) − Δ(q′)) + (Δ(q′) − Δ(q)) = Δ(q″) − Δ(q)`. -/
theorem residue_tower_price_trans (h₁ : q ∣ q') (h₂ : q' ∣ q'')
    (hq' : q' = c * q) (hq'' : q'' = c' * q') :
    (G.residueDist q'').condEntropy (⇑(G.h1TowerMap q q'' (h₁.trans h₂)))
      = G.b1 * Real.log ((c' * c : ℕ))
        - (G.residueDefect q'' - G.residueDefect q) := by
  have hc : c ≠ 0 := by
    rintro rfl
    exact (NeZero.ne q') (by rw [hq', zero_mul])
  have hc' : c' ≠ 0 := by
    rintro rfl
    exact (NeZero.ne q'') (by rw [hq'', zero_mul])
  rw [G.residue_tower_condEntropy_trans q q' q'' h₁ h₂,
    G.residue_tower_condEntropy_eq_defect q q' c h₁ hq',
    G.residue_tower_condEntropy_eq_defect q' q'' c' h₂ hq'',
    Nat.cast_mul,
    Real.log_mul (by exact_mod_cast hc') (by exact_mod_cast hc)]
  ring

end TowerPriceComp

end IncidenceGraph


end Meno
