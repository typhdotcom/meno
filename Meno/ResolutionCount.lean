import Meno.GraphHomology
import Meno.InfoRatchet
import Meno.UniformAction

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
complexity + residue complexity. Gravity, matter, time, and
uncertainty now share one carrier: the sector lattice with its
action. -/
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

end IncidenceGraph

end Meno
