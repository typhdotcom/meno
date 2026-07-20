import Meno.Matter
import Meno.GraphInstances

/-! # The Systole Inequality (G1)

The geometry ⋈ matter face of the obstruction program (PLAN, G1).

* **The impossibility anchor** is the standing `MatterSector.not_gradient`
  (`Meno/Matter.lean`): the class whose mass the inequality bounds
  admits no global potential — locally consistent, globally
  unsatisfiable.
* **The exact law** (`pairing_sq_le_energy_mul_normSq`): for every
  finite graph, every class, and every integral cycle, pairing squared
  is bounded by harmonic energy times chain norm. Route: the attained
  realizer of the class's periods (`harmonicEnergy_isLeast`) pairs
  with the cycle as the integer pairing
  (`realizer_dotProduct_castCycle`), and Cauchy–Schwarz closes.
* **The boundary (dual-norm attainment)**: the bound is sharp at the
  harmonic representative, which lies in the real cycle space — the
  least-norm representative is the explicit combination `periodRep`
  with coefficients `(gramOf c)⁻¹ *ᵥ k`. For every real cycle
  combination `z ≠ 0`, `(pairing z κ)² / ‖z‖² ≤ harmonicEnergy κ`
  (`dualNorm_combination_le`), with equality iff `z` is parallel to
  the harmonic representative (`dualNorm_combination_eq_iff`). The
  prerequisite inverse-Gram identity is the standing
  `basisGramData_gram` (`Meno/BasisIndependence.lean`).
* **The systole corollary** (`MatterSector.mass_systole`): matter's
  mass is bounded below by the reciprocal chain norm of any cycle it
  pairs with — the integer pairing squared is at least one.
* **The boundary witness** (`cycle_systole_equality`): on `C_n` with
  the full cycle the bound is equality — mass `1/n`, pairing `1`,
  norm `n`. `Simplicial.geodesic_harmonic_duality`
  (`Meno/Groupoid.lean`) is re-derived as this equality instance
  through the walk-length bridge (demotion, PLAN rule 3).
* **The strictness** lives at the theta graph
  (`Meno/ThetaHarmonic.lean`): `theta_pairing_normSq_ge_four` and
  `theta_mass_gt_systole` — the systole bound `1/4` is strictly below
  the mass `1/3`. -/

namespace Meno

open scoped BigOperators
open Matrix

universe u v

/-! ## Cauchy–Schwarz for the edge dot product, with its equality case -/

section DotProductCauchySchwarz

variable {ι : Type*} [Fintype ι]

/-- **Cauchy–Schwarz for the unit-edge dot product**: pairing squared
is bounded by the product of the squared norms. -/
theorem dotProduct_sq_le_normSq_mul_normSq (u w : ι → ℝ) :
    (u ⬝ᵥ w) ^ 2 ≤ (u ⬝ᵥ u) * (w ⬝ᵥ w) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u w
  calc (u ⬝ᵥ w) ^ 2 = (∑ i, u i * w i) ^ 2 := rfl
    _ ≤ (∑ i, u i ^ 2) * ∑ i, w i ^ 2 := h
    _ = (u ⬝ᵥ u) * (w ⬝ᵥ w) := by
        congr 1 <;> exact Finset.sum_congr rfl fun i _ => pow_two _

/-- **The equality case of Cauchy–Schwarz**: against a vector of
nonzero norm, the bound is attained exactly on its scalar multiples. -/
theorem dotProduct_sq_eq_normSq_mul_normSq_iff (u w : ι → ℝ)
    (hu : u ⬝ᵥ u ≠ 0) :
    (u ⬝ᵥ w) ^ 2 = (u ⬝ᵥ u) * (w ⬝ᵥ w) ↔ ∃ t : ℝ, w = t • u := by
  constructor
  · intro heq
    refine ⟨(u ⬝ᵥ w) / (u ⬝ᵥ u), ?_⟩
    have hexp : (w - ((u ⬝ᵥ w) / (u ⬝ᵥ u)) • u)
        ⬝ᵥ (w - ((u ⬝ᵥ w) / (u ⬝ᵥ u)) • u)
        = w ⬝ᵥ w - (u ⬝ᵥ w) ^ 2 / (u ⬝ᵥ u) := by
      show ∑ i, (w i - (u ⬝ᵥ w) / (u ⬝ᵥ u) * u i)
          * (w i - (u ⬝ᵥ w) / (u ⬝ᵥ u) * u i) = _
      rw [Finset.sum_congr rfl fun i _ =>
        show (w i - (u ⬝ᵥ w) / (u ⬝ᵥ u) * u i)
            * (w i - (u ⬝ᵥ w) / (u ⬝ᵥ u) * u i)
          = w i * w i - 2 * ((u ⬝ᵥ w) / (u ⬝ᵥ u)) * (u i * w i)
            + ((u ⬝ᵥ w) / (u ⬝ᵥ u)) ^ 2 * (u i * u i) from by ring]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      show w ⬝ᵥ w - 2 * ((u ⬝ᵥ w) / (u ⬝ᵥ u)) * (u ⬝ᵥ w)
          + ((u ⬝ᵥ w) / (u ⬝ᵥ u)) ^ 2 * (u ⬝ᵥ u) = _
      field_simp
      ring
    have hzero : (w - ((u ⬝ᵥ w) / (u ⬝ᵥ u)) • u)
        ⬝ᵥ (w - ((u ⬝ᵥ w) / (u ⬝ᵥ u)) • u) = 0 := by
      rw [hexp, heq]
      field_simp
      ring
    exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hzero)
  · rintro ⟨t, rfl⟩
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring

end DotProductCauchySchwarz

/-! ## The harmonic representative pairs with cycle combinations -/

section PeriodRepPairing

variable {ι : Type*} [Fintype ι] {r : ℕ}

/-- The least-norm representative pairs with a combination of the
cycle vectors through its coefficients: `⟨rep, Σᵢ xᵢcᵢ⟩ = x ⬝ᵥ k`. -/
theorem periodRep_dotProduct_combination (c : Fin r → ι → ℝ)
    (hC : IsUnit (gramOf c).det) (k x : Fin r → ℝ) :
    periodRep c k ⬝ᵥ (fun e => ∑ i, x i * c i e) = x ⬝ᵥ k := by
  calc periodRep c k ⬝ᵥ (fun e => ∑ i, x i * c i e)
      = ∑ e, periodRep c k e * ∑ i, x i * c i e := rfl
    _ = ∑ e, ∑ i, x i * (periodRep c k e * c i e) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, ∑ e, x i * (periodRep c k e * c i e) := Finset.sum_comm
    _ = ∑ i, x i * (periodRep c k ⬝ᵥ c i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum]
        rfl
    _ = ∑ i, x i * k i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [periodRep_periods c hC k i]
    _ = x ⬝ᵥ k := rfl

end PeriodRepPairing

namespace IncidenceGraph

variable (G : IncidenceGraph.{u, v})

/-! ## Stokes against cast lattice cycles, and the realizer pairing -/

/-- **Real Stokes against any cast lattice cycle**: a real gradient
pairs to zero against the cast of any integral cycle. -/
theorem grad_dotProduct_castCycle (f : G.V → ℝ) (c : ↥G.cycleLattice) :
    G.grad f ⬝ᵥ (fun e => ((c : G.E → ℤ) e : ℝ)) = 0 := by
  rw [G.grad_dotProduct_eq]
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [show G.boundary (fun e => ((c : G.E → ℤ) e : ℝ)) v = 0 from by
      rw [G.boundary_castR, G.mem_cycleLattice.mp c.prop v, Int.cast_zero],
    mul_zero]

/-- **A realizer pairs as the integer pairing**: every real cochain
realizing a class's periods pairs with every integral cycle as the
class's `cyclePairing` — the gradient ambiguity dies against the
cycle by Stokes. -/
theorem realizer_dotProduct_castCycle
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) (ω : G.E → ℝ)
    (hω : ∀ j, ω ⬝ᵥ G.fundCyclesR j = ((G.h1QuotEquiv κ j : ℤ) : ℝ))
    (c : ↥G.cycleLattice) :
    ω ⬝ᵥ (fun e => ((c : G.E → ℤ) e : ℝ))
      = ((G.cyclePairing c κ : ℤ) : ℝ) := by
  obtain ⟨τ, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  obtain ⟨f, rfl⟩ := (G.periods_eq_cast_iff G.cycleBasis τ ω).mp hω
  rw [add_dotProduct, G.grad_dotProduct_castCycle f c, add_zero,
    G.cyclePairing_mk]
  show ∑ e, ((τ e : ℤ) : ℝ) * ((c : G.E → ℤ) e : ℝ)
    = ((∑ e, τ e * (c : G.E → ℤ) e : ℤ) : ℝ)
  push_cast
  rfl

/-! ## The exact law -/

/-- **THE SYSTOLE INEQUALITY** (G1, the exact law): for every finite
graph, every class, and every integral cycle, pairing squared is
bounded by harmonic energy times chain norm. The realizer attained by
`harmonicEnergy_isLeast` pairs as the integer pairing; Cauchy–Schwarz
closes the bound. -/
theorem pairing_sq_le_energy_mul_normSq
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))
    (c : ↥G.cycleLattice) :
    ((G.cyclePairing c κ : ℤ) : ℝ) ^ 2
      ≤ G.harmonicEnergy κ
        * ((fun e => ((c : G.E → ℤ) e : ℝ))
            ⬝ᵥ (fun e => ((c : G.E → ℤ) e : ℝ))) := by
  obtain ⟨⟨ω, hper, hE⟩, -⟩ := G.harmonicEnergy_isLeast κ
  rw [← G.realizer_dotProduct_castCycle κ ω hper c, hE]
  exact dotProduct_sq_le_normSq_mul_normSq ω _

/-! ## The boundary: dual-norm attainment at the harmonic representative -/

/-- **The harmonic energy is the squared norm of the explicit
least-norm representative** `periodRep` — the harmonic representative
lies in the real cycle space, with coefficients `(gramOf c)⁻¹ *ᵥ k`
(the standing inverse-Gram identity `basisGramData_gram`). -/
theorem harmonicEnergy_eq_periodRep_normSq
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :
    G.harmonicEnergy κ
      = periodRep G.fundCyclesR (fun i => ((G.h1QuotEquiv κ i : ℤ) : ℝ))
        ⬝ᵥ periodRep G.fundCyclesR (fun i => ((G.h1QuotEquiv κ i : ℤ) : ℝ)) := by
  have hdet : IsUnit (gramOf G.fundCyclesR).det :=
    isUnit_iff_ne_zero.mpr
      (ne_of_gt (G.gramOf_cyclesR_posDef G.cycleBasis).det_pos)
  rw [periodRep_energy G.fundCyclesR hdet
    (fun i => ((G.h1QuotEquiv κ i : ℤ) : ℝ))]
  show ∑ i, ∑ j, (gramOf G.fundCyclesR)⁻¹ i j
      * ((G.h1QuotEquiv κ i : ℤ) : ℝ) * ((G.h1QuotEquiv κ j : ℤ) : ℝ) = _
  rw [quadForm_dotProduct]

/-- **The dual-norm bound** (G1 boundary, inequality half): every real
combination of the fundamental cycles certifies a lower bound on the
harmonic energy through its normalized squared pairing. -/
theorem dualNorm_combination_le
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) (x : Fin G.b1 → ℝ)
    (hz : (fun e => ∑ i, x i * G.fundCyclesR i e) ≠ 0) :
    (x ⬝ᵥ fun i => ((G.h1QuotEquiv κ i : ℤ) : ℝ)) ^ 2
      / ((fun e => ∑ i, x i * G.fundCyclesR i e)
          ⬝ᵥ (fun e => ∑ i, x i * G.fundCyclesR i e))
      ≤ G.harmonicEnergy κ := by
  have hdet : IsUnit (gramOf G.fundCyclesR).det :=
    isUnit_iff_ne_zero.mpr
      (ne_of_gt (G.gramOf_cyclesR_posDef G.cycleBasis).det_pos)
  have hzpos : 0 < (fun e => ∑ i, x i * G.fundCyclesR i e)
      ⬝ᵥ (fun e => ∑ i, x i * G.fundCyclesR i e) :=
    lt_of_le_of_ne (Finset.sum_nonneg fun e _ => mul_self_nonneg _)
      (Ne.symm fun h0 => hz (dotProduct_self_eq_zero.mp h0))
  rw [div_le_iff₀ hzpos,
    ← periodRep_dotProduct_combination G.fundCyclesR hdet
      (fun i => ((G.h1QuotEquiv κ i : ℤ) : ℝ)) x,
    G.harmonicEnergy_eq_periodRep_normSq κ]
  exact dotProduct_sq_le_normSq_mul_normSq _ _

/-- **Dual-norm attainment** (G1 boundary, equality half): for a
nonzero class, the dual-norm bound is attained at `z` exactly when
`z` is parallel to the harmonic representative. -/
theorem dualNorm_combination_eq_iff
    {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)} (hκ : κ ≠ 0)
    (x : Fin G.b1 → ℝ)
    (hz : (fun e => ∑ i, x i * G.fundCyclesR i e) ≠ 0) :
    (x ⬝ᵥ fun i => ((G.h1QuotEquiv κ i : ℤ) : ℝ)) ^ 2
      / ((fun e => ∑ i, x i * G.fundCyclesR i e)
          ⬝ᵥ (fun e => ∑ i, x i * G.fundCyclesR i e))
      = G.harmonicEnergy κ
      ↔ ∃ t : ℝ, (fun e => ∑ i, x i * G.fundCyclesR i e)
          = t • periodRep G.fundCyclesR
              (fun i => ((G.h1QuotEquiv κ i : ℤ) : ℝ)) := by
  have hdet : IsUnit (gramOf G.fundCyclesR).det :=
    isUnit_iff_ne_zero.mpr
      (ne_of_gt (G.gramOf_cyclesR_posDef G.cycleBasis).det_pos)
  have hzpos : 0 < (fun e => ∑ i, x i * G.fundCyclesR i e)
      ⬝ᵥ (fun e => ∑ i, x i * G.fundCyclesR i e) :=
    lt_of_le_of_ne (Finset.sum_nonneg fun e _ => mul_self_nonneg _)
      (Ne.symm fun h0 => hz (dotProduct_self_eq_zero.mp h0))
  have hrepne : periodRep G.fundCyclesR
        (fun i => ((G.h1QuotEquiv κ i : ℤ) : ℝ))
      ⬝ᵥ periodRep G.fundCyclesR
        (fun i => ((G.h1QuotEquiv κ i : ℤ) : ℝ)) ≠ 0 := by
    rw [← G.harmonicEnergy_eq_periodRep_normSq κ]
    exact ne_of_gt (G.harmonicEnergy_pos hκ)
  rw [div_eq_iff (ne_of_gt hzpos),
    ← periodRep_dotProduct_combination G.fundCyclesR hdet
      (fun i => ((G.h1QuotEquiv κ i : ℤ) : ℝ)) x,
    G.harmonicEnergy_eq_periodRep_normSq κ]
  exact dotProduct_sq_eq_normSq_mul_normSq_iff _ _ hrepne

/-! ## Chain norms in basis coordinates -/

/-- The cast of an integral cycle is the real combination of any
basis's cast cycles with its coordinate coefficients. -/
theorem castCycle_eq_reprCombination {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) (c : ↥G.cycleLattice) :
    (fun e => ((c : G.E → ℤ) e : ℝ))
      = fun e => ∑ i, ((B.repr c i : ℤ) : ℝ) * G.cyclesR B i e := by
  have hcoe : ∀ e, (c : G.E → ℤ) e = ∑ i, B.repr c i * G.cyclesZ B i e := by
    intro e
    conv_lhs => rw [← B.sum_repr c]
    rw [show ((∑ i, B.repr c i • B i : ↥G.cycleLattice) : G.E → ℤ)
        = ∑ i, B.repr c i • G.cyclesZ B i from by
      rw [show ((∑ i, B.repr c i • B i : ↥G.cycleLattice) : G.E → ℤ)
          = G.cycleLattice.subtype (∑ i, B.repr c i • B i) from rfl,
        map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl]
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul]
  funext e
  rw [hcoe e]
  push_cast
  rfl

/-- **The chain norm in coordinates**: the squared norm of a cast
integral cycle is the chain-Gram quadratic form of its basis
coordinates — the computational engine of the concrete systoles. -/
theorem castCycle_normSq_eq_repr_quadForm {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) (c : ↥G.cycleLattice) :
    (fun e => ((c : G.E → ℤ) e : ℝ)) ⬝ᵥ (fun e => ((c : G.E → ℤ) e : ℝ))
      = (fun i => ((B.repr c i : ℤ) : ℝ))
          ⬝ᵥ (gramOf (G.cyclesR B) *ᵥ fun i => ((B.repr c i : ℤ) : ℝ)) := by
  rw [dotProduct_gramOf_mulVec, G.castCycle_eq_reprCombination B c]

end IncidenceGraph

/-! ## The systole corollary -/

namespace MatterSector

variable {G : IncidenceGraph.{u, v}}

/-- **THE MASS–SYSTOLE BOUND** (G1 corollary): matter's mass is
bounded below by the reciprocal chain norm of every integral cycle it
pairs with nontrivially — the integer pairing squared is at least
one. -/
theorem mass_systole (m : MatterSector G) (c : ↥G.cycleLattice)
    (h : G.cyclePairing c m.val ≠ 0) :
    1 / ((fun e => ((c : G.E → ℤ) e : ℝ))
        ⬝ᵥ (fun e => ((c : G.E → ℤ) e : ℝ)))
      ≤ m.mass := by
  have hcast : (fun e => ((c : G.E → ℤ) e : ℝ)) ≠ 0 := by
    intro h0
    apply h
    have hc0 : (c : G.E → ℤ) = 0 := funext fun e => by
      have h1 : ((c : G.E → ℤ) e : ℝ) = 0 := by simpa using congrFun h0 e
      exact_mod_cast h1
    obtain ⟨τ, hτ⟩ := Submodule.Quotient.mk_surjective _ m.val
    rw [← hτ, G.cyclePairing_mk, hc0]
    exact dotProduct_zero τ
  have hpos : 0 < (fun e => ((c : G.E → ℤ) e : ℝ))
      ⬝ᵥ (fun e => ((c : G.E → ℤ) e : ℝ)) :=
    lt_of_le_of_ne (Finset.sum_nonneg fun e _ => mul_self_nonneg _)
      (Ne.symm fun h0 => hcast (dotProduct_self_eq_zero.mp h0))
  rw [div_le_iff₀ hpos]
  have hp : (1 : ℝ) ≤ ((G.cyclePairing c m.val : ℤ) : ℝ) ^ 2 := by
    have h1 : (1 : ℤ) ≤ (G.cyclePairing c m.val) ^ 2 := by
      rcases lt_or_gt_of_ne h with hlt | hgt
      · nlinarith
      · nlinarith
    exact_mod_cast h1
  calc (1 : ℝ) ≤ ((G.cyclePairing c m.val : ℤ) : ℝ) ^ 2 := hp
    _ ≤ G.harmonicEnergy m.val
        * ((fun e => ((c : G.E → ℤ) e : ℝ))
            ⬝ᵥ (fun e => ((c : G.E → ℤ) e : ℝ))) :=
      G.pairing_sq_le_energy_mul_normSq m.val c
    _ = m.mass * ((fun e => ((c : G.E → ℤ) e : ℝ))
        ⬝ᵥ (fun e => ((c : G.E → ℤ) e : ℝ))) := rfl

end MatterSector

/-! ## The boundary witness: equality on the cycle graph -/

section CycleWitness

variable (n : ℕ) (hn : 0 < n)

/-- The cast cycles of the cycle graph's lattice basis are the
all-ones family. -/
theorem cyclesR_cycleLatticeBasis :
    (cycleGraph n hn).cyclesR (cycleLatticeBasis n hn) = cycleAllOnes n := by
  funext i e
  show (((cycleGraph n hn).cyclesZ (cycleLatticeBasis n hn) i e : ℤ) : ℝ) = 1
  rw [cyclesZ_cycleLatticeBasis]
  exact Int.cast_one

/-- **Matter on the cycle graph**: the winding-one class of `C_n`. -/
noncomputable def cycleMatter : MatterSector (cycleGraph n hn) :=
  haveI : NeZero n := ⟨hn.ne'⟩
  ⟨Submodule.Quotient.mk (Pi.single 0 1), by
    intro h0
    have h := congrArg
      ((cycleGraph n hn).latticeQuotEquiv (cycleLatticeBasis n hn)) h0
    rw [map_zero] at h
    have h1 : Pi.single (0 : Fin n) (1 : ℤ)
        ⬝ᵥ (cycleGraph n hn).cyclesZ (cycleLatticeBasis n hn) 0 = 0 :=
      congrFun h 0
    rw [cyclesZ_cycleLatticeBasis] at h1
    have hone : Pi.single (0 : Fin n) (1 : ℤ) ⬝ᵥ cycleCyclesZ n 0 = 1 := by
      show ∑ e, (Pi.single 0 1 : Fin n → ℤ) e * 1 = 1
      simp only [mul_one]
      exact Fintype.sum_pi_single' 0 1
    rw [hone] at h1
    exact absurd h1 one_ne_zero⟩

/-- The cycle matter's keystone coordinates against the cycle basis:
winding one. -/
theorem cycleMatter_coords :
    (cycleGraph n hn).latticeQuotEquiv (cycleLatticeBasis n hn)
      (cycleMatter n hn).val = ![1] := by
  haveI : NeZero n := ⟨hn.ne'⟩
  funext j
  show Pi.single (0 : Fin n) (1 : ℤ)
    ⬝ᵥ (cycleGraph n hn).cyclesZ (cycleLatticeBasis n hn) j = ![1] j
  rw [cyclesZ_cycleLatticeBasis,
    show (![1] : Fin 1 → ℤ) j = 1 from by fin_cases j; rfl]
  show ∑ e, (Pi.single 0 1 : Fin n → ℤ) e * 1 = 1
  simp only [mul_one]
  exact Fintype.sum_pi_single' 0 1

/-- **The mass is `1/n`** — the harmonic energy of the winding-one
class, through the cycle basis's chart. -/
theorem cycleMatter_mass : (cycleMatter n hn).mass = 1 / n := by
  rw [← (cycleMatter n hn).mass_chart (cycleLatticeBasis n hn),
    cycleMatter_coords]
  show ∑ i, ∑ j,
      (gramOf ((cycleGraph n hn).cyclesR (cycleLatticeBasis n hn)))⁻¹ i j
        * ((![1] : Fin 1 → ℤ) i : ℝ) * ((![1] : Fin 1 → ℤ) j : ℝ) = 1 / n
  rw [cyclesR_cycleLatticeBasis n hn, gramOf_cycleAllOnes,
    inv_fin_one (n : ℝ) (by exact_mod_cast hn.ne')]
  norm_num [Fin.sum_univ_one]

/-- **The pairing is `1`**: the winding-one class evaluates to one on
the full cycle. -/
theorem cycleMatter_pairing :
    (cycleGraph n hn).cyclePairing (cycleLatticeBasis n hn 0)
      (cycleMatter n hn).val = 1 := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [show (cycleMatter n hn).val
      = Submodule.Quotient.mk (Pi.single 0 1) from rfl,
    (cycleGraph n hn).cyclePairing_mk,
    show ((cycleLatticeBasis n hn 0 : ↥(cycleGraph n hn).cycleLattice)
        : Fin n → ℤ) = cycleCyclesZ n 0 from by
      show (cycleGraph n hn).cyclesZ (cycleLatticeBasis n hn) 0
        = cycleCyclesZ n 0
      rw [cyclesZ_cycleLatticeBasis]]
  show ∑ e, (Pi.single 0 1 : Fin n → ℤ) e * 1 = 1
  simp only [mul_one]
  exact Fintype.sum_pi_single' 0 1

/-- **The norm is `n`**: the chain norm of the full cycle. -/
theorem cycleFullCycle_normSq :
    (fun e => (((cycleLatticeBasis n hn 0 : ↥(cycleGraph n hn).cycleLattice)
        : Fin n → ℤ) e : ℝ))
      ⬝ᵥ (fun e => (((cycleLatticeBasis n hn 0
          : ↥(cycleGraph n hn).cycleLattice) : Fin n → ℤ) e : ℝ))
      = n := by
  have hone : ∀ e : Fin n,
      (((cycleLatticeBasis n hn 0 : ↥(cycleGraph n hn).cycleLattice)
        : Fin n → ℤ) e : ℝ) = 1 := fun e => by
    rw [show ((cycleLatticeBasis n hn 0 : ↥(cycleGraph n hn).cycleLattice)
        : Fin n → ℤ) = cycleCyclesZ n 0 from by
      show (cycleGraph n hn).cyclesZ (cycleLatticeBasis n hn) 0
        = cycleCyclesZ n 0
      rw [cyclesZ_cycleLatticeBasis]]
    exact Int.cast_one
  rw [show (fun e => (((cycleLatticeBasis n hn 0
      : ↥(cycleGraph n hn).cycleLattice) : Fin n → ℤ) e : ℝ))
      = fun _ : Fin n => (1 : ℝ) from funext hone]
  show ∑ _e : Fin n, (1 : ℝ) * 1 = n
  rw [Finset.sum_congr rfl fun e _ => mul_one (1 : ℝ), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **THE EQUALITY CASE** (G1 boundary witness): on `C_n` with the
full cycle, the systole inequality is equality — mass `1/n`, pairing
`1`, norm `n`. The walk-layer duality
`Simplicial.geodesic_harmonic_duality` is this instance, through the
walk-length bridge (demotion, PLAN rule 3). -/
theorem cycle_systole_equality :
    (((cycleGraph n hn).cyclePairing (cycleLatticeBasis n hn 0)
        (cycleMatter n hn).val : ℤ) : ℝ) ^ 2
      = (cycleMatter n hn).mass
        * ((fun e => (((cycleLatticeBasis n hn 0
            : ↥(cycleGraph n hn).cycleLattice) : Fin n → ℤ) e : ℝ))
          ⬝ᵥ (fun e => (((cycleLatticeBasis n hn 0
              : ↥(cycleGraph n hn).cycleLattice) : Fin n → ℤ) e : ℝ))) := by
  rw [cycleMatter_pairing, cycleMatter_mass, cycleFullCycle_normSq]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  norm_num
  field_simp

end CycleWitness

end Meno
