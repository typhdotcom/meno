import Meno.PeriodHarmonic

/-! # The Intrinsic Harmonic Energy (C4)

**Harmonic theory for every finite graph, on the intrinsic classes.**
The presentation is a lattice basis
`B : Module.Basis (Fin n) ℤ G.cycleLattice` (review #5, finding 2);
its **priced Gram data** `basisGramData B` is the inverse of the
derived unit-edge chain Gram (review #5, finding 3 — the canonical
pricing, with nothing stored). `IncidenceGraph.harmonicEnergy` assigns
to each class of `H¹(G;ℤ) = (G.E → ℤ) ⧸ range ∂ᵀℤ` the energy of its
harmonic representative — defined through the fundamental basis, and
computed by **every** basis (`energy_eq_harmonicEnergy`,
`basisGramData_energy_latticeQuot`).

The load-bearing characterization (`periods_eq_cast_iff`): a real
cochain has the periods of an integer cochain `τ` — against *any*
basis — iff it is `τ̂ + grad f` for some potential. Realizing a class
is basis-independent, so the variational sets coincide, and
`IsLeast.unique` transports the energies. No coordinate transport, no
`GL(r,ℤ)` matrices in the proof.

Delivered (C4 acceptance):

* `harmonicEnergy` — basis-free by construction on the intrinsic
  quotient; basis-independent by `energy_eq_harmonicEnergy`.
* `harmonicEnergy_isLeast` — the variational identity for every
  finite graph: the class energy is the least cochain energy among
  realizers, attained.
* `harmonicEnergy_pos` — nonzero classes have positive energy: the
  matter inequality, intrinsic (the C6 bridge). -/

namespace Meno

open scoped BigOperators
open Matrix

universe u v

namespace IncidenceGraph

variable (G : IncidenceGraph.{u, v})
variable {n : ℕ} (B : Module.Basis (Fin n) ℤ G.cycleLattice)

/-- **The priced Gram data of a lattice basis**: the inverse of the
derived unit-edge chain Gram, through the Phase-20 builder — with the
variational identity as a theorem
(`HarmonicGramData.ofCycles_energy_isLeast`). Nothing is stored: the
Gram and its positivity are theorems of the basis (review #5,
finding 3). -/
noncomputable def basisGramData : HarmonicGramData G.V :=
  HarmonicGramData.ofCycles (G.cyclesR B) (G.gramOf_cyclesR_posDef B)

/-- Casting an integer cochain's periods: `⟨τ̂, ĉⱼ⟩ = ⟨τ, cⱼ⟩` as
reals. -/
theorem cast_periods (τ : G.E → ℤ) (j : Fin n) :
    (fun e => ((τ e : ℤ) : ℝ)) ⬝ᵥ G.cyclesR B j
      = ((τ ⬝ᵥ G.cyclesZ B j : ℤ) : ℝ) := by
  show ∑ e, ((τ e : ℤ) : ℝ) * G.cyclesR B j e
    = ((∑ e, τ e * G.cyclesZ B j e : ℤ) : ℝ)
  push_cast
  rfl

/-- **Realizing is basis-independent**: a real cochain has the periods
of the integer cochain `τ` against `B`'s basis iff it is `τ̂ + grad f`
— a condition with no basis in it. -/
theorem periods_eq_cast_iff (τ : G.E → ℤ) (ω : G.E → ℝ) :
    (∀ j, ω ⬝ᵥ G.cyclesR B j = ((τ ⬝ᵥ G.cyclesZ B j : ℤ) : ℝ))
      ↔ ∃ f : G.V → ℝ, ω = (fun e => ((τ e : ℤ) : ℝ)) + G.grad f := by
  constructor
  · intro hper
    have hzero : ∀ j,
        (ω - fun e => ((τ e : ℤ) : ℝ)) ⬝ᵥ G.cyclesR B j = 0 := by
      intro j
      rw [sub_dotProduct, hper j, G.cast_periods B τ j]
      ring
    obtain ⟨f, hf⟩ :=
      (G.period_eq_zero_iff_exists_grad B _).mp hzero
    refine ⟨f, ?_⟩
    rw [hf]
    funext e
    show ω e = ((τ e : ℤ) : ℝ) + (ω e - ((τ e : ℤ) : ℝ))
    ring
  · rintro ⟨f, rfl⟩
    intro j
    rw [add_dotProduct, G.cast_periods B τ j, G.grad_period B f j]
    ring

/-- Any basis's energy at the periods of `τ` is the least energy over
the basis-free realizer set `{τ̂ + grad f}`. -/
theorem isLeast_gradShift (τ : G.E → ℤ) :
    IsLeast {E : ℝ | ∃ ω : G.E → ℝ,
        (∃ f : G.V → ℝ, ω = (fun e => ((τ e : ℤ) : ℝ)) + G.grad f)
          ∧ E = ω ⬝ᵥ ω}
      ((G.basisGramData B).energy (fun j => τ ⬝ᵥ G.cyclesZ B j)) := by
  have h := HarmonicGramData.ofCycles_energy_isLeast (V := G.V)
    (G.cyclesR B) (G.gramOf_cyclesR_posDef B)
    (fun j => τ ⬝ᵥ G.cyclesZ B j)
  have hset : {E : ℝ | ∃ ω : G.E → ℝ,
      (∀ j, ω ⬝ᵥ G.cyclesR B j
        = (((fun j => τ ⬝ᵥ G.cyclesZ B j) j : ℤ) : ℝ)) ∧ E = ω ⬝ᵥ ω}
      = {E : ℝ | ∃ ω : G.E → ℝ,
      (∃ f : G.V → ℝ, ω = (fun e => ((τ e : ℤ) : ℝ)) + G.grad f)
        ∧ E = ω ⬝ᵥ ω} := by
    ext E
    constructor
    · rintro ⟨ω, hω, rfl⟩
      exact ⟨ω, (G.periods_eq_cast_iff B τ ω).mp hω, rfl⟩
    · rintro ⟨ω, hω, rfl⟩
      exact ⟨ω, (G.periods_eq_cast_iff B τ ω).mpr hω, rfl⟩
  rw [hset] at h
  exact h

/-- **The intrinsic harmonic energy** of an integer cohomology class
(C4): defined through the fundamental basis; every basis computes it
(`energy_eq_harmonicEnergy`). -/
noncomputable def harmonicEnergy
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) : ℝ :=
  (G.basisGramData G.cycleBasis).energy (G.h1QuotEquiv κ)

/-- **The variational identity for every finite graph** (C4
acceptance): the class energy is the least cochain energy among
realizers of the class's periods — attained. -/
theorem harmonicEnergy_isLeast
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :
    IsLeast {E : ℝ | ∃ ω : G.E → ℝ,
        (∀ j, ω ⬝ᵥ G.fundCyclesR j = ((G.h1QuotEquiv κ j : ℤ) : ℝ))
          ∧ E = ω ⬝ᵥ ω}
      (G.harmonicEnergy κ) :=
  HarmonicGramData.ofCycles_energy_isLeast (V := G.V) G.fundCyclesR
    (G.gramOf_cyclesR_posDef G.cycleBasis) (G.h1QuotEquiv κ)

/-- **Every basis computes the intrinsic energy** (C4's basis-freeness,
delivered variationally): the energy any lattice basis assigns to the
periods of `τ` is the harmonic energy of `τ`'s class. -/
theorem energy_eq_harmonicEnergy (τ : G.E → ℤ) :
    (G.basisGramData B).energy (fun j => τ ⬝ᵥ G.cyclesZ B j)
      = G.harmonicEnergy (Submodule.Quotient.mk τ) := by
  have h1 := G.isLeast_gradShift B τ
  have h2 := G.isLeast_gradShift G.cycleBasis τ
  have hval := h1.unique h2
  rw [hval]
  show (G.basisGramData G.cycleBasis).energy
      (fun j => τ ⬝ᵥ G.cyclesZ G.cycleBasis j)
    = (G.basisGramData G.cycleBasis).energy
      (G.h1QuotEquiv (Submodule.Quotient.mk τ))
  rw [G.h1QuotEquiv_mk τ]
  rfl

/-- **The chart identity**: any basis's Gram energy at a class's
keystone coordinates is the intrinsic harmonic energy — the engine of
`MatterSector.mass_chart`. -/
theorem basisGramData_energy_latticeQuot
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :
    (G.basisGramData B).energy (G.latticeQuotEquiv B κ)
      = G.harmonicEnergy κ := by
  obtain ⟨τ, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  rw [G.latticeQuotEquiv_mk B τ]
  exact G.energy_eq_harmonicEnergy B τ

/-- **Nonzero classes have positive energy** — the matter inequality,
intrinsic (the C6 bridge). -/
theorem harmonicEnergy_pos
    {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)} (hκ : κ ≠ 0) :
    0 < G.harmonicEnergy κ :=
  (G.basisGramData G.cycleBasis).energy_pos_of_ne_zero
    (G.h1QuotEquiv κ)
    (fun h0 => hκ (G.h1QuotEquiv.injective (h0.trans (map_zero _).symm)))

/-- The zero class has zero harmonic energy — the vacuum sector of the
intrinsic carrier (`classSectorAction`, `Meno/BasisIndependence.lean`). -/
theorem harmonicEnergy_zero : G.harmonicEnergy 0 = 0 := by
  show (G.basisGramData G.cycleBasis).energy (G.h1QuotEquiv 0) = 0
  rw [map_zero]
  exact (G.basisGramData G.cycleBasis).energy_zero

/-- The harmonic energy is nonnegative on every class. -/
theorem harmonicEnergy_nonneg
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :
    0 ≤ G.harmonicEnergy κ := by
  have h := (G.basisGramData G.cycleBasis).toQuadraticAction.energy_nonneg
    (G.h1QuotEquiv κ)
  rwa [(G.basisGramData G.cycleBasis).toQuadraticAction_energy] at h

end IncidenceGraph

end Meno
