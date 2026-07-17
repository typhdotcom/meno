import Meno.BasisIndependence

/-! # The Intrinsic Harmonic Energy (C4)

**Harmonic theory for every finite graph, on the intrinsic classes.**
`IncidenceGraph.harmonicEnergy` assigns to each class of
`H¹(G;ℤ) = (G.E → ℤ) ⧸ range ∂ᵀℤ` the energy of its harmonic
representative — defined through the fundamental presentation, and
computed by **every** presentation (`energy_eq_harmonicEnergy`).

The load-bearing characterization (`periods_eq_cast_iff`): a real
cochain has the periods of an integer cochain `τ` — against *any*
presentation's basis — iff it is `τ̂ + grad f` for some potential.
Realizing a class is presentation-independent, so the variational sets
coincide, and `IsLeast.unique` transports the energies. No coordinate
transport, no `GL(r,ℤ)` matrices in the proof.

Delivered (C4 acceptance):

* `harmonicEnergy` — basis-free by construction on the intrinsic
  quotient; presentation-independent by `energy_eq_harmonicEnergy`.
* `harmonicEnergy_isLeast` — the variational identity for every
  finite graph: the class energy is the least cochain energy among
  realizers, attained.
* `cochainQuotEquivR` / `finrank_cochainQuotR` — real cochains modulo
  gradients are `ℝ^{b₁}`, for every finite graph.
* `harmonicEnergy_pos` — nonzero classes have positive energy: the
  matter inequality, now intrinsic (the C6 bridge). -/

namespace Meno

open scoped BigOperators
open Matrix

universe u v

variable {G : IncidenceGraph.{u, v}}

private lemma cast_dotProduct {ι : Type*} [Fintype ι] (x y : ι → ℤ) :
    ((x ⬝ᵥ y : ℤ) : ℝ) = (fun e => (x e : ℝ)) ⬝ᵥ (fun e => (y e : ℝ)) := by
  show ((∑ e, x e * y e : ℤ) : ℝ) = ∑ e, (x e : ℝ) * (y e : ℝ)
  push_cast
  rfl

namespace IntegralCyclePresentation

variable (Q : IntegralCyclePresentation G)

/-- Casting an integer cochain's periods: `⟨τ̂, cⱼ⟩ = ⟨τ, cⱼℤ⟩` as
reals. -/
theorem cast_periods (τ : G.E → ℤ) (j : Fin Q.r) :
    (fun e => ((τ e : ℤ) : ℝ)) ⬝ᵥ Q.cycles j
      = ((τ ⬝ᵥ Q.cyclesZ j : ℤ) : ℝ) := by
  rw [cast_dotProduct]
  refine Finset.sum_congr rfl fun e _ => ?_
  show ((τ e : ℤ) : ℝ) * Q.cycles j e
    = ((τ e : ℤ) : ℝ) * ((Q.cyclesZ j e : ℤ) : ℝ)
  rw [Q.cyclesZ_cast]

/-- **Realizing is presentation-independent**: a real cochain has the
periods of the integer cochain `τ` against `Q`'s basis iff it is
`τ̂ + grad f` — a condition with no presentation in it. -/
theorem periods_eq_cast_iff (τ : G.E → ℤ) (ω : G.E → ℝ) :
    (∀ j, ω ⬝ᵥ Q.cycles j = ((τ ⬝ᵥ Q.cyclesZ j : ℤ) : ℝ))
      ↔ ∃ f : G.V → ℝ, ω = (fun e => ((τ e : ℤ) : ℝ)) + G.grad f := by
  constructor
  · intro hper
    have hzero : ∀ j,
        (ω - fun e => ((τ e : ℤ) : ℝ)) ⬝ᵥ Q.cycles j = 0 := by
      intro j
      rw [sub_dotProduct, hper j, Q.cast_periods τ j]
      ring
    obtain ⟨f, hf⟩ :=
      (Q.toCyclePresentation.period_eq_zero_iff_exists_grad _).mp hzero
    refine ⟨f, ?_⟩
    rw [hf]
    funext e
    show ω e = ((τ e : ℤ) : ℝ) + (ω e - ((τ e : ℤ) : ℝ))
    ring
  · rintro ⟨f, rfl⟩
    intro j
    rw [add_dotProduct, Q.cast_periods τ j,
      Q.toCyclePresentation.grad_period f j]
    ring

/-- Any presentation's energy at the periods of `τ` is the least
energy over the presentation-free realizer set `{τ̂ + grad f}`. -/
theorem isLeast_gradShift (τ : G.E → ℤ) :
    IsLeast {E : ℝ | ∃ ω : G.E → ℝ,
        (∃ f : G.V → ℝ, ω = (fun e => ((τ e : ℤ) : ℝ)) + G.grad f)
          ∧ E = ω ⬝ᵥ ω}
      (Q.toGramData.energy (fun j => τ ⬝ᵥ Q.cyclesZ j)) := by
  have h := HarmonicGramData.ofCycles_energy_isLeast (V := G.V)
    Q.cycles Q.gram_posDef (fun j => τ ⬝ᵥ Q.cyclesZ j)
  have hset : {E : ℝ | ∃ ω : G.E → ℝ,
      (∀ j, ω ⬝ᵥ Q.cycles j
        = (((fun j => τ ⬝ᵥ Q.cyclesZ j) j : ℤ) : ℝ)) ∧ E = ω ⬝ᵥ ω}
      = {E : ℝ | ∃ ω : G.E → ℝ,
      (∃ f : G.V → ℝ, ω = (fun e => ((τ e : ℤ) : ℝ)) + G.grad f)
        ∧ E = ω ⬝ᵥ ω} := by
    ext E
    constructor
    · rintro ⟨ω, hω, rfl⟩
      exact ⟨ω, (Q.periods_eq_cast_iff τ ω).mp hω, rfl⟩
    · rintro ⟨ω, hω, rfl⟩
      exact ⟨ω, (Q.periods_eq_cast_iff τ ω).mpr hω, rfl⟩
  rw [hset] at h
  exact h

end IntegralCyclePresentation

namespace IncidenceGraph

variable (G : IncidenceGraph.{u, v})

/-- The intrinsic `H¹` coordinates of a class: applied form of
`h1QuotEquiv` on representatives. -/
theorem h1QuotEquiv_mk (τ : G.E → ℤ) :
    G.h1QuotEquiv (Submodule.Quotient.mk τ)
      = fun j => τ ⬝ᵥ G.fundamentalPresentation.cyclesZ j := rfl

/-- **The intrinsic harmonic energy** of an integer cohomology class
(C4): defined through the fundamental presentation; every
presentation computes it (`energy_eq_harmonicEnergy`). -/
noncomputable def harmonicEnergy
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) : ℝ :=
  G.fundamentalPresentation.toGramData.energy (G.h1QuotEquiv κ)

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
    G.gramOf_fund_posDef (G.h1QuotEquiv κ)

/-- **Every presentation computes the intrinsic energy** (C4's
basis-freeness, delivered variationally): the energy any integral
presentation assigns to the periods of `τ` is the harmonic energy of
`τ`'s class. -/
theorem energy_eq_harmonicEnergy (Q : IntegralCyclePresentation G)
    (τ : G.E → ℤ) :
    Q.toGramData.energy (fun j => τ ⬝ᵥ Q.cyclesZ j)
      = G.harmonicEnergy (Submodule.Quotient.mk τ) := by
  have h1 := Q.isLeast_gradShift τ
  have h2 := G.fundamentalPresentation.isLeast_gradShift τ
  have hval := h1.unique h2
  rw [hval]
  show G.fundamentalPresentation.toGramData.energy
      (fun j => τ ⬝ᵥ G.fundamentalPresentation.cyclesZ j)
    = G.fundamentalPresentation.toGramData.energy
      (G.h1QuotEquiv (Submodule.Quotient.mk τ))
  rw [G.h1QuotEquiv_mk τ]
  rfl

/-- **Nonzero classes have positive energy** — the matter inequality,
intrinsic (the C6 bridge). -/
theorem harmonicEnergy_pos
    {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)} (hκ : κ ≠ 0) :
    0 < G.harmonicEnergy κ :=
  G.fundamentalPresentation.toGramData.energy_pos_of_ne_zero
    (G.h1QuotEquiv κ)
    (fun h0 => hκ (G.h1QuotEquiv.injective (h0.trans (map_zero _).symm)))

/-- Real cochains modulo gradients are `ℝ^{b₁}` — for every finite
graph (C4 acceptance). -/
noncomputable def cochainQuotEquivR :
    ((G.E → ℝ) ⧸ LinearMap.range (G.gradLin ℝ)) ≃ₗ[ℝ] (Fin G.b1 → ℝ) :=
  G.fundamentalPresentation.toCyclePresentation.cochainQuotEquiv

theorem finrank_cochainQuotR :
    Module.finrank ℝ ((G.E → ℝ) ⧸ LinearMap.range (G.gradLin ℝ))
      = G.b1 :=
  G.fundamentalPresentation.toCyclePresentation.finrank_cochainQuot

end IncidenceGraph

end Meno
