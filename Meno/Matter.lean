import Meno.BasisIndependence

/-! # Matter: nonzero cohomology classes

**A matter sector is a nonzero class of `H¹(G;ℤ)`** — the intrinsic
quotient `(G.E → ℤ) ⧸ range ∂ᵀℤ` — with every physical attribute a
theorem through the graph-level harmonic theory:

* `mass` — the intrinsic harmonic energy of the class
  (`IncidenceGraph.harmonicEnergy`); every presentation computes it
  (`mass_chart`, via `energy_eq_harmonicEnergy`).
* `mass_pos` — positive mass from positive-definiteness
  (`harmonicEnergy_pos`); never stored data.
* `mass_isLeast` — the variational identity: mass is the least
  cochain energy among realizers, attained.
* `not_gradient` — **matter is trapped paradox**: every real cochain
  realizing a nonzero class admits no potential.
* `annihilation` — binding a sector against its inverse releases the
  pair's entire rest mass. Algebraic cancellation inside `H¹`; the
  *geometric* `binding_kills_matter` — an ambient space change killing
  a class under the induced map — is proved in `Meno/Binding.lean`.
* `exists_matter` — nontrivial topology (`0 < b₁`) forces matter.

Coordinates enter only through the keystone equivalences, and
coordinate transport is subsumed by `mass_chart` — any two bases'
charts of the same intrinsic sector weigh the same because both
equal the intrinsic mass. -/

namespace Meno

open scoped BigOperators

universe u v

variable {G : IncidenceGraph.{u, v}}

/-- A matter sector of the graph `G`: a nonzero integer cohomology
class. -/
def MatterSector (G : IncidenceGraph.{u, v}) :=
  {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ) // κ ≠ 0}

namespace MatterSector

variable (m : MatterSector G)

/-- The mass of a matter sector: the intrinsic harmonic energy of its
class. -/
noncomputable def mass : ℝ := G.harmonicEnergy m.val

/-- Matter has positive mass — a theorem from positive-definiteness,
not stored data. -/
theorem mass_pos : 0 < m.mass := G.harmonicEnergy_pos m.prop

/-- **Matter forces topology** (the converse of `exists_matter`):
a matter sector exists only where the graph has cycles — at `b₁ = 0`
the keystone coordinates land in `Fin 0 → ℤ` and every class is
zero. -/
theorem b1_pos (m : MatterSector G) : 0 < G.b1 := by
  rcases Nat.eq_zero_or_pos G.b1 with hb | hb
  · exfalso
    apply m.prop
    apply G.h1QuotEquiv.injective
    rw [map_zero]
    funext j
    exact absurd j.isLt (by omega)
  · exact hb

/-- **The variational identity**: the mass is the least energy among
real cochains realizing the class's periods — attained. -/
theorem mass_isLeast :
    IsLeast {E : ℝ | ∃ ω : G.E → ℝ,
        (∀ j, ω ⬝ᵥ G.fundCyclesR j = ((G.h1QuotEquiv m.val) j : ℝ))
          ∧ E = ω ⬝ᵥ ω} m.mass :=
  G.harmonicEnergy_isLeast m.val

/-- **Every basis computes the mass** (the chart lemma): the energy
any lattice basis assigns to the sector's keystone coordinates is the
intrinsic mass. -/
theorem mass_chart {n : ℕ} (B : Module.Basis (Fin n) ℤ G.cycleLattice) :
    (G.basisGramData B).energy (G.latticeQuotEquiv B m.val) = m.mass :=
  G.basisGramData_energy_latticeQuot B m.val

/-- **Matter is trapped paradox**: *every* real cochain realizing a
nonzero class — not merely the least-energy representative — admits
no potential. Locally consistent, globally unsatisfiable. -/
theorem not_gradient (ω : G.E → ℝ)
    (hω : ∀ j, ω ⬝ᵥ G.fundCyclesR j = ((G.h1QuotEquiv m.val) j : ℝ)) :
    ¬ ∃ f : G.V → ℝ, G.grad f = ω := by
  rintro ⟨f, rfl⟩
  apply m.prop
  apply G.h1QuotEquiv.injective
  rw [map_zero]
  funext j
  have hper := G.grad_period G.cycleBasis f j
  have := (hω j).symm.trans hper
  exact_mod_cast this

/-- Antimatter: the inverse class. -/
def neg : MatterSector G := ⟨-m.val, neg_ne_zero.mpr m.prop⟩

/-- **Annihilation**: binding a sector against its antimatter releases
the pair's entire rest mass — twice the sector's own. Algebraic
cancellation inside `H¹`; the geometric space-changing statement is
`binding_kills_matter`. -/
theorem annihilation :
    (G.basisGramData G.cycleBasis).bindingEnergy
      (G.h1QuotEquiv m.val) (G.h1QuotEquiv m.neg.val) = 2 * m.mass := by
  have hneg : G.h1QuotEquiv m.neg.val = -(G.h1QuotEquiv m.val) := by
    show G.h1QuotEquiv (-m.val) = _
    rw [map_neg]
  rw [hneg]
  exact (G.basisGramData G.cycleBasis).bindingEnergy_neg_self
    (G.h1QuotEquiv m.val)

end MatterSector

/-- **Matter exists** wherever the graph has nontrivial topology:
`0 < b₁` forces a nonzero class. -/
theorem exists_matter (G : IncidenceGraph.{u, v}) (hb : 0 < G.b1) :
    Nonempty (MatterSector G) := by
  refine ⟨⟨G.h1QuotEquiv.symm (Pi.single ⟨0, hb⟩ 1), ?_⟩⟩
  intro h0
  have := congrArg G.h1QuotEquiv h0
  rw [LinearEquiv.apply_symm_apply, map_zero] at this
  have h1 := congrFun this ⟨0, hb⟩
  rw [Pi.single_eq_same] at h1
  exact one_ne_zero h1

end Meno
