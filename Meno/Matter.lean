import Meno.CyclePresentation

/-! # Matter: nonzero period classes over a cycle presentation

**Cohomological formulation** (the Phase 17 H¹ decision, executed in
Phase 22; this file replaces the old homology-flavored
`MatterHomology.lean`). A matter sector is a nonzero *integer period
class* against the chosen cycle basis of a concrete graph presentation
— not an abstract coordinate vector over bare matrix data.

Everything the old structure stored as fields is now a theorem:

* `mass_pos` — positive mass, from positive-definiteness (never stored
  data; every nonzero class has it).
* `mass_isLeast` — the mass is the *least* cochain energy at the
  prescribed periods (the variational identity, via the Phase-20
  builder).
* `not_gradient` — **matter is trapped paradox**: *every* cochain
  realizing a nonzero period class admits no potential. Locally
  consistent, globally unsatisfiable. Generic, by discrete Stokes.
* `annihilation` — binding a sector against its inverse releases the
  pair's entire rest mass. This is algebraic cancellation inside one
  period lattice; the *geometric* `binding_kills_matter` (an ambient
  space change killing a class under an induced map) remains open
  (PLAN, Goal 7 amendment).

**Basis independence** (Phase 23): the label `k ∈ ℤ^r` is relative to
the presentation's cycle basis, but nothing physical depends on the
choice — `MatterSector.rebaseEquiv` bijects matter sectors across any
unimodular change of basis preserving mass, and the partition function
is invariant outright (`CyclePresentation.rebase_partFn`). -/

namespace Meno

open scoped BigOperators

universe u v

variable {V : Type u} {ι : Type v} [Fintype V] [Fintype ι] [DecidableEq V]

/-- A matter sector over the cycle presentation `P`: a nonzero integer
period class against `P`'s chosen cycle basis. -/
def MatterSector (P : CyclePresentation V ι) :=
  {k : Fin P.r → ℤ // k ≠ 0}

namespace MatterSector

variable {P : CyclePresentation V ι} (m : MatterSector P)

/-- The mass of a matter sector: the Gram energy of its period class
(equivalently, by `mass_isLeast`, the least cochain energy at these
periods). -/
noncomputable def mass : ℝ := P.toGramData.energy m.val

/-- Matter has positive mass — a theorem from positive-definiteness,
not stored data. -/
theorem mass_pos : 0 < m.mass :=
  P.toGramData.energy_pos_of_ne_zero m.val m.prop

/-- **The variational identity**: the mass is the least energy among
real cochains with the sector's periods — attained. -/
theorem mass_isLeast :
    IsLeast {E : ℝ | ∃ ω : ι → ℝ,
        (∀ j, ω ⬝ᵥ P.cycles j = (m.val j : ℝ)) ∧ E = ω ⬝ᵥ ω} m.mass :=
  HarmonicGramData.ofCycles_energy_isLeast (V := V) P.cycles P.gram_posDef m.val

/-- **Matter is trapped paradox**: *every* cochain realizing a nonzero
period class — not merely the least-energy representative — admits no
potential. The constraint pattern is locally consistent everywhere and
globally unsatisfiable. -/
theorem not_gradient (ω : ι → ℝ)
    (hω : ∀ j, ω ⬝ᵥ P.cycles j = (m.val j : ℝ)) :
    ¬ ∃ f : V → ℝ, P.grad f = ω := by
  rintro ⟨f, hf⟩
  apply m.prop
  funext j
  show m.val j = 0
  have h0 : ω ⬝ᵥ P.cycles j = 0 := by
    rw [← hf]
    exact P.grad_period f j
  have hj := (hω j).symm.trans h0
  exact_mod_cast hj

/-- Antimatter: the inverse period class. -/
def neg : MatterSector P := ⟨-m.val, neg_ne_zero.mpr m.prop⟩

/-- **Annihilation**: binding a sector against its antimatter releases
the pair's entire rest mass — twice the sector's own. -/
theorem annihilation :
    P.toGramData.bindingEnergy m.val m.neg.val = 2 * m.mass :=
  P.toGramData.bindingEnergy_neg_self m.val

/-! ### Unimodular transport: matter does not depend on the basis label -/

variable (U : Matrix (Fin P.r) (Fin P.r) ℤ) (hU : IsUnit U.det)

/-- **Matter is basis-independent**: a unimodular change of cycle
basis bijects matter sectors, relabeling `k ↦ Uk`. -/
noncomputable def rebaseEquiv :
    MatterSector P ≃ MatterSector (P.rebase U hU) :=
  Equiv.subtypeEquiv (mulVecEquiv U hU) fun k => not_congr (Iff.intro
    (fun h => by rw [h]; exact Matrix.mulVec_zero U)
    (fun h => (mulVecEquiv U hU).injective
      (h.trans (Matrix.mulVec_zero U).symm)))

/-- Transport preserves mass: the relabeled sector weighs the same. -/
theorem rebaseEquiv_mass (m : MatterSector P) :
    ((rebaseEquiv U hU) m).mass = m.mass :=
  P.rebase_energy U hU m.val

end MatterSector

/-- **Matter exists** wherever the presentation has at least one basis
cycle: nontrivial topology forces matter. -/
theorem exists_matter (P : CyclePresentation V ι) (hr : 0 < P.r) :
    Nonempty (MatterSector P) := by
  refine ⟨⟨Pi.single ⟨0, hr⟩ 1, ?_⟩⟩
  intro h
  have h0 := congrFun h ⟨0, hr⟩
  simp at h0

end Meno
