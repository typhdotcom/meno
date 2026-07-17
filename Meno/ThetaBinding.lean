import Meno.Binding
import Meno.ThetaHarmonic
import Meno.GraphInstances

/-! # Binding at the Theta Graph (C7's concrete consumer)

The theta graph with its first basis cycle filled — the generic
2-complex theory of `Meno/Binding.lean` instantiated: the `(1,0)`
sector (`thetaMatter`, mass `1/3`) dies, `b₁` drops `2 → 1`, and the
spectrum loses at least the killed sector's Boltzmann weight
`exp(−1/3)`. Split from `Meno/Binding.lean` (review #3) so the
generic binding layer does not import the concrete graphs or the
information layer. -/

namespace Meno

open scoped BigOperators

section Theta

/-- The first theta basis cycle is a cycle. -/
theorem thetaCycle₁_mem :
    (![1, 1, 0, 0, -1, -1] : Fin 6 → ℤ) ∈ thetaGraph.cycleLattice :=
  thetaCyclesZ_mem 0

/-- **The theta graph with its first cycle filled.** -/
noncomputable def thetaFilled : TwoComplex.{0, 0, 0} thetaGraph :=
  thetaGraph.attach ![1, 1, 0, 0, -1, -1] thetaCycle₁_mem

/-- The theta matter wraps the filled cycle once. -/
theorem thetaMatter_pairing :
    thetaGraph.classPairing ![1, 1, 0, 0, -1, -1] thetaCycle₁_mem
      thetaMatter.val = 1 := by
  show (![1, 0, 0, 0, 0, 0] : Fin 6 → ℤ) ⬝ᵥ ![1, 1, 0, 0, -1, -1] = 1
  decide

/-- **The theta matter dies**: no class of the filled complex
restricts to it. The `(1,0)` sector wrapped the cycle the face
filled; its paradox is resolved, and it ceases to exist. -/
theorem theta_binding_kills :
    ¬ ∃ κ' : thetaFilled.h1, thetaFilled.restrict κ' = thetaMatter.val :=
  thetaFilled.binding_kills_matter thetaMatter PUnit.unit (by
    show thetaGraph.classPairing ![1, 1, 0, 0, -1, -1] thetaCycle₁_mem
      thetaMatter.val ≠ 0
    rw [thetaMatter_pairing]
    exact one_ne_zero)

/-- Filling the first cycle drops `b₁` from `2` to `1`. -/
theorem theta_attach_finrank :
    Module.finrank ℤ thetaFilled.h1Homology = 1 := by
  have h := finrank_attach_h1Homology (G := thetaGraph)
    ![1, 1, 0, 0, -1, -1] thetaCycle₁_mem ![1, 0, 0, 0, 0, 0]
    (by decide)
  rw [thetaGraph_b1] at h
  exact h

/-- **The theta removed weight**: filling the cycle the `1/3`-mass
sector wraps removes at least `exp(−1/3)` from the spectrum — the
sector's entire Boltzmann weight. -/
theorem theta_removed_weight :
    thetaFilled.partFn + Real.exp (-(1/3 : ℝ))
      ≤ thetaGraph.classPartFn := by
  have h := thetaFilled.attach_partFn_add_le thetaMatter PUnit.unit (by
    show thetaGraph.classPairing ![1, 1, 0, 0, -1, -1] thetaCycle₁_mem
      thetaMatter.val ≠ 0
    rw [thetaMatter_pairing]
    exact one_ne_zero)
  rwa [thetaMatter_mass] at h

end Theta

end Meno
