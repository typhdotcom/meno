import Meno.Matter

/-! # The Binding Sign Criterion (G6)

The binding face of the obstruction program (PLAN, G6). At `b₁ = 2`
the priced Gram is the inverse chain Gram (the standing
`basisGramData_gram`), so the two-by-two inverse gives the **closed
form**: the interaction of the two unit sectors is `−⟨c₁,c₂⟩ / det`,
their binding energy is `2⟨c₁,c₂⟩ / det`, and the chain determinant
is positive (`ofCycles_interaction_fin_two`,
`ofCycles_bindingEnergy_fin_two`).

* **The exact law / the iff** (`binding_attractive_iff`): binding is
  attraction **exactly when the cycles overlap with consistent
  orientation** — `0 < bindingEnergyClass ↔ 0 < ⟨c₁, c₂⟩`.
* **The impossibility**: with positive overlap there is no
  non-attractive joint sector — the sign is forced by topology, not
  by choice of basis. Invariance under the unimodular action is part
  of the statement: `bindingEnergyClass` is defined on the intrinsic
  classes through `harmonicEnergy`, and **every** basis chart
  computes it (`bindingEnergyClass_chart`).
* **The strictness witness** is the theta graph
  (`Meno/ThetaHarmonic.lean`): `⟨c₁,c₂⟩ = 2`, `det = 12` —
  `theta_interaction` and `theta_binding_attractive` are re-derived
  as instances of the closed form (demotion, PLAN rule 3).
* **The boundary witness** (`wedge_binding_zero`): the wedge's basis
  cycles share no edge, the overlap is zero — disjoint matter does
  not bind. -/

namespace Meno

open scoped BigOperators
open Matrix

universe u v

/-! ## The closed form at rank two -/

section ClosedForm

variable {V : Type u} {ι : Type*} [Fintype ι]

/-- The chain determinant of a positive-definite two-cycle family is
positive. -/
theorem gramOf_det_pos_fin_two (c : Fin 2 → ι → ℝ)
    (hC : (gramOf c).PosDef) : 0 < (gramOf c).det :=
  hC.det_pos

/-- **The interaction closed form at rank two**: the priced Gram is
the inverse chain Gram, so the unit sectors interact with strength
`−⟨c₁,c₂⟩ / det`. -/
theorem ofCycles_interaction_fin_two (c : Fin 2 → ι → ℝ)
    (hC : (gramOf c).PosDef) :
    (HarmonicGramData.ofCycles (V := V) c hC).interaction ![1, 0] ![0, 1]
      = -(c 0 ⬝ᵥ c 1) / (gramOf c).det := by
  have h1 : (HarmonicGramData.ofCycles (V := V) c hC).interaction
      ![1, 0] ![0, 1] = (gramOf c)⁻¹ 0 1 := by
    show ∑ i, ∑ j, (gramOf c)⁻¹ i j
        * ((![1, 0] : Fin 2 → ℤ) i : ℝ) * ((![0, 1] : Fin 2 → ℤ) j : ℝ)
      = (gramOf c)⁻¹ 0 1
    norm_num [Fin.sum_univ_two]
  rw [h1, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']
  show (gramOf c).det⁻¹
      * (!![gramOf c 1 1, -(gramOf c 0 1); -(gramOf c 1 0), gramOf c 0 0]
          0 1) = -(c 0 ⬝ᵥ c 1) / (gramOf c).det
  norm_num
  rw [show gramOf c 0 1 = c 0 ⬝ᵥ c 1 from rfl]
  ring

/-- **The binding closed form at rank two**: the unit sectors bind
with energy `2⟨c₁,c₂⟩ / det`. -/
theorem ofCycles_bindingEnergy_fin_two (c : Fin 2 → ι → ℝ)
    (hC : (gramOf c).PosDef) :
    (HarmonicGramData.ofCycles (V := V) c hC).bindingEnergy ![1, 0] ![0, 1]
      = 2 * (c 0 ⬝ᵥ c 1) / (gramOf c).det := by
  rw [HarmonicGramData.bindingEnergy_eq, ofCycles_interaction_fin_two]
  ring

/-- **The sign criterion at rank two**: the unit sectors bind
attractively iff the two cycles overlap positively. -/
theorem ofCycles_binding_attractive_iff_fin_two (c : Fin 2 → ι → ℝ)
    (hC : (gramOf c).PosDef) :
    0 < (HarmonicGramData.ofCycles (V := V) c hC).bindingEnergy
        ![1, 0] ![0, 1]
      ↔ 0 < c 0 ⬝ᵥ c 1 := by
  rw [ofCycles_bindingEnergy_fin_two,
    lt_div_iff₀ (gramOf_det_pos_fin_two c hC), zero_mul]
  constructor
  · intro h; linarith
  · intro h; linarith

end ClosedForm

/-! ## The intrinsic binding energy and its charts -/

namespace IncidenceGraph

variable (G : IncidenceGraph.{u, v})

/-- **The intrinsic binding energy** of two `H¹` classes: what joint
minimization releases, defined through the basis-free
`harmonicEnergy` — invariant under the unimodular action by
construction. -/
noncomputable def bindingEnergyClass
    (κ₁ κ₂ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) : ℝ :=
  G.harmonicEnergy κ₁ + G.harmonicEnergy κ₂ - G.harmonicEnergy (κ₁ + κ₂)

/-- **Every basis chart computes the intrinsic binding** — the
unimodular-invariance half of the sign criterion: the coordinate
binding energy of any lattice basis equals the intrinsic one. -/
theorem bindingEnergyClass_chart {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice)
    (κ₁ κ₂ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :
    G.bindingEnergyClass κ₁ κ₂
      = (G.basisGramData B).bindingEnergy
          (G.latticeQuotEquiv B κ₁) (G.latticeQuotEquiv B κ₂) := by
  show G.harmonicEnergy κ₁ + G.harmonicEnergy κ₂
      - G.harmonicEnergy (κ₁ + κ₂)
    = (G.basisGramData B).energy (G.latticeQuotEquiv B κ₁)
      + (G.basisGramData B).energy (G.latticeQuotEquiv B κ₂)
      - (G.basisGramData B).energy
          (G.latticeQuotEquiv B κ₁ + G.latticeQuotEquiv B κ₂)
  rw [G.basisGramData_energy_latticeQuot B κ₁,
    G.basisGramData_energy_latticeQuot B κ₂,
    show G.latticeQuotEquiv B κ₁ + G.latticeQuotEquiv B κ₂
        = G.latticeQuotEquiv B (κ₁ + κ₂) from (map_add _ κ₁ κ₂).symm,
    G.basisGramData_energy_latticeQuot B (κ₁ + κ₂)]

/-- **THE BINDING SIGN CRITERION** (G6, the iff): at `b₁ = 2`, the
sectors of the two basis cycles bind attractively **iff** the cycles
overlap with consistent orientation — `0 < ⟨c₁, c₂⟩`. The left side
is intrinsic (`bindingEnergyClass`), so the sign is forced by
topology, not by choice of basis: with positive overlap there is no
non-attractive joint sector in any chart. -/
theorem binding_attractive_iff
    (B : Module.Basis (Fin 2) ℤ G.cycleLattice) :
    0 < G.bindingEnergyClass (G.h1Basis B 0) (G.h1Basis B 1)
      ↔ 0 < G.cyclesR B 0 ⬝ᵥ G.cyclesR B 1 := by
  have hsingle₀ : (Pi.single (0 : Fin 2) (1 : ℤ)) = ![1, 0] := by
    funext i
    fin_cases i <;> rfl
  have hsingle₁ : (Pi.single (1 : Fin 2) (1 : ℤ)) = ![0, 1] := by
    funext i
    fin_cases i <;> rfl
  rw [G.bindingEnergyClass_chart B, G.latticeQuotEquiv_h1Basis B 0,
    G.latticeQuotEquiv_h1Basis B 1, hsingle₀, hsingle₁]
  exact ofCycles_binding_attractive_iff_fin_two (G.cyclesR B)
    (G.gramOf_cyclesR_posDef B)

end IncidenceGraph

/-! ## The boundary witness: the wedge does not bind -/

/-- **Disjoint matter does not bind** (G6 boundary): the wedge's two
basis cycles share no edge — the overlap is zero, so the binding
energy vanishes. -/
theorem wedge_binding_zero (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    (wedgePeriodData n₁ n₂ h₁ h₂).bindingEnergy ![1, 0] ![0, 1] = 0 := by
  show (HarmonicGramData.ofCycles (V := Fin n₁ ⊕ Fin n₂)
      (wedgeCycles n₁ n₂) (gramOf_wedgeCycles_posDef n₁ n₂ h₁ h₂)).bindingEnergy
      ![1, 0] ![0, 1] = 0
  rw [ofCycles_bindingEnergy_fin_two]
  rw [show wedgeCycles n₁ n₂ 0 ⬝ᵥ wedgeCycles n₁ n₂ 1
      = gramOf (wedgeCycles n₁ n₂) 0 1 from rfl,
    gramOf_wedgeCycles]
  norm_num

end Meno
