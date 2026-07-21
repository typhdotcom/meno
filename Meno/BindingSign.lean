import Meno.Matter

/-! # The Binding Sign Criterion

The binding face of the obstruction program. At `b₁ = 2`
the priced Gram is the inverse chain Gram (the standing
`basisGramData_gram`), so the two-by-two inverse gives the **closed
form**: the interaction of the two unit sectors is `−⟨c₁,c₂⟩ / det`,
their binding energy is `2⟨c₁,c₂⟩ / det`, and the chain determinant
is positive (`ofCycles_interaction_fin_two`,
`ofCycles_bindingEnergy_fin_two`).

* **The exact law / the iff** (`binding_attractive_iff`): binding is
  attraction **exactly when the cycles overlap with consistent
  orientation** — `0 < bindingEnergyClass ↔ 0 < ⟨c₁, c₂⟩`.
* **The law is intrinsic**: at rank two, with positive overlap no
  chart makes the joint sector non-attractive — the sign is forced by
  topology, not by choice of basis. Invariance under the unimodular
  action is part of the `binding_attractive_iff` statement:
  `bindingEnergyClass` is defined on the intrinsic classes through
  `harmonicEnergy`, and **every** basis chart computes it
  (`bindingEnergyClass_chart`).
* **The strictness witness** (`theta_binding_attractive_class`,
  `Meno/ThetaHarmonic.lean`): the intrinsic binding of the theta
  classes is positive — `⟨c₁,c₂⟩ = 2 > 0` forces attraction through
  the criterion's own iff.
* **The boundary witness** (`wedge_binding_zero`): the wedge's basis
  cycles share no edge, the overlap is zero — disjoint matter does
  not bind.
* **The impossibility — beyond rank two the overlap does not decide**
  (`exists_overlap_pos_binding_neg`): the criterion is genuinely a
  rank-two law. At `b₁ = 3` the doubled triangle's first two basis
  cycles overlap positively (`⟨c₀,c₁⟩ = 1`) yet their sectors bind
  with energy `−1/4` — the third cycle screens the overlap. -/

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

/-- **THE BINDING SIGN CRITERION** (the iff): at `b₁ = 2`, the
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

/-- **Disjoint matter does not bind**: the wedge's two
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

/-! ## The impossibility: rank three screens the overlap

The doubled triangle `A→B→C→A` with the edges `A→B` and `C→A`
doubled: `b₁ = 3`, and the three triangles `c₀ = e₁+e₂+f₁`,
`c₁ = e₂+e₃+f₂`, `c₂ = e₁+e₂+e₃` are a lattice basis with chain Gram
`!![3,1,2; 1,3,2; 2,2,3]`. The first two cycles overlap positively —
yet the off-diagonal of the *inverse* Gram is
`(⟨c₀,c₂⟩⟨c₁,c₂⟩ − ⟨c₀,c₁⟩⟨c₂,c₂⟩)/det = (4 − 3)/8 > 0`, so their
sectors repel: both run through the short third cycle with the same
orientation, and the third channel screens the pairwise overlap. At
rank two no mediator exists — the sign criterion is a rank-two law. -/

section Screened

/-- Edge sources in the doubled triangle. -/
def screenedSrc : Fin 5 → Fin 3 := ![0, 1, 2, 2, 0]

/-- Edge targets in the doubled triangle. -/
def screenedTgt : Fin 5 → Fin 3 := ![1, 2, 0, 0, 1]

/-- The doubled triangle as an incidence graph: the triangle
`A→B→C→A` with the edges `A→B` and `C→A` doubled. -/
@[reducible] def screenedTriangle : IncidenceGraph :=
  { V := Fin 3
    E := Fin 5
    src := screenedSrc
    tgt := screenedTgt }

/-- The integral basis cycles: `c₀ = e₁+e₂+f₁`, `c₁ = e₂+e₃+f₂`,
`c₂ = e₁+e₂+e₃`. -/
def screenedCyclesZ : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 1, 0], ![0, 1, 1, 0, 1], ![1, 1, 1, 0, 0]]

/-- The basis cycles, cast to `ℝ`. -/
noncomputable def screenedCycles : Fin 3 → Fin 5 → ℝ :=
  ![![1, 1, 0, 1, 0], ![0, 1, 1, 0, 1], ![1, 1, 1, 0, 0]]

/-- The real cycles are the casts of the integral ones. -/
theorem screenedCycles_eq_cast (i : Fin 3) (e : Fin 5) :
    screenedCycles i e = ((screenedCyclesZ i e : ℤ) : ℝ) := by
  fin_cases i <;> fin_cases e <;> norm_num [screenedCycles, screenedCyclesZ]

/-- The doubled triangle's substrate boundary, in explicit-sum form. -/
theorem screenedTriangle_boundary_eq_sum {R : Type*} [CommRing R]
    (ω : Fin 5 → R) (w : Fin 3) :
    screenedTriangle.boundary ω w
      = ∑ e, ((if screenedTgt e = w then (1 : R) else 0)
        - (if screenedSrc e = w then (1 : R) else 0)) * ω e := rfl

/-- The basis vectors are integral cycles. -/
theorem screenedCyclesZ_mem (i : Fin 3) :
    screenedCyclesZ i ∈ screenedTriangle.cycleLattice := by
  rw [IncidenceGraph.mem_cycleLattice]
  intro w
  rw [screenedTriangle_boundary_eq_sum]
  fin_cases i <;> fin_cases w <;> decide

/-- **Independence of the casts**: read off the flows on the two
private doubled edges (`f₁` carries only `c₀`, `f₂` only `c₁`) and on
the shared edge `e₁` (carrying `c₀` and `c₂`). -/
theorem screened_cast_independent (x : Fin 3 → ℝ)
    (hx : (fun e => ∑ i, x i * ((screenedCyclesZ i e : ℤ) : ℝ)) = 0) :
    x = 0 := by
  have h3 := congrFun hx 3
  have h4 := congrFun hx 4
  have h0 := congrFun hx 0
  simp +decide [screenedCyclesZ, Fin.sum_univ_three] at h3 h4 h0
  have hx0 : x 0 = 0 := by linarith
  have hx1 : x 1 = 0 := by linarith
  have hx2 : x 2 = 0 := by linarith
  funext i
  fin_cases i
  · simpa using hx0
  · simpa using hx1
  · simpa using hx2

/-- **Integral spanning**: flow conservation at the three vertices
forces the coefficients `a = ![ω f₁, ω f₂, ω e₃ − ω f₂]` — the period
lattice is the full integral cycle lattice. -/
theorem screened_integral_spanning (x : Fin 5 → ℤ)
    (hx : x ∈ screenedTriangle.cycleLattice) :
    ∃ a : Fin 3 → ℤ, x = fun e => ∑ i, a i * screenedCyclesZ i e := by
  have h0 := (IncidenceGraph.mem_cycleLattice _ |>.mp hx) 0
  have h1 := (IncidenceGraph.mem_cycleLattice _ |>.mp hx) 1
  have h2 := (IncidenceGraph.mem_cycleLattice _ |>.mp hx) 2
  rw [screenedTriangle_boundary_eq_sum] at h0 h1 h2
  simp +decide [screenedSrc, screenedTgt, Fin.sum_univ_five] at h0 h1 h2
  refine ⟨![x 3, x 4, x 2 - x 4], ?_⟩
  funext e
  fin_cases e <;>
    simp +decide [screenedCyclesZ, Fin.sum_univ_three] <;>
    omega

/-- The doubled triangle's lattice basis, assembled from the raw
facts. -/
noncomputable def screenedLatticeBasis :
    Module.Basis (Fin 3) ℤ screenedTriangle.cycleLattice :=
  screenedTriangle.basisOfCycles screenedCyclesZ screenedCyclesZ_mem
    screened_cast_independent screened_integral_spanning

/-- The assembled basis's integer cycles are the screened cycles. -/
theorem cyclesZ_screenedLatticeBasis :
    screenedTriangle.cyclesZ screenedLatticeBasis = screenedCyclesZ :=
  screenedTriangle.cyclesZ_basisOfCycles _ _ _ _

/-- `b₁ = 3`, through the basis. -/
theorem screenedTriangle_b1 : screenedTriangle.b1 = 3 :=
  (screenedTriangle.card_eq_b1 screenedLatticeBasis).symm

/-- The lattice basis's cast cycles are the screened cycles. -/
theorem cyclesR_screenedLatticeBasis :
    screenedTriangle.cyclesR screenedLatticeBasis = screenedCycles := by
  funext i e
  show ((screenedTriangle.cyclesZ screenedLatticeBasis i e : ℤ) : ℝ)
    = screenedCycles i e
  rw [cyclesZ_screenedLatticeBasis]
  exact (screenedCycles_eq_cast i e).symm

/-- The cycle-chain Gram matrix of the doubled triangle. -/
theorem gramOf_screenedCycles :
    gramOf screenedCycles = !![3, 1, 2; 1, 3, 2; 2, 2, 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [gramOf, dotProduct, screenedCycles, Fin.sum_univ_five] <;>
    norm_num

/-- The inverse chain Gram, in closed form (`det = 8`). -/
theorem screenedGram_inv :
    (!![3, 1, 2; 1, 3, 2; 2, 2, 3] : Matrix (Fin 3) (Fin 3) ℝ)⁻¹
      = !![5/8, 1/8, -(1/2); 1/8, 5/8, -(1/2); -(1/2), -(1/2), 1] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]

/-- The derived priced Gram of the screened basis is the literal
inverse chain Gram. -/
theorem screened_basisGramData_gram :
    (screenedTriangle.basisGramData screenedLatticeBasis).gram
      = !![5/8, 1/8, -(1/2); 1/8, 5/8, -(1/2); -(1/2), -(1/2), 1] := by
  show (gramOf (screenedTriangle.cyclesR screenedLatticeBasis))⁻¹ = _
  rw [cyclesR_screenedLatticeBasis, gramOf_screenedCycles, screenedGram_inv]

/-- The interaction of the two unit sectors is the priced
off-diagonal `1/8` — **positive**, despite the positive overlap. -/
theorem screened_interaction :
    (screenedTriangle.basisGramData screenedLatticeBasis).interaction
      ![1, 0, 0] ![0, 1, 0] = 1 / 8 := by
  show (∑ i : Fin 3, ∑ j : Fin 3,
      (screenedTriangle.basisGramData screenedLatticeBasis).gram i j
        * ((![1, 0, 0] : Fin 3 → ℤ) i : ℝ)
        * ((![0, 1, 0] : Fin 3 → ℤ) j : ℝ)) = 1 / 8
  rw [screened_basisGramData_gram]
  norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]

/-- The first two basis cycles overlap with consistent orientation:
`⟨c₀,c₁⟩ = 1 > 0`. -/
theorem screened_overlap_pos :
    0 < screenedTriangle.cyclesR screenedLatticeBasis 0
        ⬝ᵥ screenedTriangle.cyclesR screenedLatticeBasis 1 := by
  rw [cyclesR_screenedLatticeBasis,
    show screenedCycles 0 ⬝ᵥ screenedCycles 1
      = gramOf screenedCycles 0 1 from rfl,
    gramOf_screenedCycles]
  norm_num

/-- **The intrinsic binding of the overlapping sectors is `−1/4`**:
repulsion at positive overlap — the third cycle screens. -/
theorem screened_binding_repulsive :
    screenedTriangle.bindingEnergyClass
        (screenedTriangle.h1Basis screenedLatticeBasis 0)
        (screenedTriangle.h1Basis screenedLatticeBasis 1) = -(1 / 4) := by
  have hsingle₀ : (Pi.single (0 : Fin 3) (1 : ℤ)) = ![1, 0, 0] := by
    funext i
    fin_cases i <;> rfl
  have hsingle₁ : (Pi.single (1 : Fin 3) (1 : ℤ)) = ![0, 1, 0] := by
    funext i
    fin_cases i <;> rfl
  rw [screenedTriangle.bindingEnergyClass_chart screenedLatticeBasis,
    screenedTriangle.latticeQuotEquiv_h1Basis screenedLatticeBasis 0,
    screenedTriangle.latticeQuotEquiv_h1Basis screenedLatticeBasis 1,
    hsingle₀, hsingle₁, HarmonicGramData.bindingEnergy_eq,
    screened_interaction]
  norm_num

/-- The binding is strictly negative: the sectors repel. -/
theorem screened_binding_neg :
    screenedTriangle.bindingEnergyClass
        (screenedTriangle.h1Basis screenedLatticeBasis 0)
        (screenedTriangle.h1Basis screenedLatticeBasis 1) < 0 := by
  rw [screened_binding_repulsive]
  norm_num

/-- **THE IMPOSSIBILITY**: positive overlap does not force attraction
beyond rank two — at `b₁ = 3` there is a graph and a lattice basis
whose first two cycles overlap with consistent orientation while
their sectors bind repulsively. The sign criterion
(`binding_attractive_iff`) is genuinely a rank-two law. -/
theorem exists_overlap_pos_binding_neg :
    ∃ (G : IncidenceGraph.{0, 0})
      (B : Module.Basis (Fin 3) ℤ G.cycleLattice),
      0 < G.cyclesR B 0 ⬝ᵥ G.cyclesR B 1 ∧
        G.bindingEnergyClass (G.h1Basis B 0) (G.h1Basis B 1) < 0 :=
  ⟨screenedTriangle, screenedLatticeBasis, screened_overlap_pos,
    screened_binding_neg⟩

end Screened

end Meno
