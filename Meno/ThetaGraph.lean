import Meno.CycleBasis

/-! # The Theta Graph: incidence data (topology layer)

The subdivided theta graph `K₂,₃` — two junction vertices joined by
three internal-vertex paths — as **pure incidence data**: edge maps,
the graph, the two basis cycles sharing a path, and the topological
facts about them (closedness, spanning, integral primitivity), all
stated through the substrate's `IncidenceGraph.boundary` — no
specialized boundary operator (review #3, finding 4).

Everything priced lives downstream: the chain Gram `!![4, 2; 2, 4]`,
its positive-definiteness and inverse, and the cycle/integral
presentations are **harmonic** content and live in
`Meno/ThetaHarmonic.lean` (review #3, finding 2 — this file imports
only the topology layer). -/

namespace Meno

open scoped BigOperators

/-! ## The subdivided theta graph `K₂,₃`

Vertices: `0 = u`, `1 = v` (junctions), `2, 3, 4` (path interiors).
Edges (all oriented junction-to-junction): `e₀ : u→a₁`, `e₁ : a₁→v`,
`e₂ : u→a₂`, `e₃ : a₂→v`, `e₄ : u→a₃`, `e₅ : a₃→v`. Cycle basis
`c₁ = p₁ − p₃`, `c₂ = p₂ − p₃`. -/

section Theta

/-- Edge sources in `K₂,₃`. -/
def thetaSrc : Fin 6 → Fin 5 := ![0, 2, 0, 3, 0, 4]

/-- Edge targets in `K₂,₃`. -/
def thetaTgt : Fin 6 → Fin 5 := ![2, 1, 3, 1, 4, 1]

/-- The theta graph `K₂,₃` as an incidence graph. -/
@[reducible] def thetaGraph : IncidenceGraph :=
  { V := Fin 5
    E := Fin 6
    src := thetaSrc
    tgt := thetaTgt }

/-- The basis cycles: `c₁ = p₁ − p₃` and `c₂ = p₂ − p₃`. -/
noncomputable def thetaCycles : Fin 2 → Fin 6 → ℝ :=
  ![![1, 1, 0, 0, -1, -1], ![0, 0, 1, 1, -1, -1]]

/-- The theta graph's substrate boundary, in explicit-sum form. -/
theorem thetaGraph_boundary_eq_sum (ω : Fin 6 → ℝ) (w : Fin 5) :
    thetaGraph.boundary ω w
      = ∑ e, ((if thetaTgt e = w then (1 : ℝ) else 0)
        - (if thetaSrc e = w then (1 : ℝ) else 0)) * ω e := rfl

/-- The basis vectors are cycles: their boundary vanishes at every
vertex. -/
theorem thetaGraph_boundary_cycles (i : Fin 2) (w : Fin 5) :
    thetaGraph.boundary (thetaCycles i) w = 0 := by
  rw [thetaGraph_boundary_eq_sum]
  fin_cases i <;> fin_cases w <;>
    simp +decide [thetaSrc, thetaTgt, thetaCycles, Fin.sum_univ_six]

/-- **The cycle space is exactly the span of the basis** (`b₁ = 2`):
a cochain with vanishing boundary is determined by its flows on the
first and second paths, as a combination of `c₁` and `c₂`. Flow
conservation at each interior vertex equalizes the two edges of each
path; conservation at the junction forces the third path's flow to be
minus the sum of the first two. -/
theorem eq_comb_of_theta_boundary_eq_zero (ω : Fin 6 → ℝ)
    (h : ∀ w, thetaGraph.boundary ω w = 0) :
    ω = fun e => ω 0 * thetaCycles 0 e + ω 2 * thetaCycles 1 e := by
  have h0 := h 0
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  rw [thetaGraph_boundary_eq_sum] at h0 h2 h3 h4
  simp +decide [thetaSrc, thetaTgt, Fin.sum_univ_six] at h0 h2 h3 h4
  funext e
  fin_cases e <;> simp +decide [thetaCycles] <;> linarith

/-- **The theta graph's topological cycle basis** (`b₁ = 2`): closed,
spanning — no Gram, no pricing. The priced presentation is
`thetaPresentation` (`Meno/ThetaHarmonic.lean`). -/
@[reducible] noncomputable def thetaCycleBasis : CycleBasis thetaGraph where
  r := 2
  cycles := thetaCycles
  cycles_closed := fun i w => thetaGraph_boundary_cycles i w
  spanning := fun ω hω => by
    refine ⟨![ω 0, ω 2], ?_⟩
    have h := eq_comb_of_theta_boundary_eq_zero ω (fun w => hω w)
    funext e
    rw [congrFun h e, Fin.sum_univ_two]
    rfl
  independent := fun x hx => by
    have h0 := congrFun hx 0
    have h2 := congrFun hx 2
    simp +decide [thetaCycles, Fin.sum_univ_two] at h0 h2
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h2

/-- The theta basis `c₁ = p₁ − p₃`, `c₂ = p₂ − p₃` is integrally
primitive: an integer cochain with zero boundary is an *integer*
combination of the basis. Completes the primitivity trio (cycle and
wedge in `Meno/CyclePresentation.lean`). -/
theorem theta_integral_spanning (ω : Fin 6 → ℤ)
    (h : ∀ w, thetaGraph.boundary (fun e => (ω e : ℝ)) w = 0) :
    ∃ a : Fin 2 → ℤ, ∀ e, (ω e : ℝ) = ∑ i, (a i : ℝ) * thetaCycles i e := by
  refine ⟨![ω 0, ω 2], fun e => ?_⟩
  have hr := eq_comb_of_theta_boundary_eq_zero (fun e => (ω e : ℝ)) h
  calc (ω e : ℝ)
      = (ω 0 : ℝ) * thetaCycles 0 e + (ω 2 : ℝ) * thetaCycles 1 e :=
        congrFun hr e
    _ = ∑ i, ((![ω 0, ω 2] : Fin 2 → ℤ) i : ℝ) * thetaCycles i e := by
        rw [Fin.sum_univ_two]
        rfl

end Theta

end Meno
