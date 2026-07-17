import Meno.PeriodLattice

/-! # The Theta Graph: topology layer

The subdivided theta graph `K₂,₃` — two junction vertices joined by
three internal-vertex paths — as raw graph data: edge maps, the two
basis cycles sharing a path, chain Gram `!![4, 2; 2, 4]` with its
inverse, and the cycle/integral presentations. Split out of
`Meno/ThetaHarmonic.lean` (C12, review #2) so that consumers needing
only the *graph* (`Meno/GraphInstances.lean`) do not import the
harmonic, matter, and information layers; the harmonic content
(`thetaHarmonicGramData`, duality, matter, residue counts) lives in
`Meno/ThetaHarmonic.lean`, which imports this file. -/

namespace Meno

open scoped BigOperators
open Matrix

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

/-- The boundary of a 1-cochain: net flow into each vertex. -/
noncomputable def thetaBoundary (ω : Fin 6 → ℝ) (w : Fin 5) : ℝ :=
  ∑ e, ((if thetaTgt e = w then (1 : ℝ) else 0)
    - (if thetaSrc e = w then (1 : ℝ) else 0)) * ω e

/-- The basis cycles: `c₁ = p₁ − p₃` and `c₂ = p₂ − p₃`. -/
noncomputable def thetaCycles : Fin 2 → Fin 6 → ℝ :=
  ![![1, 1, 0, 0, -1, -1], ![0, 0, 1, 1, -1, -1]]

/-- The basis vectors are cycles: their boundary vanishes at every
vertex. -/
theorem thetaBoundary_cycles (i : Fin 2) (w : Fin 5) :
    thetaBoundary (thetaCycles i) w = 0 := by
  fin_cases i <;> fin_cases w <;>
    simp +decide [thetaBoundary, thetaSrc, thetaTgt, thetaCycles,
      Fin.sum_univ_six]

/-- **The cycle space is exactly the span of the basis** (`b₁ = 2`):
a cochain with vanishing boundary is determined by its flows on the
first and second paths, as a combination of `c₁` and `c₂`. Flow
conservation at each interior vertex equalizes the two edges of each
path; conservation at the junction forces the third path's flow to be
minus the sum of the first two. -/
theorem eq_comb_of_thetaBoundary_eq_zero (ω : Fin 6 → ℝ)
    (h : ∀ w, thetaBoundary ω w = 0) :
    ω = fun e => ω 0 * thetaCycles 0 e + ω 2 * thetaCycles 1 e := by
  have h0 := h 0
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  simp +decide [thetaBoundary, thetaSrc, thetaTgt, Fin.sum_univ_six]
    at h0 h2 h3 h4
  funext e
  fin_cases e <;> simp +decide [thetaCycles] <;> linarith

/-- The cycle-chain Gram matrix of `K₂,₃`: paths have length two, and
distinct basis cycles share (only) the third path. -/
theorem gramOf_thetaCycles : gramOf thetaCycles = !![4, 2; 2, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [gramOf, dotProduct, thetaCycles, Fin.sum_univ_six] <;>
    norm_num

/-- The chain Gram matrix is positive definite. -/
theorem thetaChainGram_posDef :
    (!![4, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · show (!![4, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℝ)ᴴ = !![4, 2; 2, 4]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · have hcomp : star x ⬝ᵥ (!![4, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℝ).mulVec x
        = 4 * x 0 ^ 2 + 4 * (x 0 * x 1) + 4 * x 1 ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Pi.star_apply]
      ring
    rw [hcomp]
    have h01 : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hx (funext fun i => by fin_cases i <;> simp [hc.1, hc.2])
    rcases h01 with h0 | h1
    · nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 1),
        lt_of_le_of_ne (sq_nonneg (x 0)) (Ne.symm (pow_ne_zero 2 h0))]
    · nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0),
        lt_of_le_of_ne (sq_nonneg (x 1)) (Ne.symm (pow_ne_zero 2 h1))]

/-- The harmonic period Gram form: the inverse of the chain Gram. -/
theorem thetaChainGram_inv :
    (!![4, 2; 2, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹
      = !![1/3, -(1/6); -(1/6), 1/3] := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The theta graph `K₂,₃` as an incidence graph. -/
@[reducible] def thetaGraph : IncidenceGraph :=
  { V := Fin 5
    E := Fin 6
    src := thetaSrc
    tgt := thetaTgt }

/-- The theta graph as a cycle presentation: `K₂,₃` with its chosen
basis `c₁ = p₁ − p₃`, `c₂ = p₂ − p₃`. -/
@[reducible] noncomputable def thetaPresentation : CyclePresentation thetaGraph where
  r := 2
  cycles := thetaCycles
  cycles_closed := fun i w => thetaBoundary_cycles i w
  spanning := fun ω hω => by
    refine ⟨![ω 0, ω 2], ?_⟩
    have h := eq_comb_of_thetaBoundary_eq_zero ω (fun w => hω w)
    funext e
    rw [congrFun h e, Fin.sum_univ_two]
    rfl
  gram_posDef := by
    rw [gramOf_thetaCycles]
    exact thetaChainGram_posDef

/-- The theta graph as an **integral** presentation: integer basis,
integer period realizability (single-edge cochains on the first and
second paths), and integer integration (the Phase-19 explicit
potential, whose entries are integer combinations of `ω`). Feeds the
keystone `latticeQuotEquiv`. -/
@[reducible] noncomputable def thetaIntegralPresentation :
    IntegralCyclePresentation thetaGraph :=
  { thetaPresentation with
    cyclesZ := ![![1, 1, 0, 0, -1, -1], ![0, 0, 1, 1, -1, -1]]
    cyclesZ_cast := fun i e => by
      fin_cases i <;> fin_cases e <;> norm_num [thetaCycles]
    periods_onto := fun k => by
      refine ⟨![k 0, 0, k 1, 0, 0, 0], fun j => ?_⟩
      fin_cases j <;>
        simp +decide [dotProduct, Fin.sum_univ_six]
    integral_potentials := fun ω h => by
      have h0 := h 0
      have h1 := h 1
      simp +decide [dotProduct, Fin.sum_univ_six] at h0 h1
      refine ⟨![0, ω 4 + ω 5, ω 0, ω 2, ω 4], ?_⟩
      have hgrad : (fun e =>
          (![0, ω 4 + ω 5, ω 0, ω 2, ω 4] : Fin 5 → ℤ) (thetaTgt e)
            - (![0, ω 4 + ω 5, ω 0, ω 2, ω 4] : Fin 5 → ℤ) (thetaSrc e))
          = ω := by
        funext e
        fin_cases e <;> simp +decide [thetaSrc, thetaTgt] <;> omega
      exact hgrad }

/-- The theta basis `c₁ = p₁ − p₃`, `c₂ = p₂ − p₃` is integrally
primitive: an integer cochain with zero boundary is an *integer*
combination of the basis. Completes the primitivity trio (cycle and
wedge in `Meno/CyclePresentation.lean`). -/
theorem theta_integral_spanning (ω : Fin 6 → ℤ)
    (h : ∀ w, thetaBoundary (fun e => (ω e : ℝ)) w = 0) :
    ∃ a : Fin 2 → ℤ, ∀ e, (ω e : ℝ) = ∑ i, (a i : ℝ) * thetaCycles i e := by
  refine ⟨![ω 0, ω 2], fun e => ?_⟩
  have hr := eq_comb_of_thetaBoundary_eq_zero (fun e => (ω e : ℝ)) h
  calc (ω e : ℝ)
      = (ω 0 : ℝ) * thetaCycles 0 e + (ω 2 : ℝ) * thetaCycles 1 e :=
        congrFun hr e
    _ = ∑ i, ((![ω 0, ω 2] : Fin 2 → ℤ) i : ℝ) * thetaCycles i e := by
        rw [Fin.sum_univ_two]
        rfl

end Theta

end Meno
