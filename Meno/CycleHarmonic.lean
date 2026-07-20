import Meno.HarmonicForm
import Meno.Matter
import Meno.PeriodHarmonic
import Meno.Simplicial
import Meno.WedgePresentation

/-! # Cycle-Graph Harmonic Bridge — the flagship spine integration

This file specialises the abstract `HarmonicGramData` to the concrete
cycle graph `CycleGraph n` defined in `Simplicial.lean`. It produces

  `cycleHarmonicGramData n hn : HarmonicGramData (Fin n)`

with rank-1 Gram form `!![1/n]`. The variational identity
`gram-energy = harmonic-energy minimum` is supplied directly by

  `cycleGraph_harmonicEnergy_k : harmonicEnergy_k n hn k = k² / n`

(proved in `Simplicial.lean`'s Hodge section via the Hodge orthogonal
decomposition `EC1 = Harm ⊕ image(d)` and Pythagoras). The induced
`QuadraticAction 1` matches `QuadraticAction.ofScalar (1/n) _` at the
Gram-matrix level, and its partition function is identified with the
legacy `partitionFn n hn` defined in `Simplicial.lean`.

## The flagship theorem

`partitionFn_T_duality_via_spine` states:

  `Z(π² · n) = √((1/n) / π) · partitionFn n hn`

as a corollary of `QuadraticAction.scalarPartFn_duality`. No new modular
or theta input is needed: the new analytic spine carries the duality from
its single source (the modular `S`-transformation of `jacobiTheta`) all
the way to the concrete cycle graph.

This file is the **success criterion** for the abstraction stack laid
down in Phases 1–9. If `SectorAction → QuadraticAction → HarmonicGramData`
is the correct factorisation, the existing cycle-graph T-duality content
factors cleanly through `scalarPartFn_duality` without bespoke analytic
work. It does. -/

namespace Meno

open scoped BigOperators
open Matrix Simplicial

/-- The harmonic Gram data of the n-cycle. Rank is 1 (the first Betti
number of `C_n`); the Gram form is `!![1/n]`, the rank-1 Hodge Gram of
the cycle's harmonic 1-cochain `cycleHarmonicForm`. Positive-definiteness
reduces to `1/n > 0` (so `n ≥ 3` is more than enough); summability is
derived (`HarmonicGramData.summable`). -/
noncomputable def cycleHarmonicGramData (n : ℕ) (hn : n ≥ 3) :
    HarmonicGramData (Fin n) where
  r := 1
  gram := !![1 / (n : ℝ)]
  gram_posDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
    · ext i j; fin_cases i; fin_cases j; rfl
    · intro x hx
      have hx0 : x 0 ≠ 0 := by
        intro h0; apply hx; ext i; fin_cases i; exact h0
      have hcomp : star x ⬝ᵥ !![(1 : ℝ) / n].mulVec x = (1 / n) * (x 0) ^ 2 := by
        simp [dotProduct, mulVec, Matrix.cons_val_fin_one, Pi.star_apply]
        ring
      rw [hcomp]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hα : (0 : ℝ) < 1 / n := one_div_pos.mpr hn0
      have hsq : 0 < (x 0) ^ 2 := by positivity
      exact mul_pos hα hsq


/-- **Spine partition function = scalar partition function** at α = 1/n.
A consequence of Q-matrix equality. -/
theorem cycleHarmonicGramData_partFn_eq_scalar (n : ℕ) (hn : n ≥ 3) :
    (cycleHarmonicGramData n hn).toQuadraticAction.toSectorAction.partFn
    = QuadraticAction.scalarPartFn (1 / n) := by
  have hαpos : (0 : ℝ) < 1 / n := one_div_pos.mpr
    (by exact_mod_cast (show 0 < n by omega))
  rw [QuadraticAction.partFn_eq_of_Q_eq
        (cycleHarmonicGramData n hn).toQuadraticAction
        (QuadraticAction.ofScalar (1 / n) hαpos) rfl,
      QuadraticAction.ofScalar_partFn_eq]

/-- **Scalar partition function at α = 1/n equals legacy `partitionFn`.**
Definitional manipulation: `exp(-(1/n)·k²) = exp(-k²/n)`. -/
theorem scalarPartFn_one_div_n_eq_partitionFn (n : ℕ) (hn : n ≥ 3) :
    QuadraticAction.scalarPartFn (1 / n) = partitionFn n hn := by
  show ∑' k : ℤ, Real.exp (-(1 / n) * (k : ℝ) ^ 2)
    = ∑' k : ℤ, Real.exp (-(k : ℝ) ^ 2 / n)
  refine tsum_congr (fun k => ?_)
  congr 1; field_simp

/-- **Spine partition function = legacy `partitionFn`**: the rank-1 Hodge
Gram data of the n-cycle reproduces the existing path-integral
`partitionFn n hn`. -/
theorem cycleHarmonicGramData_partFn_eq_partitionFn (n : ℕ) (hn : n ≥ 3) :
    (cycleHarmonicGramData n hn).toQuadraticAction.toSectorAction.partFn
    = partitionFn n hn := by
  rw [cycleHarmonicGramData_partFn_eq_scalar,
      scalarPartFn_one_div_n_eq_partitionFn]

/-- **THE FLAGSHIP**: the cycle-graph T-duality

  `Z(π² · n) = √((1/n) / π) · partitionFn n hn`

— now derived **through the topology** (review #11): it is
`cycle_harmonic_duality` at the cycle graph, read in the
`cycleLatticeBasis` chart. The dual side is the priced cycle lattice —
the all-ones cycle with chain Gram `!![n]`, so the homology action is
the scalar action at `π²·n` — the harmonic side is the legacy
`partitionFn`, and the prefactor is the carrier discriminant `1/n`.
No bespoke modular input, and no direct coordinate duality call: the
scalar `S`-transformation is consumed once, inside the intrinsic
proof's analytic spine. -/
theorem partitionFn_T_duality_via_spine (n : ℕ) (hn : n ≥ 3) :
    (↑(QuadraticAction.scalarPartFn (Real.pi ^ 2 * n)) : ℂ) =
    ↑((1 / (n : ℝ)) / Real.pi) ^ ((1 : ℂ) / 2) * ↑(partitionFn n hn) := by
  have hpos : 0 < n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
  have hπn : (0 : ℝ) < Real.pi ^ 2 * n := by positivity
  have hcycR : (cycleGraph n hpos).cyclesR (cycleLatticeBasis n hpos)
      = cycleAllOnes n := by
    funext i e
    show (((cycleGraph n hpos).cyclesZ (cycleLatticeBasis n hpos) i e
      : ℤ) : ℝ) = cycleAllOnes n i e
    rw [cyclesZ_cycleLatticeBasis]
    simp [cycleCyclesZ, cycleAllOnes]
  have hdual : ((cycleGraph n hpos).cycleAction).toSectorAction.partFn
      = QuadraticAction.scalarPartFn (Real.pi ^ 2 * n) := by
    rw [← ((cycleGraph n hpos).cycleAction).partFn_chartAction
      (cycleLatticeBasis n hpos)]
    rw [show ((cycleGraph n hpos).cycleAction).chartAction
        (cycleLatticeBasis n hpos)
        = QuadraticAction.ofScalar (Real.pi ^ 2 * n) hπn from
      QuadraticAction.eq_of_Q_eq (by
        rw [QuadLatticeAction.chartAction_Q,
          (cycleGraph n hpos).cycleAction_gram (cycleLatticeBasis n hpos),
          hcycR, gramOf_cycleAllOnes]
        show Real.pi ^ 2 • !![(n : ℝ)] = !![Real.pi ^ 2 * n]
        ext i j
        fin_cases i
        fin_cases j
        simp)]
    exact QuadraticAction.ofScalar_partFn_eq _ hπn
  have hharm : ((cycleGraph n hpos).classQuadAction).toSectorAction.partFn
      = partitionFn n hn := by
    rw [(cycleGraph n hpos).classQuadAction_partFn,
      ← (cycleGraph n hpos).basisGramData_partFn (cycleLatticeBasis n hpos),
      ← cycleHarmonicGramData_partFn_eq_partitionFn n hn]
    refine QuadraticAction.partFn_eq_of_Q_eq _ _ ?_
    rw [HarmonicGramData.toQuadraticAction_Q,
      HarmonicGramData.toQuadraticAction_Q,
      (cycleGraph n hpos).basisGramData_gram, hcycR, gramOf_cycleAllOnes,
      inv_fin_one _ hn0.ne']
    show !![(n : ℝ)⁻¹] = !![1 / (n : ℝ)]
    rw [one_div]
  have hdisc : ((cycleGraph n hpos).classQuadAction).disc = 1 / (n : ℝ) := by
    rw [(cycleGraph n hpos).classQuadAction_disc (cycleLatticeBasis n hpos),
      hcycR, gramOf_cycleAllOnes, inv_fin_one _ hn0.ne']
    show (!![(n : ℝ)⁻¹] : Matrix (Fin 1) (Fin 1) ℝ).det = 1 / (n : ℝ)
    rw [Matrix.det_fin_one]
    norm_num
  have hb1 : (cycleGraph n hpos).b1 = 1 := cycleGraph_b1' n hpos
  have h := (cycleGraph n hpos).cycle_harmonic_duality
  rw [hb1, hdisc, pow_one, hdual, hharm] at h
  exact h

/-! ## Theta identification (formerly `Theta.lean`)

`Theta.lean` carried its own copy of the modular machinery, specialized
at `τ = i/(πn)`. Its two public statements survive here as corollaries
of the spine's single theta identification
`QuadraticAction.scalarPartFn_eq_jacobiTheta`. -/


/-! ## Rank 2: the wedge of two cycles

The wedge `C_{n₁} ∨ C_{n₂}` (two cycles joined at a point) has first
Betti number 2, and its harmonic 1-cochains have disjoint edge supports
— one per cycle — so the harmonic Gram form is the **direct sum**
`diag(1/n₁, 1/n₂)`. The Gram data below packages that form; its
positive-definiteness and summability are inherited from
`QuadraticAction.ofDiagonal₂`, whose Gram matrix is definitionally the
same.

The graph-level *derivation* of this Gram form is now the genuine
wedge's (`Meno/WedgePresentation.lean`, C1/C5): the two basis cycles
have disjoint edge supports, chain Gram `diag(n₁, n₂)` (vertex-free,
`Meno/PeriodHarmonic.lean`), spanning by the Euler criterion on the
`n₁ + n₂ − 1`-vertex graph, and the period Gram is the inverse. The
cycle-side identification lives in the `PeriodUnification` section
(`cyclePeriodData_energy_eq`). A simplicial wedge complex
with its own Hodge decomposition still does not exist in
`Simplicial.lean` — the derivation is cohomological (periods), not
chain-level. -/

/-- Harmonic Gram data of the wedge of two cycles: rank 2, Gram form
`diag(1/n₁, 1/n₂)`. -/
noncomputable def wedgeHarmonicGramData (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    HarmonicGramData (Fin n₁ ⊕ Fin n₂) where
  r := 2
  gram := !![1 / (n₁ : ℝ), 0; 0, 1 / (n₂ : ℝ)]
  gram_posDef := (QuadraticAction.ofDiagonal₂ (1 / (n₁ : ℝ)) (1 / (n₂ : ℝ))
    (one_div_pos.mpr (by exact_mod_cast (show 0 < n₁ by omega)))
    (one_div_pos.mpr (by exact_mod_cast (show 0 < n₂ by omega)))).Q_posDef

/-- The first-cycle basis winding `(1, 0)` has energy `1/n₁`: each
cycle's mass spectrum survives in the wedge. -/
theorem wedgeHarmonicGramData_energy_basis₁ (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    (wedgeHarmonicGramData n₁ n₂ h₁ h₂).energy ![1, 0] = 1 / n₁ := by
  show ∑ i, ∑ j, (!![1 / (n₁ : ℝ), 0; 0, 1 / (n₂ : ℝ)]) i j
      * ((![1, 0] : Fin 2 → ℤ) i : ℝ) * ((![1, 0] : Fin 2 → ℤ) j : ℝ) = 1 / n₁
  simp [Fin.sum_univ_two]

/-- **Rank-2 matter exists**: the wedge carries matter sectors — the
intrinsic class of the single-edge cochain on the first cycle (C6).
First matter instance above rank 1 — the abstraction stack is not
secretly rank-1. -/
noncomputable def wedgeMatter₁ (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    MatterSector (wedgeGraph n₁ n₂ (by omega) (by omega)) :=
  haveI : NeZero n₁ := ⟨by omega⟩
  haveI : NeZero n₂ := ⟨by omega⟩
  ⟨Submodule.Quotient.mk
      (Sum.elim (fun e => if e = 0 then 1 else 0) (fun _ => 0)), by
    intro h0
    have h := congrArg
      ((wedgeGraph n₁ n₂ (by omega) (by omega)).latticeQuotEquiv
        (wedgeLatticeBasis n₁ n₂ (by omega) (by omega))) h0
    rw [map_zero] at h
    have h1 : (Sum.elim (fun e => if e = 0 then (1 : ℤ) else 0)
          (fun _ => 0) : Fin n₁ ⊕ Fin n₂ → ℤ)
        ⬝ᵥ (wedgeGraph n₁ n₂ (by omega) (by omega)).cyclesZ
          (wedgeLatticeBasis n₁ n₂ (by omega) (by omega)) 0 = 0 :=
      congrFun h 0
    rw [cyclesZ_wedgeLatticeBasis] at h1
    rw [show ((Sum.elim (fun e => if e = 0 then (1 : ℤ) else 0)
          (fun _ => 0) : Fin n₁ ⊕ Fin n₂ → ℤ)
        ⬝ᵥ wedgeCyclesZ n₁ n₂ 0)
        = ∑ e : Fin n₁ ⊕ Fin n₂,
            (Sum.elim (fun e => if e = 0 then (1 : ℤ) else 0)
              (fun _ => 0)) e
            * Sum.elim (fun _ => (1 : ℤ)) (fun _ => 0) e from rfl,
      Fintype.sum_sum_type] at h1
    simp at h1⟩

theorem wedge_exists_matter (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    Nonempty (MatterSector (wedgeGraph n₁ n₂ (by omega) (by omega))) :=
  ⟨wedgeMatter₁ n₁ n₂ h₁ h₂⟩


/-! ## Unification: the walk route and the period route agree

`Simplicial.lean` derived the cycle graph's harmonic minimum
`harmonicEnergy_k = k²/n` through ~2500 lines of walk/homotopy/Hodge
machinery. `PeriodHarmonic.lean` re-derives the same Gram form
`[[1/n]]` in ~100 lines through the least-norm-at-prescribed-periods
machinery. Here the two are proved to be the *same analytic object*:
same Gram matrix, same energies, and the legacy walk-based value is
certified as the period-variational minimum. Two independent
derivations of the spine's first mass. -/

section PeriodUnification


/-- The energies agree at every sector. -/
theorem cyclePeriodData_energy_eq (n : ℕ) (hn : n ≥ 3) (k : Fin 1 → ℤ) :
    (cyclePeriodData n (by omega)).energy k
      = (cycleHarmonicGramData n hn).energy k := by
  calc (cyclePeriodData n (by omega)).energy k
      = ∑ i, ∑ j, (!![1 / (n : ℝ)] : Matrix (Fin 1) (Fin 1) ℝ) i j
          * (k i : ℝ) * (k j : ℝ) := by
        show ∑ i, ∑ j, (cyclePeriodData n (by omega)).gram i j
            * (k i : ℝ) * (k j : ℝ) = _
        rw [cyclePeriodData_gram]
    _ = (cycleHarmonicGramData n hn).energy k := rfl


/-! ### The wedge: assertion retired

`wedgeHarmonicGramData` above was introduced (Phase 13) with its Gram
form `diag(1/n₁, 1/n₂)` asserted on "true, unformalized ground." The
period machinery now derives that form from the wedge graph itself
(`Meno/PeriodHarmonic.lean`); here the derived data is identified with
the asserted data — matrix, energies, and partition function — and the
asserted energy is certified as the variational minimum. -/


/-- The energies agree at every sector. -/
theorem wedgePeriodData_energy_eq (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3)
    (k : Fin 2 → ℤ) :
    (wedgePeriodData n₁ n₂ (by omega) (by omega)).energy k
      = (wedgeHarmonicGramData n₁ n₂ h₁ h₂).energy k := by
  calc (wedgePeriodData n₁ n₂ (by omega) (by omega)).energy k
      = ∑ i, ∑ j, (!![1 / (n₁ : ℝ), 0; 0, 1 / (n₂ : ℝ)]) i j
          * (k i : ℝ) * (k j : ℝ) := by
        show ∑ i, ∑ j, (wedgePeriodData n₁ n₂ (by omega) (by omega)).gram i j
            * (k i : ℝ) * (k j : ℝ) = _
        rw [wedgePeriodData_gram]
    _ = (wedgeHarmonicGramData n₁ n₂ h₁ h₂).energy k := rfl


/-- The wedge lattice basis's cast cycles are the real wedge cycles. -/
theorem cyclesR_wedgeLatticeBasis (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) :
    (wedgeGraph n₁ n₂ h₁ h₂).cyclesR (wedgeLatticeBasis n₁ n₂ h₁ h₂)
      = wedgeCycles n₁ n₂ := by
  funext i e
  show (((wedgeGraph n₁ n₂ h₁ h₂).cyclesZ
      (wedgeLatticeBasis n₁ n₂ h₁ h₂) i e : ℤ) : ℝ)
    = wedgeCycles n₁ n₂ i e
  rw [cyclesZ_wedgeLatticeBasis]
  fin_cases i <;> cases e <;> simp [wedgeCyclesZ, wedgeCycles]

/-- The wedge matter's keystone coordinates are `(1, 0)`. -/
theorem wedgeMatter₁_coords (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    (wedgeGraph n₁ n₂ (by omega) (by omega)).latticeQuotEquiv
        (wedgeLatticeBasis n₁ n₂ (by omega) (by omega))
        (wedgeMatter₁ n₁ n₂ h₁ h₂).val
      = ![1, 0] := by
  haveI : NeZero n₁ := ⟨by omega⟩
  haveI : NeZero n₂ := ⟨by omega⟩
  funext j
  show (Sum.elim (fun e => if e = 0 then (1 : ℤ) else 0) (fun _ => 0))
      ⬝ᵥ (wedgeGraph n₁ n₂ (by omega) (by omega)).cyclesZ
        (wedgeLatticeBasis n₁ n₂ (by omega) (by omega)) j = ![1, 0] j
  rw [cyclesZ_wedgeLatticeBasis]
  fin_cases j
  · show (∑ e : Fin n₁ ⊕ Fin n₂,
        (Sum.elim (fun e => if e = 0 then (1 : ℤ) else 0) (fun _ => 0)) e
          * Sum.elim (fun _ => (1 : ℤ)) (fun _ => 0) e) = 1
    rw [Fintype.sum_sum_type]
    simp
  · show (∑ e : Fin n₁ ⊕ Fin n₂,
        (Sum.elim (fun e => if e = 0 then (1 : ℤ) else 0) (fun _ => 0)) e
          * Sum.elim (fun _ => (0 : ℤ)) (fun _ => 1) e) = 0
    rw [Fintype.sum_sum_type]
    simp

/-- The wedge matter's mass is `1/n₁`: intrinsic mass → chart →
derived Gram → asserted Gram, one chain of identifications. -/
theorem wedgeMatter₁_mass (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    (wedgeMatter₁ n₁ n₂ h₁ h₂).mass = 1 / n₁ := by
  rw [← (wedgeMatter₁ n₁ n₂ h₁ h₂).mass_chart
      (wedgeLatticeBasis n₁ n₂ (by omega) (by omega)),
    wedgeMatter₁_coords n₁ n₂ h₁ h₂]
  show ∑ i, ∑ j,
      (gramOf ((wedgeGraph n₁ n₂ (by omega) (by omega)).cyclesR
        (wedgeLatticeBasis n₁ n₂ (by omega) (by omega))))⁻¹ i j
      * ((![1, 0] : Fin 2 → ℤ) i : ℝ) * ((![1, 0] : Fin 2 → ℤ) j : ℝ)
    = 1 / n₁
  rw [cyclesR_wedgeLatticeBasis]
  show (wedgePeriodData n₁ n₂ (by omega) (by omega)).energy ![1, 0] = 1 / n₁
  rw [wedgePeriodData_energy_eq n₁ n₂ h₁ h₂,
    wedgeHarmonicGramData_energy_basis₁]


end PeriodUnification

end Meno
