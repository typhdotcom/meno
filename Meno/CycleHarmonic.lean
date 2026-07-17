import Meno.HarmonicForm
import Meno.Matter
import Meno.PeriodHarmonic
import Meno.Simplicial

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
transported from `summable_partitionFn` via `Equiv.funUnique`. -/
noncomputable def cycleHarmonicGramData (n : ℕ) (hn : n ≥ 3) :
    HarmonicGramData (Fin n) where
  r := 1
  gram := !![1 / (n : ℝ)]
  gram_symm := by ext i j; fin_cases i; fin_cases j; rfl
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
  summable := by
    have hsumZ : Summable (fun k : ℤ => Real.exp (-(k : ℝ) ^ 2 / n)) :=
      summable_partitionFn n hn
    let e : (Fin 1 → ℤ) ≃ ℤ := Equiv.funUnique (Fin 1) ℤ
    refine Summable.congr (e.summable_iff.mpr hsumZ) ?_
    intro k
    show Real.exp (-((e k : ℤ) : ℝ) ^ 2 / n)
      = Real.exp (-(∑ i : Fin 1, ∑ j : Fin 1,
          !![(1 : ℝ) / n] i j * (k i : ℝ) * (k j : ℝ)))
    have hek : (e k : ℤ) = k 0 := rfl
    rw [hek]
    congr 1
    simp [Matrix.cons_val_fin_one]
    ring

/-- Energy of the cycle harmonic Gram data: `(1/n) · k²`. -/
theorem cycleHarmonicGramData_energy (n : ℕ) (hn : n ≥ 3) (k : Fin 1 → ℤ) :
    (cycleHarmonicGramData n hn).energy k = (k 0 : ℝ) ^ 2 / n := by
  show ∑ i : Fin 1, ∑ j : Fin 1,
      !![(1 : ℝ) / n] i j * (k i : ℝ) * (k j : ℝ) = (k 0 : ℝ) ^ 2 / n
  simp [Matrix.cons_val_fin_one]; ring

/-- **The variational identity**: the Gram-form energy at integer winding `k`
equals `harmonicEnergy_k n hn k`, the minimum 1-cochain energy over the
winding-`k` class. This is the bridge from the graph layer to the
abstract `HarmonicGramData`. -/
theorem cycleHarmonicGramData_energy_eq_harmonicEnergy_k
    (n : ℕ) (hn : n ≥ 3) (k : Fin 1 → ℤ) :
    (cycleHarmonicGramData n hn).energy k = harmonicEnergy_k n hn (k 0) := by
  rw [cycleHarmonicGramData_energy, cycleGraph_harmonicEnergy_k]

/-- The induced `QuadraticAction` has the same Gram matrix `!![1/n]` as
`QuadraticAction.ofScalar (1/n) _`. -/
theorem cycleHarmonicGramData_toQuadraticAction_Q (n : ℕ) (hn : n ≥ 3) :
    (cycleHarmonicGramData n hn).toQuadraticAction.Q
    = (QuadraticAction.ofScalar (1 / n) (one_div_pos.mpr
        (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n))).Q := rfl

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

is a consequence of `QuadraticAction.scalarPartFn_duality` applied at
coupling `α = 1/n`. No bespoke modular input is needed at this layer —
the duality is unpacked from the analytic primitive. The categorical
groupoid wrapper from `Duality.lean` is no longer load-bearing for this
correspondence; the new spine carries it. -/
theorem partitionFn_T_duality_via_spine (n : ℕ) (hn : n ≥ 3) :
    (↑(QuadraticAction.scalarPartFn (Real.pi ^ 2 * n)) : ℂ) =
    ↑((1 / (n : ℝ)) / Real.pi) ^ ((1 : ℂ) / 2) * ↑(partitionFn n hn) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hαpos : (0 : ℝ) < 1 / n := one_div_pos.mpr hn0
  have hπα : Real.pi ^ 2 / (1 / n) = Real.pi ^ 2 * n := by field_simp
  rw [show Real.pi ^ 2 * n = Real.pi ^ 2 / (1 / n) from hπα.symm,
      QuadraticAction.scalarPartFn_duality (1 / n) hαpos,
      scalarPartFn_one_div_n_eq_partitionFn n hn]

/-! ## Theta identification (formerly `Theta.lean`)

`Theta.lean` carried its own copy of the modular machinery, specialized
at `τ = i/(πn)`. Its two public statements survive here as corollaries
of the spine's single theta identification
`QuadraticAction.scalarPartFn_eq_jacobiTheta`. -/

/-- The n-cycle partition function is the Jacobi theta function at
`τ = i/(πn)`. -/
theorem partitionFn_eq_jacobiTheta (n : ℕ) (hn : n ≥ 3) :
    (↑(partitionFn n hn) : ℂ) = jacobiTheta (Complex.I / (↑Real.pi * ↑n)) := by
  rw [← scalarPartFn_one_div_n_eq_partitionFn n hn,
      QuadraticAction.scalarPartFn_eq_jacobiTheta]
  congr 1
  show Complex.I * ↑(1 / (n : ℝ)) / ↑Real.pi = Complex.I / (↑Real.pi * ↑n)
  have hpi : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  have hn0 : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast
  field_simp

/-- **T-duality in theta form** (formerly `Theta.partitionFn_T_duality`):
`ϑ₃(iπn) = (1/(πn))^(1/2) · Z(Cₙ)`. A corollary of the spine flagship. -/
theorem partitionFn_T_duality_theta (n : ℕ) (hn : n ≥ 3) :
    jacobiTheta (Complex.I * ↑Real.pi * ↑n) =
      (↑(1 / (Real.pi * ↑n) : ℝ) : ℂ) ^ ((1 : ℂ) / 2) * ↑(partitionFn n hn) := by
  have hθ : (↑(QuadraticAction.scalarPartFn (Real.pi ^ 2 * n)) : ℂ)
      = jacobiTheta (Complex.I * ↑Real.pi * ↑n) := by
    rw [QuadraticAction.scalarPartFn_eq_jacobiTheta]
    congr 1
    show Complex.I * ↑(Real.pi ^ 2 * (n : ℝ)) / ↑Real.pi = Complex.I * ↑Real.pi * ↑n
    have hpi : (↑Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
    push_cast
    field_simp
  have harg : ((1 : ℝ) / (Real.pi * n)) = (1 / (n : ℝ)) / Real.pi := by
    field_simp
  rw [← hθ, harg]
  exact partitionFn_T_duality_via_spine n hn

/-! ## Rank 2: the wedge of two cycles

The wedge `C_{n₁} ∨ C_{n₂}` (two cycles joined at a point) has first
Betti number 2, and its harmonic 1-cochains have disjoint edge supports
— one per cycle — so the harmonic Gram form is the **direct sum**
`diag(1/n₁, 1/n₂)`. The Gram data below packages that form; its
positive-definiteness and summability are inherited from
`QuadraticAction.ofDiagonal₂`, whose Gram matrix is definitionally the
same.

The graph-level *derivation* of this Gram form is formalized in
`Meno/PeriodHarmonic.lean` through the period machinery: the wedge
graph's two basis cycles have disjoint edge supports, chain Gram
`diag(n₁, n₂)`, spanning is a theorem (`b₁ = 2`,
`eq_comb_of_wedgeBoundary_eq_zero`), and the period Gram is the
inverse. The identification with the data below lives in the
`PeriodUnification` section (`wedgePeriodData_gram_eq`,
`wedgeHarmonicGramData_energy_isLeast`). A simplicial wedge complex
with its own Hodge decomposition still does not exist in
`Simplicial.lean` — the derivation is cohomological (periods), not
chain-level. -/

/-- Harmonic Gram data of the wedge of two cycles: rank 2, Gram form
`diag(1/n₁, 1/n₂)`. -/
noncomputable def wedgeHarmonicGramData (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    HarmonicGramData (Fin n₁ ⊕ Fin n₂) where
  r := 2
  gram := !![1 / (n₁ : ℝ), 0; 0, 1 / (n₂ : ℝ)]
  gram_symm := (QuadraticAction.ofDiagonal₂ (1 / (n₁ : ℝ)) (1 / (n₂ : ℝ))
    (one_div_pos.mpr (by exact_mod_cast (show 0 < n₁ by omega)))
    (one_div_pos.mpr (by exact_mod_cast (show 0 < n₂ by omega)))).Q_symm
  gram_posDef := (QuadraticAction.ofDiagonal₂ (1 / (n₁ : ℝ)) (1 / (n₂ : ℝ))
    (one_div_pos.mpr (by exact_mod_cast (show 0 < n₁ by omega)))
    (one_div_pos.mpr (by exact_mod_cast (show 0 < n₂ by omega)))).Q_posDef
  summable := (QuadraticAction.ofDiagonal₂ (1 / (n₁ : ℝ)) (1 / (n₂ : ℝ))
    (one_div_pos.mpr (by exact_mod_cast (show 0 < n₁ by omega)))
    (one_div_pos.mpr (by exact_mod_cast (show 0 < n₂ by omega)))).summable

/-- The first-cycle basis winding `(1, 0)` has energy `1/n₁`: each
cycle's mass spectrum survives in the wedge. -/
theorem wedgeHarmonicGramData_energy_basis₁ (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    (wedgeHarmonicGramData n₁ n₂ h₁ h₂).energy ![1, 0] = 1 / n₁ := by
  show ∑ i, ∑ j, (!![1 / (n₁ : ℝ), 0; 0, 1 / (n₂ : ℝ)]) i j
      * ((![1, 0] : Fin 2 → ℤ) i : ℝ) * ((![1, 0] : Fin 2 → ℤ) j : ℝ) = 1 / n₁
  simp [Fin.sum_univ_two]

/-- **Rank-2 matter exists**: the wedge carries matter sectors — now
anchored to the wedge presentation itself (Phase 22), not to bare Gram
data. First matter instance above rank 1 — the abstraction stack is
not secretly rank-1. -/
noncomputable def wedgeMatter₁ (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    MatterSector (wedgePresentation n₁ n₂ (by omega) (by omega)) :=
  ⟨![1, 0], by
    intro h
    have h0 := congrFun h 0
    simp at h0⟩

theorem wedge_exists_matter (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    Nonempty (MatterSector (wedgePresentation n₁ n₂ (by omega) (by omega))) :=
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

/-- The period-model Gram data of `C_n` has the same Gram matrix as the
walk-derived data: `[[1/n]]` both ways. -/
theorem cyclePeriodData_gram_eq (n : ℕ) (hn : n ≥ 3) :
    (cyclePeriodData n (by omega)).gram = (cycleHarmonicGramData n hn).gram := by
  rw [cyclePeriodData_gram]
  rfl

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

/-- **Two variational stories, one number**: the walk-based harmonic
minimum `harmonicEnergy_k n hn k` of `Simplicial.lean` — historically
the spine's first mass, `k²/n` — is the least energy among 1-cochains
on the period-model cycle graph with period `k`. -/
theorem harmonicEnergy_k_isLeast_periods (n : ℕ) (hn : n ≥ 3) (k : ℤ) :
    IsLeast {E : ℝ | ∃ ω : Fin n → ℝ,
        (∀ j, ω ⬝ᵥ cycleAllOnes n j = ((![k] : Fin 1 → ℤ) j : ℝ)) ∧ E = ω ⬝ᵥ ω}
      (harmonicEnergy_k n hn k) := by
  have h := HarmonicGramData.ofCycles_energy_isLeast (V := Fin n)
    (cycleAllOnes n)
    (by
      rw [gramOf_cycleAllOnes]
      exact posDef_fin_one _ (by exact_mod_cast (show 0 < n by omega))) ![k]
  have hchain : (cyclePeriodData n (by omega)).energy ![k]
      = harmonicEnergy_k n hn k := by
    rw [cyclePeriodData_energy_eq n hn,
      cycleHarmonicGramData_energy_eq_harmonicEnergy_k n hn]
    norm_num
  rw [← hchain]
  exact h

/-! ### The wedge: assertion retired

`wedgeHarmonicGramData` above was introduced (Phase 13) with its Gram
form `diag(1/n₁, 1/n₂)` asserted on "true, unformalized ground." The
period machinery now derives that form from the wedge graph itself
(`Meno/PeriodHarmonic.lean`); here the derived data is identified with
the asserted data — matrix, energies, and partition function — and the
asserted energy is certified as the variational minimum. -/

/-- The period-model Gram data of the wedge has the same Gram matrix
as the asserted data: `diag(1/n₁, 1/n₂)` both ways. -/
theorem wedgePeriodData_gram_eq (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    (wedgePeriodData n₁ n₂ (by omega) (by omega)).gram
      = (wedgeHarmonicGramData n₁ n₂ h₁ h₂).gram :=
  calc (wedgePeriodData n₁ n₂ (by omega) (by omega)).gram
      = !![1 / (n₁ : ℝ), 0; 0, 1 / (n₂ : ℝ)] :=
        wedgePeriodData_gram n₁ n₂ (by omega) (by omega)
    _ = (wedgeHarmonicGramData n₁ n₂ h₁ h₂).gram := rfl

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

/-- The partition functions agree: the asserted analytic layer *is*
the derived one. -/
theorem wedgePeriodData_partFn_eq (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    (wedgePeriodData n₁ n₂ (by omega)
        (by omega)).toQuadraticAction.toSectorAction.partFn
      = (wedgeHarmonicGramData n₁ n₂
          h₁ h₂).toQuadraticAction.toSectorAction.partFn :=
  QuadraticAction.partFn_eq_of_Q_eq _ _ (wedgePeriodData_gram_eq n₁ n₂ h₁ h₂)

/-- **The Phase-13 assertion, retired**: the energy of the asserted
`diag(1/n₁, 1/n₂)` Gram data is the least cochain energy at prescribed
periods over the actual wedge graph's cycles. The last documented
assertion debt in the harmonic layer is now a theorem. -/
theorem wedgeHarmonicGramData_energy_isLeast (n₁ n₂ : ℕ)
    (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) (k : Fin 2 → ℤ) :
    IsLeast {E : ℝ | ∃ ω : Fin n₁ ⊕ Fin n₂ → ℝ,
        (∀ j, ω ⬝ᵥ wedgeCycles n₁ n₂ j = (k j : ℝ)) ∧ E = ω ⬝ᵥ ω}
      ((wedgeHarmonicGramData n₁ n₂ h₁ h₂).energy k) := by
  rw [← wedgePeriodData_energy_eq n₁ n₂ h₁ h₂ k]
  exact HarmonicGramData.ofCycles_energy_isLeast (V := Fin n₁ ⊕ Fin n₂)
    (wedgeCycles n₁ n₂)
    (gramOf_wedgeCycles_posDef n₁ n₂ (by omega) (by omega)) k
/-- The wedge matter's mass is `1/n₁`: presentation → derived Gram →
asserted Gram, one chain of identifications. -/
theorem wedgeMatter₁_mass (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3) :
    (wedgeMatter₁ n₁ n₂ h₁ h₂).mass = 1 / n₁ := by
  show (wedgePeriodData n₁ n₂ (by omega) (by omega)).energy ![1, 0] = 1 / n₁
  rw [wedgePeriodData_energy_eq n₁ n₂ h₁ h₂,
    wedgeHarmonicGramData_energy_basis₁]


end PeriodUnification

end Meno
