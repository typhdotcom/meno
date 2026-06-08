import Meno.LoopKernel
import Meno.QuadraticAction

/-! # Sector Presentation: connecting categorical and quadratic layers

A `SectorPresentation L r` exhibits the loop kernel `L`'s sector action
as a quadratic action of rank `r`. The data:

* `coord : End L.base ≃ (Fin r → ℤ)` — a re-indexing of the categorical
  endomorphism monoid as the integer lattice `Fin r → ℤ`.
* `coord_one`, `coord_comp` — the structural compatibility: composition
  in `End L.base` corresponds to addition in the lattice. Together these
  promote `coord` to a monoid isomorphism (between the multiplicative
  `End` and the additive `Fin r → ℤ`).
* `Q`, `Q_symm`, `Q_posDef` — the Gram form of the quadratic action.
* `energy_eq` — the energy on the loop kernel coincides with the
  quadratic form in lattice coordinates.

From a presentation, we transport partition functions: `L.partFn`
equals the partition function of the associated quadratic action.

The structural compatibility (`coord_one`, `coord_comp`) is the
load-bearing piece that makes downstream **categorical duality** (Phase
6's `dualVia`) coherent: bare set equivalence suffices for the analytic
identity but structural duality requires composition correspondence. -/

namespace Meno

open scoped BigOperators
open CategoryTheory

universe u v

/-- A presentation of a loop kernel's sector action as a quadratic action
of rank `r`. -/
structure SectorPresentation (L : LoopKernelObj.{u, v}) (r : ℕ) where
  /-- Re-indexing of `End L.base` as the lattice `Fin r → ℤ`. -/
  coord : End L.base ≃ (Fin r → ℤ)
  /-- Identity maps to zero. -/
  coord_one : coord (𝟙 L.base) = 0
  /-- Composition maps to addition. -/
  coord_comp : ∀ g h : End L.base, coord (g ≫ h) = coord g + coord h
  /-- Gram form of the quadratic action. -/
  Q : Matrix (Fin r) (Fin r) ℝ
  Q_symm : Q.IsSymm
  Q_posDef : Q.PosDef
  /-- Energy on the loop kernel is the quadratic form in lattice
  coordinates. -/
  energy_eq : ∀ g : End L.base,
    L.energy g = ∑ i, ∑ j, Q i j * ((coord g) i : ℝ) * ((coord g) j : ℝ)

namespace SectorPresentation

variable {L : LoopKernelObj.{u, v}} {r : ℕ} (P : SectorPresentation L r)

/-- The quadratic action induced by a presentation. Summability is
transported from `L.summable` via the `coord` equivalence. -/
noncomputable def toQuadraticAction : QuadraticAction r where
  Q := P.Q
  Q_symm := P.Q_symm
  Q_posDef := P.Q_posDef
  summable := by
    -- Transport L.summable through the coord equivalence and energy_eq.
    refine (P.coord.symm.summable_iff.mpr L.summable).congr ?_
    intro k
    -- Energy of L at coord.symm k equals the quadratic form at k.
    have hg : L.energy (P.coord.symm k) =
        ∑ i, ∑ j, P.Q i j * (k i : ℝ) * (k j : ℝ) := by
      rw [P.energy_eq (P.coord.symm k), P.coord.apply_symm_apply]
    show Real.exp (-L.energy (P.coord.symm k))
      = Real.exp (-(∑ i, ∑ j, P.Q i j * (k i : ℝ) * (k j : ℝ)))
    rw [hg]

/-- The partition function transports: `L.partFn` equals the partition
function of the induced quadratic action. -/
theorem partFn_eq : L.partFn = P.toQuadraticAction.toSectorAction.partFn := by
  show ∑' g : End L.base, Real.exp (-L.energy g)
    = ∑' k : Fin r → ℤ,
      Real.exp (-(∑ i, ∑ j, P.Q i j * (k i : ℝ) * (k j : ℝ)))
  rw [← P.coord.tsum_eq (fun k => Real.exp (-(∑ i, ∑ j,
        P.Q i j * (k i : ℝ) * (k j : ℝ))))]
  refine tsum_congr (fun g => ?_)
  have hg : L.energy g =
      ∑ i, ∑ j, P.Q i j * ((P.coord g) i : ℝ) * ((P.coord g) j : ℝ) :=
    P.energy_eq g
  rw [hg]

/-- The complexity transports. -/
theorem complexity_eq :
    L.complexity = P.toQuadraticAction.toSectorAction.complexity := by
  show Real.log L.partFn = Real.log P.toQuadraticAction.toSectorAction.partFn
  rw [P.partFn_eq]

end SectorPresentation

end Meno
