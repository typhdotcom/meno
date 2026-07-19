import Meno.LoopKernel
import Meno.QuadraticAction
import Meno.SiegelPoisson
import Meno.LatticeAction

/-! # Sector Presentation: connecting categorical and quadratic layers

A `SectorPresentation L r` exhibits the loop kernel `L`'s sector action
as a quadratic action of rank `r`. The data:

* `coord : End L.base ≃ (Fin r → ℤ)` — a re-indexing of the categorical
  endomorphism monoid as the integer lattice `Fin r → ℤ`.
* `coord_one`, `coord_comp` — the structural compatibility: composition
  in `End L.base` corresponds to addition in the lattice. Together these
  promote `coord` to a monoid isomorphism (between the multiplicative
  `End` and the additive `Fin r → ℤ`).
* `Q`, `Q_posDef` — the Gram form of the quadratic action (symmetry
  is derived, review #6).
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
  Q_posDef : Q.PosDef
  /-- Energy on the loop kernel is the quadratic form in lattice
  coordinates. -/
  energy_eq : ∀ g : End L.base,
    L.energy g = ∑ i, ∑ j, Q i j * ((coord g) i : ℝ) * ((coord g) j : ℝ)

namespace SectorPresentation

variable {L : LoopKernelObj.{u, v}} {r : ℕ} (P : SectorPresentation L r)

/-- Symmetry of the presentation's Gram form — a theorem of
positive-definiteness over ℝ, with the retired field's name and
statement (review #6). -/
theorem Q_symm : P.Q.IsSymm := P.Q_posDef.isSymm

/-- The quadratic action induced by a presentation. Summability is a
theorem of every quadratic action (`QuadraticAction.summable`) — the
old transport of `L.summable` through the `coord` equivalence is no
longer needed to build the action. -/
noncomputable def toQuadraticAction : QuadraticAction r where
  Q := P.Q
  Q_posDef := P.Q_posDef

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

include P in
/-- **Presentations force commutativity**: `coord` is injective and
sends composition to addition, so `End L.base` must be commutative.

Contrapositive: a loop kernel with nonabelian endomorphism monoid —
e.g. the wedge of two cycles, whose loop monoid is the free group on
two generators — admits **no** sector presentation, at any rank. For
such spaces the analytic layer cannot live on `End` at all: every `H₁`
sector contains infinitely many endomorphisms of equal energy, so the
Boltzmann sum over `End` diverges. Sectors must be homology classes
(the abelianization), and the bridge from a nonabelian `π₁` is a
quotient map onto `ℤ^r`, not an equivalence. This theorem is what makes
the spine's "sector = homology class" formulation forced rather than
conventional. -/
theorem end_comm (g h : End L.base) : g ≫ h = h ≫ g := by
  apply P.coord.injective
  rw [P.coord_comp, P.coord_comp, add_comm]

/-! ## The categorical dual via a presentation (Phase 6 target)

With the general dual available (`Meno/SiegelPoisson.lean`), the
categorical dual is transport: same category, same basepoint, energy
pulled back from the dual quadratic action `π²·Q⁻¹` through the same
coordinates. The **same** `coord` then presents the dual object as the
dual action, and the categorical duality theorem is a two-line
consequence of `QuadraticAction.duality_via_lattice` — the coordinate
duality re-derived through the canonical embedding into
`QuadLatticeAction` (review #12), so the direct analytic invocation of
`QuadraticAction.duality` occurs once globally, inside
`QuadLatticeAction.duality`. -/

/-- The dual loop kernel through a presentation: energy is the dual
quadratic action's energy in the presentation's coordinates. -/
noncomputable def _root_.Meno.LoopKernelObj.dualVia
    (P : SectorPresentation L r) : LoopKernelObj.{u, v} where
  C := L.C
  cat := L.cat
  base := L.base
  energy g := P.toQuadraticAction.dual.energy (P.coord g)
  energy_id := by
    rw [P.coord_one]
    exact P.toQuadraticAction.dual.energy_zero
  energy_nonneg g := P.toQuadraticAction.dual.energy_nonneg _
  summable :=
    P.coord.summable_iff.mpr P.toQuadraticAction.dual.summable

/-- The presentation of the dual: the same coordinates exhibit
`L.dualVia P` as the dual quadratic action. -/
noncomputable def dualPresentation (P : SectorPresentation L r) :
    SectorPresentation (LoopKernelObj.dualVia P) r where
  coord := P.coord
  coord_one := P.coord_one
  coord_comp := P.coord_comp
  Q := P.toQuadraticAction.dual.Q
  Q_posDef := P.toQuadraticAction.dual.Q_posDef
  energy_eq _ := rfl

/-- The dual object's partition function is the dual action's. -/
theorem dualVia_partFn (P : SectorPresentation L r) :
    (LoopKernelObj.dualVia P).partFn
      = P.toQuadraticAction.dual.toSectorAction.partFn := by
  rw [(P.dualPresentation).partFn_eq]
  exact QuadraticAction.partFn_eq_of_Q_eq _ _ rfl

/-- **Categorical Siegel–Poisson duality**: the partition function of
the dual loop kernel is `√(det Q / π^r)` times the original's, for any
loop kernel admitting a presentation — at any rank, any Gram form.
Phase 6's `dualVia_partFn` target, now at full generality — derived
through the canonical embedding into `QuadLatticeAction`
(review #12). -/
theorem dualVia_partFn_duality (P : SectorPresentation L r) :
    ((LoopKernelObj.dualVia P).partFn : ℂ)
      = ↑(P.Q.det / Real.pi ^ r : ℝ) ^ ((1 : ℂ) / 2) * ↑L.partFn := by
  rw [dualVia_partFn P, P.partFn_eq]
  exact P.toQuadraticAction.duality_via_lattice

end SectorPresentation

end Meno
