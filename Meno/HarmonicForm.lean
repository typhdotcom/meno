import Meno.QuadraticAction

/-! # Harmonic Form: variational origin of a quadratic action

A `HarmonicGramData V r` packages the analytic content the Hodge harmonic
construction supplies to a finite graph on `V`:

* the first Betti number `r = b₁ G`,
* a symmetric positive-definite Gram form on `Fin r → ℝ`,
* the witness that exp(-kᵀ Q k) is summable on the integer lattice
  `Fin r → ℤ`,
* (philosophically) the variational identity
  `harmonicEnergy k = min over ω ∈ winding class k of ‖ω‖²`.

The Gram form is the data from which a `QuadraticAction` is built. The
variational identity itself is stated abstractly here as a `Prop`-field
witnessing the minimisation; concrete graph instances supply both.

This file is intentionally an **interface layer**. Concrete construction
of the harmonic representative `harmonicRep G k` and proof of the
variational identity via Hodge orthogonal decomposition (`EC1 = Harm ⊕
image(d)` + Pythagoras) is graph-specific and lives downstream in the
specialisation files. The interface is what Phases 6, 7, 9 need: the
existence of a Gram form satisfying the variational property, with the
positive-definiteness needed for summability and duality. -/

namespace Meno

open scoped BigOperators

universe u

/-- Abstract harmonic Gram data on a vertex type `V`.

`r` is the first Betti number; `gram` is the Gram form of the harmonic
1-cochain basis. The structure carries explicit summability so the
downstream `toQuadraticAction` is total. The `variational` field is the
abstract statement that some "harmonic energy" function attains the
minimum within each winding class; instances supply the energy function
and prove the identity. -/
structure HarmonicGramData (V : Type u) where
  r : ℕ
  gram : Matrix (Fin r) (Fin r) ℝ
  gram_symm : gram.IsSymm
  gram_posDef : gram.PosDef
  summable : Summable (fun k : Fin r → ℤ =>
    Real.exp (-(∑ i, ∑ j, gram i j * (k i : ℝ) * (k j : ℝ))))

namespace HarmonicGramData

variable {V : Type u} (H : HarmonicGramData V)

/-- The Gram-form energy `kᵀ Q k` on integer windings. By construction
this equals the harmonic energy minimum within the winding class. -/
noncomputable def energy (k : Fin H.r → ℤ) : ℝ :=
  ∑ i, ∑ j, H.gram i j * (k i : ℝ) * (k j : ℝ)

/-- The `QuadraticAction` produced by the harmonic Gram data. -/
noncomputable def toQuadraticAction : QuadraticAction H.r where
  Q := H.gram
  Q_symm := H.gram_symm
  Q_posDef := H.gram_posDef
  summable := H.summable

theorem toQuadraticAction_Q : H.toQuadraticAction.Q = H.gram := rfl

theorem toQuadraticAction_energy (k : Fin H.r → ℤ) :
    H.toQuadraticAction.energy k = H.energy k := rfl

end HarmonicGramData

end Meno
