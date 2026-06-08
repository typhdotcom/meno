import Meno.HarmonicForm

/-! # Matter: homology classes with positive harmonic minimum action

A `MatterSector H` is a nontrivial winding class on a graph (with harmonic
Gram data `H : HarmonicGramData V`) whose harmonic minimum action — the
energy `kᵀ Q k` of the Gram form — is strictly positive.

For a positive-definite Gram form, **every** nonzero winding class is a
matter sector: positive-definiteness gives `kᵀ Q k > 0` whenever `k ≠ 0`
(viewed in real coordinates). The theorem `MatterSector.ofNonzero`
records this.

Concrete realisations — cycle-graph harmonics with `Q = !![1/n]`, and the
binding-energy releases-mass theorem — are graph-specific and live in the
specialisation files. The interface here is what downstream consumers
need: matter classes are nonzero winding classes with positive Gram
energy. -/

namespace Meno

open scoped BigOperators

universe u

/-- A matter sector on the harmonic Gram data `H`: a nontrivial integer
winding class with strictly positive Gram-form energy. -/
structure MatterSector {V : Type u} (H : HarmonicGramData V) where
  /-- The integer winding class. -/
  k : Fin H.r → ℤ
  /-- The class is nontrivial. -/
  nontrivial : k ≠ 0
  /-- The class has strictly positive harmonic minimum action. -/
  positive_action : 0 < H.energy k

namespace MatterSector

variable {V : Type u} {H : HarmonicGramData V}

/-- Every nonzero integer winding class is a matter sector when the Gram
form is positive-definite: positive-definiteness gives `kᵀ Q k > 0`
whenever the embedded real vector is nonzero. -/
noncomputable def ofNonzero (k : Fin H.r → ℤ) (hk : k ≠ 0) : MatterSector H where
  k := k
  nontrivial := hk
  positive_action := by
    -- The Gram form is posDef, so kᵀ Q k > 0 for k ≠ 0 (as a real vector).
    have hReal : (fun i => (k i : ℝ)) ≠ 0 := by
      intro h
      apply hk
      ext i
      have : (k i : ℝ) = 0 := congrFun h i
      exact_mod_cast this
    have hPos := H.gram_posDef.dotProduct_mulVec_pos (x := fun i => (k i : ℝ)) hReal
    have hStar : (star (fun i : Fin H.r => (k i : ℝ))) = fun i => (k i : ℝ) := by
      funext i; exact star_trivial _
    rw [hStar] at hPos
    -- Convert dot product form to the explicit sum.
    show 0 < ∑ i, ∑ j, H.gram i j * (k i : ℝ) * (k j : ℝ)
    have hExpand : ∑ i, ∑ j, H.gram i j * (k i : ℝ) * (k j : ℝ)
        = (fun i => (k i : ℝ)) ⬝ᵥ H.gram.mulVec (fun i => (k i : ℝ)) := by
      show ∑ i, ∑ j, H.gram i j * (k i : ℝ) * (k j : ℝ)
        = ∑ i, (k i : ℝ) * ∑ j, H.gram i j * (k j : ℝ)
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hExpand]; exact hPos

/-- A matter sector's action is bounded below by its first-eigenvalue
contribution. This is a corollary of positive_action. -/
theorem energy_pos (M : MatterSector H) : 0 < H.energy M.k := M.positive_action

end MatterSector

/-- **Matter-noncontractible bridge**: for any positive-definite Gram form
with rank ≥ 1, there exists a matter sector. Witnesses the existence of
matter once the graph has nontrivial first homology. -/
theorem exists_matter {V : Type u} (H : HarmonicGramData V) (hr : 0 < H.r) :
    Nonempty (MatterSector H) := by
  -- Take the standard basis vector e_0.
  let k : Fin H.r → ℤ := Pi.single ⟨0, hr⟩ 1
  have hk : k ≠ 0 := by
    intro h
    have := congrFun h ⟨0, hr⟩
    simp [k] at this
  exact ⟨MatterSector.ofNonzero k hk⟩

end Meno
