import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Sector Action: the analytic primitive

A `SectorAction` is the triple `(Λ, E, summable)` underlying Meno's analytic
content: a sector type `Λ`, a non-negative energy `E : Λ → ℝ` attaining zero
somewhere, and summability of the Boltzmann weight `exp(-E k)`. From this we
derive the partition function `Z = ∑' exp(-E)`, the complexity `K = log Z`,
the Gibbs density `μ = exp(-E) / Z` (a probability on `Λ`), the expectation
`⟨f⟩`, and the variance `Var(f) = ⟨f²⟩ - ⟨f⟩²`.

Two combinators are provided:

* `prod`: independent product, `Λ := A.Λ × B.Λ`, energies add, partition
  functions multiply.
* `sum`: disjoint union, `Λ := A.Λ ⊕ B.Λ`, partition functions add.

This file is foundational: subsequent files specialise the analytic
primitive — categorical, simplicial, harmonic, type-level — to reduce
their content to `SectorAction` data plus algebraic structure. -/

namespace Meno

universe u v

open scoped BigOperators

/-- A sector action: a sector type `Λ` with a non-negative energy `E`
attaining zero, whose Boltzmann weight `exp(-E)` is summable. -/
structure SectorAction where
  Λ : Type u
  E : Λ → ℝ
  E_zero : ∃ z : Λ, E z = 0
  E_nonneg : ∀ k, 0 ≤ E k
  summable : Summable (fun k => Real.exp (-E k))

namespace SectorAction

variable (A : SectorAction.{u})

/-- Boltzmann weight at sector `k`: `exp(-E k)`. -/
noncomputable def weight (k : A.Λ) : ℝ := Real.exp (-A.E k)

theorem weight_pos (k : A.Λ) : 0 < A.weight k := Real.exp_pos _

theorem weight_nonneg (k : A.Λ) : 0 ≤ A.weight k := (A.weight_pos k).le


/-- Partition function `Z = ∑' k, exp(-E k)`. -/
noncomputable def partFn : ℝ := ∑' k, A.weight k

/-- Complexity `K = log Z`. -/
noncomputable def complexity : ℝ := Real.log A.partFn

/-- Gibbs density `μ k = exp(-E k) / Z`. -/
noncomputable def gibbsMass (k : A.Λ) : ℝ := A.weight k / A.partFn

/-- Gibbs expectation of an observable `f : Λ → ℝ`. -/
noncomputable def gibbsExpect (f : A.Λ → ℝ) : ℝ := ∑' k, f k * A.gibbsMass k

/-- Gibbs variance of an observable: `⟨f²⟩ - ⟨f⟩²`. -/
noncomputable def gibbsVariance (f : A.Λ → ℝ) : ℝ :=
  A.gibbsExpect (fun k => f k ^ 2) - A.gibbsExpect f ^ 2

/-! ## Foundational lemmas -/

/-- The partition function is strictly positive: the zero-energy witness
contributes a positive term to a summable, non-negative series. -/
theorem partFn_pos : 0 < A.partFn := by
  obtain ⟨z, _⟩ := A.E_zero
  exact A.summable.tsum_pos (fun k => A.weight_nonneg k) z (A.weight_pos z)


/-- The Gibbs density is non-negative. -/
theorem gibbsMass_nonneg (k : A.Λ) : 0 ≤ A.gibbsMass k :=
  div_nonneg (A.weight_nonneg k) A.partFn_pos.le

/-- The Gibbs density is strictly positive: every sector carries
weight. -/
theorem gibbsMass_pos (k : A.Λ) : 0 < A.gibbsMass k :=
  div_pos (A.weight_pos k) A.partFn_pos

/-- The Gibbs density is summable. -/
theorem summable_gibbsMass : Summable A.gibbsMass := by
  show Summable (fun k => A.weight k / A.partFn)
  exact A.summable.div_const _

/-- The Gibbs density integrates to 1: it is a probability density on `Λ`. -/
theorem tsum_gibbsMass_eq_one : ∑' k, A.gibbsMass k = 1 := by
  show ∑' k, A.weight k / A.partFn = 1
  rw [tsum_div_const]
  exact div_self (ne_of_gt A.partFn_pos)


/-- The centered second moment is summable when both raw moments
are. -/
theorem summable_sq_sub_gibbs (f : A.Λ → ℝ)
    (hsq : Summable (fun k => f k ^ 2 * A.gibbsMass k))
    (hf : Summable (fun k => f k * A.gibbsMass k)) :
    Summable (fun k => (f k - A.gibbsExpect f) ^ 2 * A.gibbsMass k) := by
  set c := A.gibbsExpect f with hc
  have hfc : Summable (fun k => 2 * c * (f k * A.gibbsMass k)) :=
    hf.mul_left (2 * c)
  have hc2 : Summable (fun k => c ^ 2 * A.gibbsMass k) :=
    A.summable_gibbsMass.mul_left (c ^ 2)
  refine ((hsq.sub hfc).add hc2).congr ?_
  intro k; ring

/-- **The variance is the centered second moment** (review #14): with
both raw moments summable, `Var(f) = ∑' (f − ⟨f⟩)² · μ` — the closed
form behind both the nonnegativity and the strict positivity of Gibbs
fluctuation. -/
theorem gibbsVariance_eq_tsum (f : A.Λ → ℝ)
    (hsq : Summable (fun k => f k ^ 2 * A.gibbsMass k))
    (hf : Summable (fun k => f k * A.gibbsMass k)) :
    A.gibbsVariance f
      = ∑' k, (f k - A.gibbsExpect f) ^ 2 * A.gibbsMass k := by
  set c := A.gibbsExpect f with hc
  have hfc : Summable (fun k => 2 * c * (f k * A.gibbsMass k)) :=
    hf.mul_left (2 * c)
  have hc2 : Summable (fun k => c ^ 2 * A.gibbsMass k) :=
    A.summable_gibbsMass.mul_left (c ^ 2)
  have hcong : (fun k => (f k - c) ^ 2 * A.gibbsMass k) =
      (fun k => f k ^ 2 * A.gibbsMass k - 2 * c * (f k * A.gibbsMass k)
                + c ^ 2 * A.gibbsMass k) := by funext k; ring
  have hT : ∑' k, (f k - c) ^ 2 * A.gibbsMass k = A.gibbsVariance f := by
    rw [hcong, (hsq.sub hfc).tsum_add hc2, hsq.tsum_sub hfc,
        tsum_mul_left, tsum_mul_left, A.tsum_gibbsMass_eq_one]
    show A.gibbsExpect (fun k => f k ^ 2) - 2 * c * A.gibbsExpect f + c ^ 2 * 1
      = A.gibbsVariance f
    show A.gibbsExpect (fun k => f k ^ 2) - 2 * c * A.gibbsExpect f + c ^ 2 * 1
      = A.gibbsExpect (fun k => f k ^ 2) - A.gibbsExpect f ^ 2
    have : c = A.gibbsExpect f := hc
    rw [this]; ring
  exact hT.symm

/-- Variance is non-negative when the relevant moments are summable.
The classical argument: `(f - ⟨f⟩)² · μ ≥ 0` pointwise; sum via the
centered-moment closed form. -/
theorem gibbsVariance_nonneg (f : A.Λ → ℝ)
    (hsq : Summable (fun k => f k ^ 2 * A.gibbsMass k))
    (hf : Summable (fun k => f k * A.gibbsMass k)) :
    0 ≤ A.gibbsVariance f := by
  rw [A.gibbsVariance_eq_tsum f hsq hf]
  exact tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (A.gibbsMass_nonneg k)

/-- **Strict Gibbs fluctuation** (review #14): an observable that
misses its own mean somewhere has strictly positive variance — every
sector carries positive Gibbs mass, so the centered term at the
witness is positive. -/
theorem gibbsVariance_pos (f : A.Λ → ℝ)
    (hsq : Summable (fun k => f k ^ 2 * A.gibbsMass k))
    (hf : Summable (fun k => f k * A.gibbsMass k))
    {k₀ : A.Λ} (hk₀ : f k₀ ≠ A.gibbsExpect f) :
    0 < A.gibbsVariance f := by
  rw [A.gibbsVariance_eq_tsum f hsq hf]
  refine (A.summable_sq_sub_gibbs f hsq hf).tsum_pos
    (fun k => mul_nonneg (sq_nonneg _) (A.gibbsMass_nonneg k)) k₀ ?_
  refine mul_pos ?_ (A.gibbsMass_pos k₀)
  exact lt_of_le_of_ne (sq_nonneg _)
    (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hk₀)))

/-! ## Product: independent sectors -/

/-- Independent product of sector actions: sectors are pairs, energies add,
weights multiply, partition functions multiply. -/
noncomputable def prod (A : SectorAction.{u}) (B : SectorAction.{v}) :
    SectorAction.{max u v} where
  Λ := A.Λ × B.Λ
  E := fun p => A.E p.1 + B.E p.2
  E_zero := by
    obtain ⟨a, ha⟩ := A.E_zero
    obtain ⟨b, hb⟩ := B.E_zero
    exact ⟨(a, b), by simp [ha, hb]⟩
  E_nonneg := fun p => add_nonneg (A.E_nonneg p.1) (B.E_nonneg p.2)
  summable := by
    -- weight (a,b) = exp(-E_A a - E_B b) = exp(-E_A a) * exp(-E_B b)
    have h := A.summable.mul_of_nonneg B.summable
      (fun k => A.weight_nonneg k) (fun k => B.weight_nonneg k)
    refine h.congr ?_
    intro p
    show Real.exp (-A.E p.1) * Real.exp (-B.E p.2) = Real.exp (-(A.E p.1 + B.E p.2))
    rw [← Real.exp_add]; ring_nf

/-- Weight of the product action factorizes. -/
theorem weight_prod (A : SectorAction.{u}) (B : SectorAction.{v}) (p : A.Λ × B.Λ) :
    (A.prod B).weight p = A.weight p.1 * B.weight p.2 := by
  show Real.exp (-(A.E p.1 + B.E p.2)) = Real.exp (-A.E p.1) * Real.exp (-B.E p.2)
  rw [← Real.exp_add]; ring_nf

/-- Partition function factorizes over an independent product. -/
theorem partFn_prod (A : SectorAction.{u}) (B : SectorAction.{v}) :
    (A.prod B).partFn = A.partFn * B.partFn := by
  show ∑' p : A.Λ × B.Λ, (A.prod B).weight p = (∑' a, A.weight a) * (∑' b, B.weight b)
  rw [show (fun p : A.Λ × B.Λ => (A.prod B).weight p)
      = (fun p : A.Λ × B.Λ => A.weight p.1 * B.weight p.2) from by
    funext p; exact weight_prod A B p]
  exact (A.summable.tsum_mul_tsum B.summable
    (A.summable.mul_of_nonneg B.summable
      (fun k => A.weight_nonneg k) (fun k => B.weight_nonneg k))).symm

/-- Complexity adds over an independent product. -/
theorem complexity_prod (A : SectorAction.{u}) (B : SectorAction.{v}) :
    (A.prod B).complexity = A.complexity + B.complexity := by
  show Real.log (A.prod B).partFn = Real.log A.partFn + Real.log B.partFn
  rw [partFn_prod, Real.log_mul (ne_of_gt A.partFn_pos) (ne_of_gt B.partFn_pos)]

/-! ## Energy-preserving equivalence -/

/-- **Energy-preserving equivalence of sector actions** (review #21):
a relabeling of sectors under which every sector keeps its energy.
The congruence the gravity theorem's decomposition lemmas are read
through (`complexity_congr`; `SectorAction.complexity_gravity`,
`Meno/InfoRatchet.lean`). -/
def EnergyEquiv (A B : SectorAction.{u}) : Prop :=
  ∃ e : A.Λ ≃ B.Λ, ∀ x, B.E (e x) = A.E x

/-- Partition functions agree across an energy-preserving
equivalence: the Boltzmann sum is reindexed, term by term. -/
theorem partFn_congr {A B : SectorAction.{u}} (h : A.EnergyEquiv B) :
    A.partFn = B.partFn := by
  obtain ⟨e, he⟩ := h
  show ∑' x, A.weight x = ∑' y, B.weight y
  rw [← Equiv.tsum_eq e B.weight]
  exact tsum_congr fun x => by
    show Real.exp (-A.E x) = Real.exp (-B.E (e x))
    rw [he x]

/-- Complexity agrees across an energy-preserving equivalence. -/
theorem complexity_congr {A B : SectorAction.{u}} (h : A.EnergyEquiv B) :
    A.complexity = B.complexity :=
  congrArg Real.log (partFn_congr h)

/-! ## Disjoint sum: mutually exclusive sectors -/

/-- Disjoint sum of sector actions: sectors are tagged unions, energies follow
the tag, partition functions add. -/
noncomputable def sum (A : SectorAction.{u}) (B : SectorAction.{v}) :
    SectorAction.{max u v} where
  Λ := A.Λ ⊕ B.Λ
  E := Sum.elim A.E B.E
  E_zero := by
    obtain ⟨a, ha⟩ := A.E_zero
    exact ⟨Sum.inl a, by simp [ha]⟩
  E_nonneg := fun s => by
    cases s with
    | inl a => exact A.E_nonneg a
    | inr b => exact B.E_nonneg b
  summable := by
    -- Both Sum.inl-component and Sum.inr-component are summable, so the sum is.
    refine Summable.sum (fun s => Real.exp (-(Sum.elim A.E B.E) s)) ?_ ?_
    · refine A.summable.congr ?_
      intro a; rfl
    · refine B.summable.congr ?_
      intro b; rfl


end SectorAction

end Meno
