import Meno.Binding
import Meno.BasisIndependence
import Meno.ResolutionCount
import Mathlib.Tactic.TFAE

/-! # The Completion Object: the Equivalence

Six statements, pairwise equivalent, at the top of the tree
(`meno_tfae`): a finite multigraph has cycles **iff** matter exists
**iff** the spectrum strictly exceeds the vacuum **iff** the
harmonic energy genuinely fluctuates **iff** every resolution
carries a strict information deficit **iff** every genuine
refinement of the tower is strictly priced. **Any one phenomenon
certifies all the others.**

Each phenomenon carries both directions by name:

* **matter** (`exists_matter` / `MatterSector.b1_pos`): with cycles
  a nonzero `H¹` class exists; a matter sector already forces
  cycles;
* **spectrum** (`one_lt_classPartFn` /
  `classPartFn_eq_one_of_b1_eq_zero`): with cycles the class
  partition function strictly exceeds the vacuum's unit weight; at
  `b₁ = 0` it collapses to exactly `1`;
* **fluctuation** (`classSectorAction_gibbsVariance_energy_pos` /
  `classSectorAction_gibbsVariance_energy_eq_zero_of_b1_eq_zero`):
  with cycles the harmonic energy genuinely fluctuates under the
  intrinsic Gibbs law; at `b₁ = 0` it is exactly still;
* **deficit** (`residueDefect_pos` /
  `residueDefect_eq_zero_of_b1_eq_zero`): with cycles, at every
  resolution `1 < q`, the Gibbs residue law sits strictly below
  maximal ignorance; at `b₁ = 0` the residue is a single class and
  the deficit is exactly zero;
* **arrow** (`sectionCost_h1TowerMap` /
  `sectionCost_h1TowerMap_eq_zero_of_b1_eq_zero`): reversing a
  genuine refinement step `q → c·q`, `1 < c`, costs `b₁·log c` per
  coarse sector — strictly positive with cycles, exactly free
  without.

All four vacuum collapses flow through one fact: at `b₁ = 0` every
integral class is zero (`h1Class_eq_zero_of_b1_eq_zero`, through
`MatterSector.b1_pos` — the keystone coordinates land in
`Fin 0 → ℤ`). `meno_dichotomy` is the conjunction chart of the
equivalence: the single biconditional
`0 < b₁ ↔ (matter ∧ spectrum ∧ fluctuation ∧ deficit ∧ arrow)`.

**The universe of the model is interesting exactly when it is
globally unsatisfiable.** Each engine is consumed by name, and each
sits at the top of its layer's stack: deleting any consumed engine,
or anything load-bearing beneath it, breaks this file. The faces
sharpen these phenomena at their corners; the completion consumes
the spine. -/

namespace Meno

universe u

/-! ## The vacuum: every phenomenon collapses at `b₁ = 0` -/

/-- **The vacuum keystone**: at `b₁ = 0` every integral cohomology
class is zero — the contrapositive of `MatterSector.b1_pos`, which
packages the keystone-coordinate argument. -/
theorem h1Class_eq_zero_of_b1_eq_zero (G : IncidenceGraph.{u})
    (hb : G.b1 = 0)
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) : κ = 0 := by
  by_contra hκ
  exact absurd (MatterSector.b1_pos ⟨κ, hκ⟩) (by omega)

/-- **The spectrum vacuum**: at `b₁ = 0` the class partition
function is exactly the vacuum's unit weight — the sum has one
term, `exp(−0) = 1`. -/
theorem classPartFn_eq_one_of_b1_eq_zero (G : IncidenceGraph.{u})
    (hb : G.b1 = 0) : G.classPartFn = 1 := by
  unfold IncidenceGraph.classPartFn
  rw [tsum_eq_single 0
    (fun κ hκ => absurd (h1Class_eq_zero_of_b1_eq_zero G hb κ) hκ)]
  rw [G.harmonicEnergy_zero, neg_zero, Real.exp_zero]

/-- **The fluctuation vacuum**: at `b₁ = 0` the intrinsic carrier's
energy variance is exactly zero — the harmonic energy is the zero
observable on a one-class lattice. -/
theorem classSectorAction_gibbsVariance_energy_eq_zero_of_b1_eq_zero
    (G : IncidenceGraph.{u}) (hb : G.b1 = 0) :
    (G.classSectorAction).gibbsVariance G.harmonicEnergy = 0 := by
  have hE : ∀ κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ),
      G.harmonicEnergy κ = 0 := fun κ => by
    rw [h1Class_eq_zero_of_b1_eq_zero G hb κ]
    exact G.harmonicEnergy_zero
  have hexp : ∀ f : (G.classSectorAction).Λ → ℝ, (∀ k, f k = 0) →
      (G.classSectorAction).gibbsExpect f = 0 := by
    intro f hf
    have hpt : (fun k => f k * (G.classSectorAction).gibbsMass k)
        = fun _ => (0 : ℝ) := by
      funext k
      simp only [hf k, zero_mul]
    unfold SectorAction.gibbsExpect
    rw [hpt, tsum_zero]
  unfold SectorAction.gibbsVariance
  rw [hexp _ (fun k => by simp only [hE k]; norm_num), hexp _ hE]
  norm_num

/-- **The deficit vacuum**: at `b₁ = 0` the finite reduction is a
single class, every distribution on it is uniform, and the
information deficit is exactly zero — at every resolution. -/
theorem residueDefect_eq_zero_of_b1_eq_zero (G : IncidenceGraph.{u})
    (q : ℕ) [NeZero q] (hb : G.b1 = 0) : G.residueDefect q = 0 := by
  have hsub : Subsingleton ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :=
    ⟨fun a b => (h1Class_eq_zero_of_b1_eq_zero G hb a).trans
      (h1Class_eq_zero_of_b1_eq_zero G hb b).symm⟩
  have : Subsingleton (IncidenceGraph.H1Reduction G q) := by
    constructor
    intro a b
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Subsingleton.elim x y]
  have : Unique (IncidenceGraph.H1Reduction G q) := uniqueOfSubsingleton 0
  have hmass : (G.residueDist q).mass 0 = 1 := by
    have h := (G.residueDist q).sum_one
    rwa [Fintype.sum_subsingleton _ (0 : IncidenceGraph.H1Reduction G q)] at h
  unfold IncidenceGraph.residueDefect FinDist.defect FinDist.entropy
    shannonEntropy
  rw [Fintype.card_unique,
    Fintype.sum_subsingleton _ (0 : IncidenceGraph.H1Reduction G q), hmass]
  norm_num [Real.log_one]

/-- **The arrow vacuum**: at `b₁ = 0` every tower step is free —
the fibers are singletons and the section cost is `0 · log c`. -/
theorem sectionCost_h1TowerMap_eq_zero_of_b1_eq_zero
    (G : IncidenceGraph.{u}) (q c : ℕ) [NeZero q] [NeZero c]
    (hb : G.b1 = 0) :
    sectionCost (⇑(G.h1TowerMap q (c * q) (dvd_mul_left q c))) = 0 := by
  have hcard : (0 : ℝ) < Nat.card (IncidenceGraph.H1Reduction G q) := by
    exact_mod_cast Nat.card_pos
  have hlaw := G.sectionCost_h1TowerMap q (c * q) c (dvd_mul_left q c) rfl
  rw [hb, div_eq_iff hcard.ne'] at hlaw
  simpa using hlaw

/-! ## The completion object -/

/-- **THE COMPLETION** (the equivalence): six statements, pairwise
equivalent — a finite multigraph has cycles **iff** matter exists
**iff** the spectrum strictly exceeds the vacuum **iff** the energy
fluctuates **iff** every resolution carries a strict information
deficit **iff** every genuine refinement of the tower is strictly
priced. **Any one phenomenon certifies all the others**: observe
fluctuation alone, and matter must exist. Forward: the five strict
engines, consumed by name. Reverse: matter's converse
(`MatterSector.b1_pos`) and the four vacuum collapses. -/
theorem meno_tfae (G : IncidenceGraph.{u}) :
    [0 < G.b1,
      Nonempty (MatterSector G),
      1 < G.classPartFn,
      0 < (G.classSectorAction).gibbsVariance G.harmonicEnergy,
      ∀ (q : ℕ) [NeZero q], 1 < q → 0 < G.residueDefect q,
      ∀ (q c : ℕ) [NeZero q] [NeZero c], 1 < c →
        0 < sectionCost
          (⇑(G.h1TowerMap q (c * q) (dvd_mul_left q c)))].TFAE := by
  tfae_have 1 → 2 := fun hb => exists_matter G hb
  tfae_have 2 → 1 := fun ⟨m⟩ => m.b1_pos
  tfae_have 1 → 3 := fun hb => G.one_lt_classPartFn hb
  tfae_have 3 → 1 := by
    intro h3
    by_contra hb
    rw [classPartFn_eq_one_of_b1_eq_zero G (by omega)] at h3
    exact lt_irrefl 1 h3
  tfae_have 1 → 4 := fun hb => G.classSectorAction_gibbsVariance_energy_pos hb
  tfae_have 4 → 1 := by
    intro h4
    by_contra hb
    rw [classSectorAction_gibbsVariance_energy_eq_zero_of_b1_eq_zero G
      (by omega)] at h4
    exact lt_irrefl 0 h4
  tfae_have 1 → 5 := by
    intro hb q _ hq
    exact G.residueDefect_pos q hb hq
  tfae_have 5 → 1 := by
    intro h5
    by_contra hb
    have : NeZero (2 : ℕ) := ⟨by norm_num⟩
    have h0 := residueDefect_eq_zero_of_b1_eq_zero G 2 (by omega)
    have hpos := h5 2 one_lt_two
    rw [h0] at hpos
    exact lt_irrefl 0 hpos
  tfae_have 1 → 6 := by
    intro hb q c _ _ hc
    have hcard : (0 : ℝ) < Nat.card (IncidenceGraph.H1Reduction G q) := by
      exact_mod_cast Nat.card_pos
    have hlaw := G.sectionCost_h1TowerMap q (c * q) c (dvd_mul_left q c) rfl
    rw [div_eq_iff hcard.ne'] at hlaw
    rw [hlaw]
    exact mul_pos (mul_pos (by exact_mod_cast hb)
      (Real.log_pos (by exact_mod_cast hc))) hcard
  tfae_have 6 → 1 := by
    intro h6
    by_contra hb
    have : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
    have : NeZero (2 : ℕ) := ⟨by norm_num⟩
    have h0 := sectionCost_h1TowerMap_eq_zero_of_b1_eq_zero G 1 2 (by omega)
    have hpos := h6 1 2 one_lt_two
    rw [h0] at hpos
    exact lt_irrefl 0 hpos
  tfae_finish

/-- **THE DICHOTOMY** (the conjunction chart of `meno_tfae`): a
finite multigraph has cycles **iff** matter exists, the spectrum
strictly exceeds the vacuum, the energy fluctuates, every
resolution carries a strict information deficit, and every genuine
refinement of the tower is strictly priced. -/
theorem meno_dichotomy (G : IncidenceGraph.{u}) :
    0 < G.b1 ↔
      Nonempty (MatterSector G)
      ∧ 1 < G.classPartFn
      ∧ 0 < (G.classSectorAction).gibbsVariance G.harmonicEnergy
      ∧ (∀ (q : ℕ) [NeZero q], 1 < q → 0 < G.residueDefect q)
      ∧ (∀ (q c : ℕ) [NeZero q] [NeZero c], 1 < c →
          0 < sectionCost (⇑(G.h1TowerMap q (c * q) (dvd_mul_left q c)))) := by
  have h := meno_tfae G
  constructor
  · intro hb
    exact ⟨(h.out 0 1).mp hb, (h.out 0 2).mp hb, (h.out 0 3).mp hb,
      (h.out 0 4).mp hb, (h.out 0 5).mp hb⟩
  · rintro ⟨hm, -, -, -, -⟩
    exact (h.out 0 1).mpr hm

end Meno
