import Meno.Simplicial
import Meno.Geodesic
import Meno.SectorPresentation
import Meno.CycleHarmonic
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Fundamental Groupoid and Groupoid Complexity

The simplicial model builds a groupoid from any 2-complex with symmetric edges:
objects = vertices, morphisms = homotopy classes of walks. The partition function
over automorphisms defines complexity C(G) = log Z, with its product law proved
directly on it. -/

namespace Simplicial

open CategoryTheory

universe u

variable {V : Type u}

/-! ## The Fundamental Groupoid -/

/-- Objects of the fundamental groupoid of a complex. -/
structure SimplicialGroupoid (C : Complex V) where
  as : V

/-- Composition of homotopy classes via Quot.lift. -/
private def homotopyClassComp (C : Complex V) (u v w : V) :
    HomotopyClass₂ C u v → HomotopyClass₂ C v w → HomotopyClass₂ C u w :=
  fun a b =>
    Quot.lift (fun p =>
      Quot.lift (fun q => Quot.mk _ (p.append q))
        (fun _ _ hq => Quot.sound (Homotopic₂.congr_append_right C p hq)) b)
      (fun _ _ hp => by
        induction b using Quot.ind with | mk q =>
        exact Quot.sound (Homotopic₂.congr_append C hp (Homotopic₂.refl q))) a

/-- Inverse of homotopy classes. -/
private def homotopyClassInv (C : Complex V) (hsym : C.toGraph.Symmetric) (u v : V) :
    HomotopyClass₂ C u v → HomotopyClass₂ C v u :=
  Quot.lift (fun p => Quot.mk _ (p.reverse hsym))
    (fun _ _ h => Quot.sound (Homotopic₂.reverse hsym h))

/-- The fundamental groupoid of a symmetric 2-complex. -/
noncomputable instance simplicialGroupoid (C : Complex V) (hsym : C.toGraph.Symmetric) :
    Groupoid (SimplicialGroupoid C) where
  Hom x y := HomotopyClass₂ C x.as y.as
  id x := Quot.mk _ (Walk.nil x.as)
  comp f g := homotopyClassComp C _ _ _ f g
  id_comp f := by
    induction f using Quot.ind with | mk p => exact Quot.sound (Homotopic₂.refl p)
  comp_id f := by
    induction f using Quot.ind with | mk p =>
    show homotopyClassComp C _ _ _ (Quot.mk _ p) (Quot.mk _ (Walk.nil _)) = Quot.mk _ p
    simp only [homotopyClassComp]
    exact Quot.sound (by rw [Walk.append_nil]; exact Homotopic₂.refl p)
  assoc f g h := by
    induction f using Quot.ind with | mk p =>
    induction g using Quot.ind with | mk q =>
    induction h using Quot.ind with | mk r =>
    show homotopyClassComp C _ _ _ (homotopyClassComp C _ _ _ (Quot.mk _ p) (Quot.mk _ q)) (Quot.mk _ r) =
         homotopyClassComp C _ _ _ (Quot.mk _ p) (homotopyClassComp C _ _ _ (Quot.mk _ q) (Quot.mk _ r))
    simp only [homotopyClassComp]
    exact Quot.sound (by rw [Walk.append_assoc]; exact Homotopic₂.refl _)
  inv f := homotopyClassInv C hsym _ _ f
  inv_comp f := by
    induction f using Quot.ind with | mk p =>
    show homotopyClassComp C _ _ _ (homotopyClassInv C hsym _ _ (Quot.mk _ p)) (Quot.mk _ p) = _
    simp only [homotopyClassInv, homotopyClassComp]
    exact Quot.sound (reverse_append_homotopic hsym p)
  comp_inv f := by
    induction f using Quot.ind with | mk p =>
    show homotopyClassComp C _ _ _ (Quot.mk _ p) (homotopyClassInv C hsym _ _ (Quot.mk _ p)) = _
    simp only [homotopyClassInv, homotopyClassComp]
    exact Quot.sound (append_reverse_homotopic hsym p)

/-- Canonical groupoid instance for cycle graphs, using `cycleGraph_symmetric`. -/
noncomputable instance cycleGraphGroupoid (n : ℕ) (hn : n ≥ 3) :
    Groupoid (SimplicialGroupoid (CycleGraph n hn)) :=
  simplicialGroupoid (C := CycleGraph n hn) (cycleGraph_symmetric n hn)

/-! ## Groupoid Complexity via Partition Functions -/

/-- Partition function over endomorphisms of a groupoid object. -/
noncomputable def groupoidPartitionFn
    {C : Type*} [Groupoid C] (x : C)
    (K : End x → ℝ)
    (_hsum : Summable (fun g => Real.exp (-K g))) : ℝ :=
  ∑' g : End x, Real.exp (-K g)

/-- Complexity of a groupoid object: log of the partition function. -/
noncomputable def groupoidComplexity
    {C : Type*} [Groupoid C] (x : C)
    (K : End x → ℝ)
    (hsum : Summable (fun g => Real.exp (-K g))) : ℝ :=
  Real.log (groupoidPartitionFn x K hsum)

/-- The partition function is positive (sum of exponentials). -/
theorem groupoidPartitionFn_pos
    {C : Type*} [Groupoid C] (x : C)
    (K : End x → ℝ)
    (hsum : Summable (fun g => Real.exp (-K g))) :
    0 < groupoidPartitionFn x K hsum := by
  exact hsum.tsum_pos (fun g => le_of_lt (Real.exp_pos _)) (𝟙 x) (Real.exp_pos _)

/-! ## Complexity laws of the groupoid measure

Groupoid complexity is `C(x) = log Z` over automorphism Boltzmann
sums. This section keeps exactly what downstream code consumes:
additivity under a factoring of `Z` (`groupoidComplexity_prod`,
feeding `GroupoidObj.prod_complexity`) and, below, the
energy-preserving equivalence (`GroupoidObj.Equiv`) — both read by
the duality wrappers in `Meno/Duality.lean`. (Reviews #25, #26: the
former hierarchy-axioms mirror of the deleted type-level classes,
its trivial and congruence laws, and the consumerless sigma
capacity sub-layer are deleted.) -/

/-- When the partition function factors, complexity is additive. -/
theorem groupoidComplexity_prod
    {C : Type*} [Groupoid C] (x : C)
    (K : End x → ℝ) (hsum : Summable (fun g => Real.exp (-K g)))
    (Z₁ Z₂ : ℝ) (hZ₁ : 0 < Z₁) (hZ₂ : 0 < Z₂)
    (hfactor : groupoidPartitionFn x K hsum = Z₁ * Z₂) :
    groupoidComplexity x K hsum = Real.log Z₁ + Real.log Z₂ := by
  simp only [groupoidComplexity, hfactor,
    Real.log_mul (ne_of_gt hZ₁) (ne_of_gt hZ₂)]

/-! ## Cycle Graph Instance -/

/-- On the cycle graph, the groupoid partition function (given a winding number
    classification of loops) equals the concrete partition function. -/
theorem cycleGroupoid_partitionFn_eq (n : ℕ) (hn : n ≥ 3)
    {C : Type*} [Groupoid C] (x : C)
    (K : End x → ℝ)
    (hsum : Summable (fun g => Real.exp (-K g)))
    (wind : End x ≃ ℤ)
    (hK : ∀ g, K g = (wind g : ℝ) ^ 2 / n) :
    groupoidPartitionFn x K hsum = partitionFn n hn := by
  unfold groupoidPartitionFn partitionFn
  conv_lhs =>
    rw [show (fun g => Real.exp (-K g)) =
        (fun k : ℤ => Real.exp (-(k : ℝ) ^ 2 / ↑n)) ∘ wind from by
      ext g; rw [Function.comp_apply, hK g]; ring_nf]
  exact Equiv.tsum_eq wind (fun k : ℤ => Real.exp (-(k : ℝ) ^ 2 / ↑n))

/-- Canonical winding coordinate on cycle-loop endomorphisms,
    induced by the proved equivalence `End(x) ≃ ℤ`. -/
noncomputable def cycleCanonicalWinding (n : ℕ) (hn : n ≥ 3)
    (x : SimplicialGroupoid (CycleGraph n hn)) :
    End x → ℤ :=
  cycleLoopClassEquivInt n hn x.as

/-- Canonical cycle energy on endomorphisms: quadratic in canonical winding. -/
noncomputable def cycleCanonicalEnergy (n : ℕ) (hn : n ≥ 3)
    (x : SimplicialGroupoid (CycleGraph n hn)) :
    End x → ℝ :=
  cycleLoopClassHodgeEnergy n hn x.as

/-- The canonical cycle energy is exactly winding-square over n. -/
theorem cycleCanonicalEnergy_eq_winding_sq (n : ℕ) (hn : n ≥ 3)
    (x : SimplicialGroupoid (CycleGraph n hn))
    (g : End x) :
    cycleCanonicalEnergy n hn x g = (cycleCanonicalWinding n hn x g : ℝ) ^ 2 / n := by
  simpa [cycleCanonicalEnergy, cycleCanonicalWinding] using
    (cycleLoopClassHodgeEnergy_eq_winding_sq n hn x.as g)

/-- Summability of canonical cycle energy weights, transported along `End x ≃ ℤ`. -/
theorem summable_cycleCanonicalEnergy (n : ℕ) (hn : n ≥ 3)
    (x : SimplicialGroupoid (CycleGraph n hn)) :
    Summable (fun g : End x => Real.exp (-(cycleCanonicalEnergy n hn x g))) := by
  let wind : End x ≃ ℤ := cycleLoopClassEquivInt n hn x.as
  have hsumZ : Summable (fun k : ℤ => Real.exp (-((k : ℝ) ^ 2 / ↑n))) := by
    refine (summable_partitionFn n hn).congr ?_
    intro k
    congr 1
    ring
  have hcomp :
      (fun g : End x => Real.exp (-(cycleCanonicalEnergy n hn x g))) =
      (fun k : ℤ => Real.exp (-((k : ℝ) ^ 2 / ↑n))) ∘ wind := by
    funext g
    change Real.exp (-(cycleCanonicalEnergy n hn x g)) =
      Real.exp (-((wind g : ℝ) ^ 2 / ↑n))
    rw [cycleCanonicalEnergy_eq_winding_sq n hn x g]
    rfl
  rw [hcomp]
  exact wind.summable_iff.mpr hsumZ

/-- The canonical winding of the identity loop is zero. -/
theorem cycleCanonicalWinding_id (n : ℕ) (hn : n ≥ 3)
    (x : SimplicialGroupoid (CycleGraph n hn)) :
    cycleCanonicalWinding n hn x (𝟙 x) = 0 := by
  show (Walk.nil x.as : Walk (CycleGraph n hn).toGraph x.as x.as).loopWinding = 0
  simp

/-- The canonical winding is additive under loop composition: winding is
a monoid morphism `(End x, ≫) → (ℤ, +)`. Reduces to `loopWinding_append`
through the `Quot.lift` computation rule. -/
theorem cycleCanonicalWinding_comp (n : ℕ) (hn : n ≥ 3)
    (x : SimplicialGroupoid (CycleGraph n hn)) (g h : End x) :
    cycleCanonicalWinding n hn x (g ≫ h) =
    cycleCanonicalWinding n hn x g + cycleCanonicalWinding n hn x h := by
  refine Quot.inductionOn g (fun p => ?_)
  refine Quot.inductionOn h (fun q => ?_)
  show (p.append q).loopWinding = p.loopWinding + q.loopWinding
  exact Walk.loopWinding_append p q

/-- The canonical cycle energy vanishes on the identity loop. -/
theorem cycleCanonicalEnergy_id (n : ℕ) (hn : n ≥ 3)
    (x : SimplicialGroupoid (CycleGraph n hn)) :
    cycleCanonicalEnergy n hn x (𝟙 x) = 0 := by
  rw [cycleCanonicalEnergy_eq_winding_sq, cycleCanonicalWinding_id]
  simp

/-- The canonical cycle energy is non-negative. -/
theorem cycleCanonicalEnergy_nonneg (n : ℕ) (hn : n ≥ 3)
    (x : SimplicialGroupoid (CycleGraph n hn)) (g : End x) :
    0 ≤ cycleCanonicalEnergy n hn x g := by
  rw [cycleCanonicalEnergy_eq_winding_sq]
  positivity

/-- Canonical cycle partition identity with no extra hypotheses:
    both energy and summability are derived canonically. -/
theorem cycleGroupoid_partitionFn_eq_canonical_energy (n : ℕ) (hn : n ≥ 3)
    (x : SimplicialGroupoid (CycleGraph n hn)) :
    groupoidPartitionFn x (cycleCanonicalEnergy n hn x)
      (summable_cycleCanonicalEnergy n hn x) = partitionFn n hn := by
  let wind : End x ≃ ℤ := cycleLoopClassEquivInt n hn x.as
  refine cycleGroupoid_partitionFn_eq n hn x (cycleCanonicalEnergy n hn x)
    (summable_cycleCanonicalEnergy n hn x) wind ?_
  intro g
  simpa [cycleCanonicalEnergy, wind] using
    (cycleLoopClassHodgeEnergy_eq_winding_sq n hn x.as g)

/-- Basepoint-specialized canonical bridge theorem. -/
def cycleBaseObj (n : ℕ) (hn : n ≥ 3) : SimplicialGroupoid (CycleGraph n hn) where
  as := cycleBase n hn

/-- Basepoint-specialized canonical cycle partition identity with no extra hypotheses. -/
theorem cycleGroupoid_partitionFn_eq_base_canonical_energy (n : ℕ) (hn : n ≥ 3) :
    groupoidPartitionFn (cycleBaseObj n hn)
      (cycleCanonicalEnergy n hn (cycleBaseObj n hn))
      (summable_cycleCanonicalEnergy n hn (cycleBaseObj n hn)) = partitionFn n hn := by
  simpa [cycleBaseObj] using
    (cycleGroupoid_partitionFn_eq_canonical_energy n hn (cycleBaseObj n hn))

/-! ## Groupoid objects

The bundled domain of groupoid complexity: a groupoid with a chosen
base object and a summable energy on its endomorphisms. The product
law (`GroupoidObj.prod_complexity`) and the energy-preserving
equivalence (`GroupoidObj.Equiv`) are consumed by the duality
wrappers in `Meno/Duality.lean`. -/

section Bridge

/-- A groupoid object with energy function: the domain of groupoid complexity. -/
structure GroupoidObj where
  {G : Type u}
  [grpd : Groupoid G]
  base : G
  energy : @End G grpd.toCategoryStruct base → ℝ
  summable : Summable (fun g => Real.exp (-energy g))

attribute [instance] GroupoidObj.grpd

/-- **Bridge to the spine**: every groupoid object satisfying the two
ground conditions (zero identity energy, non-negative energy) is a loop
kernel. All five data fields transfer verbatim — the bridge is pure
repackaging (plan falsification clause #4: near-`rfl`). -/
noncomputable def GroupoidObj.toLoopKernelObj (E : GroupoidObj)
    (h_id : E.energy (𝟙 E.base) = 0)
    (h_nonneg : ∀ g, 0 ≤ E.energy g) : Meno.LoopKernelObj where
  C := E.G
  base := E.base
  energy := E.energy
  energy_id := h_id
  energy_nonneg := h_nonneg
  summable := E.summable

noncomputable def GroupoidObj.complexity (E : GroupoidObj) : ℝ :=
  groupoidComplexity (C := E.G) E.base E.energy E.summable

noncomputable def GroupoidObj.partFn (E : GroupoidObj) : ℝ :=
  groupoidPartitionFn (C := E.G) E.base E.energy E.summable

/-- The bridge preserves partition functions definitionally: both sides
are `∑' g : End base, exp (-energy g)`. -/
theorem GroupoidObj.toLoopKernelObj_partFn (E : GroupoidObj)
    (h_id : E.energy (𝟙 E.base) = 0) (h_nonneg : ∀ g, 0 ≤ E.energy g) :
    (E.toLoopKernelObj h_id h_nonneg).partFn = E.partFn := rfl

open scoped BigOperators


/-- Equivalence of groupoid objects: endomorphism equivalence preserving energy. -/
def GroupoidObj.Equiv (E₁ E₂ : GroupoidObj) : Prop :=
  ∃ (e : End E₁.base ≃* End E₂.base), ∀ g, E₂.energy (e g) = E₁.energy g

set_option maxHeartbeats 400000 in
private lemma prod_summable (E₁ E₂ : GroupoidObj) :
    Summable (fun g : End E₁.base × End E₂.base =>
      Real.exp (-(E₁.energy g.1 + E₂.energy g.2))) := by
  rw [show (fun g : End E₁.base × End E₂.base =>
      Real.exp (-(E₁.energy g.1 + E₂.energy g.2))) =
      fun g => Real.exp (-E₁.energy g.1) * Real.exp (-E₂.energy g.2) from
    funext fun g => by rw [neg_add, Real.exp_add]]
  exact Summable.mul_of_nonneg E₁.summable E₂.summable
    (fun _ => le_of_lt (Real.exp_pos _)) (fun _ => le_of_lt (Real.exp_pos _))

/-- Product of groupoid objects with independent energies. -/
noncomputable def GroupoidObj.prod (E₁ E₂ : GroupoidObj) : GroupoidObj where
  G := E₁.G × E₂.G
  base := (E₁.base, E₂.base)
  energy g := E₁.energy (Prod.fst g) + E₂.energy (Prod.snd g)
  summable := prod_summable E₁ E₂

set_option maxHeartbeats 400000 in
private theorem groupoidObj_prod_partFn (E₁ E₂ : GroupoidObj) :
    (E₁.prod E₂).partFn = E₁.partFn * E₂.partFn := by
  unfold GroupoidObj.partFn groupoidPartitionFn GroupoidObj.prod
  simp only []
  rw [show (fun g : End (E₁.base, E₂.base) =>
      Real.exp (-(E₁.energy (Prod.fst g) + E₂.energy (Prod.snd g)))) =
      fun g => Real.exp (-E₁.energy (Prod.fst g)) * Real.exp (-E₂.energy (Prod.snd g)) from
    funext fun g => by rw [neg_add, Real.exp_add]]
  exact (E₁.summable.tsum_mul_tsum E₂.summable
    (Summable.mul_of_nonneg E₁.summable E₂.summable
      (fun _ => le_of_lt (Real.exp_pos _)) (fun _ => le_of_lt (Real.exp_pos _)))).symm

theorem GroupoidObj.prod_complexity (E₁ E₂ : GroupoidObj) :
    (E₁.prod E₂).complexity = E₁.complexity + E₂.complexity := by
  unfold GroupoidObj.complexity groupoidComplexity
  have := groupoidObj_prod_partFn E₁ E₂
  unfold GroupoidObj.partFn at this
  rw [this]
  exact Real.log_mul (ne_of_gt (groupoidPartitionFn_pos _ _ _))
                     (ne_of_gt (groupoidPartitionFn_pos _ _ _))


end Bridge

/-! ## The Cycle Groupoid Through the Spine

The canonical cycle groupoid object factors through the analytic spine:

    cycleCanonicalObj ──toLoopKernelObj──▶ cycleLoopKernel
      ──cycleSectorPresentation──▶ QuadraticAction with Q = !![1/n]
      ──partFn_eq_of_Q_eq──▶ scalarPartFn (1/n)
      ──scalarPartFn_one_div_n_eq_partitionFn──▶ partitionFn n hn

and its T-duality is a corollary of the spine flagship
`Meno.partitionFn_T_duality_via_spine` — no reference to
`quadraticPartFn_duality` or the `GroupoidObj.dual` machinery.

The Gram form of the presentation is **the same** `!![1/n]` as
`Meno.cycleHarmonicGramData`: its symmetry and positive-definiteness
proofs are reused, not re-proved. Two origins (winding classes of the
fundamental groupoid; Hodge harmonic Gram data) feed one analytic
object. -/

section CycleSpine

/-- Canonical cycle groupoid object at the basepoint: energy and
summability are both derived from the proved winding equivalence.
(Relocated upstream from `Duality.lean`.) -/
noncomputable def cycleCanonicalObj (n : ℕ) (hn : n ≥ 3) : GroupoidObj where
  G := SimplicialGroupoid (CycleGraph n hn)
  base := cycleBaseObj n hn
  energy := cycleCanonicalEnergy n hn (cycleBaseObj n hn)
  summable := summable_cycleCanonicalEnergy n hn (cycleBaseObj n hn)

/-- Canonical cycle object partition function recovers `partitionFn`
with no extra hypotheses. (Relocated upstream from `Duality.lean`.) -/
theorem cycleCanonicalObj_partFn_eq_partitionFn (n : ℕ) (hn : n ≥ 3) :
    (cycleCanonicalObj n hn).partFn = partitionFn n hn := by
  simpa [cycleCanonicalObj, GroupoidObj.partFn] using
    cycleGroupoid_partitionFn_eq_base_canonical_energy n hn

/-- The canonical cycle loop kernel: the cycle groupoid object pushed
through the spine bridge. Ground conditions are the proved
identity/non-negativity lemmas for the canonical Hodge energy. -/
noncomputable def cycleLoopKernel (n : ℕ) (hn : n ≥ 3) : Meno.LoopKernelObj :=
  (cycleCanonicalObj n hn).toLoopKernelObj
    (cycleCanonicalEnergy_id n hn (cycleBaseObj n hn))
    (cycleCanonicalEnergy_nonneg n hn (cycleBaseObj n hn))

/-- Sector presentation of the cycle loop kernel: winding coordinates
identify `End (cycleBaseObj)` with the rank-1 lattice `Fin 1 → ℤ`, and
the canonical Hodge energy is the quadratic form of the harmonic Gram
matrix `!![1/n]`. Structural compatibility (`coord_one`, `coord_comp`)
is winding additivity under loop composition. -/
noncomputable def cycleSectorPresentation (n : ℕ) (hn : n ≥ 3) :
    Meno.SectorPresentation (cycleLoopKernel n hn) 1 where
  coord := (cycleLoopClassEquivInt n hn (cycleBase n hn)).trans
    (Equiv.funUnique (Fin 1) ℤ).symm
  coord_one := by
    funext i
    show cycleCanonicalWinding n hn (cycleBaseObj n hn) (𝟙 (cycleBaseObj n hn)) = 0
    exact cycleCanonicalWinding_id n hn (cycleBaseObj n hn)
  coord_comp := by
    intro g h
    funext i
    show cycleCanonicalWinding n hn (cycleBaseObj n hn) (g ≫ h)
      = cycleCanonicalWinding n hn (cycleBaseObj n hn) g
        + cycleCanonicalWinding n hn (cycleBaseObj n hn) h
    exact cycleCanonicalWinding_comp n hn (cycleBaseObj n hn) g h
  Q := !![1 / (n : ℝ)]
  Q_posDef := (Meno.cycleHarmonicGramData n hn).gram_posDef
  energy_eq := by
    intro g
    show cycleCanonicalEnergy n hn (cycleBaseObj n hn) g = _
    rw [cycleCanonicalEnergy_eq_winding_sq n hn (cycleBaseObj n hn) g]
    show (cycleCanonicalWinding n hn (cycleBaseObj n hn) g : ℝ) ^ 2 / n
      = ∑ i : Fin 1, ∑ j : Fin 1, !![1 / (n : ℝ)] i j
          * ((cycleCanonicalWinding n hn (cycleBaseObj n hn) g : ℤ) : ℝ)
          * ((cycleCanonicalWinding n hn (cycleBaseObj n hn) g : ℤ) : ℝ)
    simp [Matrix.cons_val_fin_one]
    ring

/-- **Groupoid partition function through the spine.** The cycle loop
kernel's partition function transits the presentation to the quadratic
action with Gram `!![1/n]`, to `scalarPartFn (1/n)`, to
`partitionFn n hn` — every step a spine theorem. -/
theorem cycleLoopKernel_partFn_eq_partitionFn (n : ℕ) (hn : n ≥ 3) :
    (cycleLoopKernel n hn).partFn = partitionFn n hn := by
  rw [(cycleSectorPresentation n hn).partFn_eq]
  have hα : (0 : ℝ) < 1 / n := one_div_pos.mpr
    (by exact_mod_cast (show 0 < n by omega))
  rw [Meno.QuadraticAction.partFn_eq_of_Q_eq
        (cycleSectorPresentation n hn).toQuadraticAction
        (Meno.QuadraticAction.ofScalar (1 / n) hα) rfl,
      Meno.QuadraticAction.ofScalar_partFn_eq,
      Meno.scalarPartFn_one_div_n_eq_partitionFn n hn]

/-- **Two origins, one analytic object**: the groupoid presentation and
the Hodge harmonic Gram data produce quadratic actions with the same
Gram matrix, hence the same partition function. -/
theorem cycleSectorPresentation_partFn_eq_gramData (n : ℕ) (hn : n ≥ 3) :
    (cycleSectorPresentation n hn).toQuadraticAction.toSectorAction.partFn
    = (Meno.cycleHarmonicGramData n hn).toQuadraticAction.toSectorAction.partFn :=
  Meno.QuadraticAction.partFn_eq_of_Q_eq _ _ rfl

/-- **Cycle groupoid T-duality, rederived through the spine.** The
canonical cycle groupoid object's partition function obeys T-duality as
a corollary of `Meno.partitionFn_T_duality_via_spine`. This supersedes
the route through `GroupoidObj.dual` / `quadraticPartFn_duality` for the
canonical cycle: no winding hypothesis, no dual-object construction —
the spine carries the duality. -/
theorem cycleCanonicalObj_T_duality (n : ℕ) (hn : n ≥ 3) :
    (↑(Meno.QuadraticAction.scalarPartFn (Real.pi ^ 2 * n)) : ℂ) =
    ↑((1 / (n : ℝ)) / Real.pi) ^ ((1 : ℂ) / 2)
      * ↑((cycleCanonicalObj n hn).partFn) := by
  rw [cycleCanonicalObj_partFn_eq_partitionFn]
  exact Meno.partitionFn_T_duality_via_spine n hn

/-- **The categorical dual of the cycle loop kernel** (Phase 6's
`dualVia`, instantiated): the dual object built by transporting
`π²·Q⁻¹` through the winding coordinates has partition function
`√((1/n)/π) · Z(C_n)`. The concrete witness that
`SectorPresentation.dualVia_partFn_duality` has a consumer. -/
theorem cycleLoopKernel_dualVia_partFn (n : ℕ) (hn : n ≥ 3) :
    (((Meno.LoopKernelObj.dualVia (cycleSectorPresentation n hn)).partFn : ℝ) : ℂ)
      = ↑((1 / (n : ℝ)) / Real.pi : ℝ) ^ ((1 : ℂ) / 2)
        * ↑(partitionFn n hn) := by
  rw [Meno.SectorPresentation.dualVia_partFn_duality,
    cycleLoopKernel_partFn_eq_partitionFn]
  congr 3
  rw [show (cycleSectorPresentation n hn).Q = !![1 / (n : ℝ)] from rfl,
    Matrix.det_fin_one, pow_one]
  simp

end CycleSpine

/-! ## The Geodesic Instance (Goal 4)

Minimal walk length within a homotopy class, as a Lawvere-subadditive
length on the fundamental groupoid. The combinatorial mass `n` of the
cycle is exhibited at the `Geodesic` layer with no analytic content —
and meets the harmonic mass `1/n` in the duality `n · (1/n) = 1`. -/

section GeodesicInstance

open Meno

/-- Geodesic length of a homotopy class: minimal walk length among
representatives — well-defined by homotopy invariance. -/
noncomputable def homotopyClassLength (C : Complex V) {u v : V} :
    HomotopyClass₂ C u v → ℝ :=
  Quot.lift (fun p => (geodesicLength C p : ℝ))
    (fun _ _ h => congrArg (fun m : ℕ => (m : ℝ))
      (geodesicLength_eq_of_homotopic C h))

/-- **The simplicial walk-length `Geodesic` structure** (Goal 4): the
fundamental groupoid of a symmetric complex carries the
minimal-representative walk length; subadditivity holds because the
append of minimal representatives represents the composite class. -/
noncomputable def simplicialGeodesic (C : Complex V)
    (hsym : C.toGraph.Symmetric) :
    letI := simplicialGroupoid C hsym
    Geodesic (SimplicialGroupoid C) :=
  letI := simplicialGroupoid C hsym
  { length := fun {x y} f => homotopyClassLength C f
    length_nonneg := fun {x y} f => by
      induction f using Quot.ind with | mk p =>
      show (0 : ℝ) ≤ (geodesicLength C p : ℝ)
      positivity
    length_id := fun x => by
      show ((geodesicLength C (Walk.nil x.as) : ℕ) : ℝ) = 0
      norm_cast
      have h := geodesicLength_le_length C (Walk.nil x.as)
      have h0 : (Walk.nil x.as : Walk C.toGraph x.as x.as).length = 0 := rfl
      omega
    length_comp_le := fun {x y z} f g => by
      induction f using Quot.ind with | mk p =>
      induction g using Quot.ind with | mk q =>
      show ((geodesicLength C (p.append q) : ℕ) : ℝ)
        ≤ (geodesicLength C p : ℝ) + (geodesicLength C q : ℝ)
      obtain ⟨p', hp', hplen⟩ := geodesicLength_achieved C p
      obtain ⟨q', hq', hqlen⟩ := geodesicLength_achieved C q
      have h1 : geodesicLength C (p.append q)
          = geodesicLength C (p'.append q') :=
        geodesicLength_eq_of_homotopic C (Homotopic₂.congr_append C hp' hq')
      have h2 : geodesicLength C (p'.append q') ≤ (p'.append q').length :=
        geodesicLength_le_length C _
      rw [Walk.length_append] at h2
      have h3 : geodesicLength C (p.append q)
          ≤ geodesicLength C p + geodesicLength C q := by omega
      exact_mod_cast h3 }

/-- The cycle graph's canonical `Geodesic` instance. -/
noncomputable instance cycleGeodesic (n : ℕ) (hn : n ≥ 3) :
    Geodesic (SimplicialGroupoid (CycleGraph n hn)) :=
  simplicialGeodesic (CycleGraph n hn) (cycleGraph_symmetric n hn)

/-- The canonical winding-1 loop, as a groupoid endomorphism. -/
noncomputable def canonicalLoop (n : ℕ) (hn : n ≥ 3) :
    End (⟨cycleBase n hn⟩ : SimplicialGroupoid (CycleGraph n hn)) :=
  Quot.mk _ (cycleWalk n hn)

/-- **Goal 4's acceptance**: the geodesic length of the canonical
cycle is the combinatorial mass `n`, at the `Geodesic` layer, with no
analytic content involved. -/
theorem cycleGeodesic_canonical (n : ℕ) (hn : n ≥ 3) :
    Geodesic.length (canonicalLoop n hn) = n := by
  show ((geodesicLength (CycleGraph n hn) (cycleWalk n hn) : ℕ) : ℝ) = n
  rw [cycleGraph_geodesic_eq_n]

/-- **The geodesic/harmonic duality**: combinatorial mass times
harmonic mass is one — `n · (1/n) = 1`. The winding-1 sector's two
independent invariants, meeting. -/
theorem geodesic_harmonic_duality (n : ℕ) (hn : n ≥ 3) :
    Geodesic.length (canonicalLoop n hn)
      * (Meno.cyclePeriodData n (by omega)).energy ![1] = 1 := by
  rw [cycleGeodesic_canonical]
  have henergy : (Meno.cyclePeriodData n (by omega)).energy ![1] = 1 / n := by
    show ∑ i, ∑ j, (Meno.cyclePeriodData n (by omega)).gram i j
        * ((![1] : Fin 1 → ℤ) i : ℝ) * ((![1] : Fin 1 → ℤ) j : ℝ) = 1 / n
    rw [Meno.cyclePeriodData_gram]
    simp
  rw [henergy]
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  field_simp

end GeodesicInstance

end Simplicial
