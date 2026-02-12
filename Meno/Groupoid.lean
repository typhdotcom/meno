import Meno.Simplicial
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
over automorphisms defines complexity C(G) = log Z, satisfying the hierarchy axioms. -/

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

/-! ## Hierarchy Axioms

These mirror `SGD.ComplexityMeasure` (Basic.lean) for the groupoid setting:

| Basic.lean axiom | Groupoid analogue | Status |
| :--- | :--- | :--- |
| `unique_zero` | `groupoidComplexity_trivial` | Done |
| `congr` | `groupoidComplexity_congr` | Done |
| `prod_eq` | `groupoidComplexity_prod` | Done |
| `sigma_le` | — | Requires fibered groupoids |

The domain shifts from bare types (`Type u → M`) to groupoid objects with energy
functions (`End x → ℝ`). This captures topology that Axiom K hides from the
type-level measure. -/

/-- **unique_zero**: Trivial groupoid (single automorphism) with K(id) = 0 has C = 0. -/
theorem groupoidComplexity_trivial
    {C : Type*} [Groupoid C] (x : C)
    (K : End x → ℝ)
    (hsum : Summable (fun g => Real.exp (-K g)))
    [Unique (End x)]
    (hK : K default = 0) :
    groupoidComplexity x K hsum = 0 := by
  unfold groupoidComplexity groupoidPartitionFn
  have : ∑' g : End x, Real.exp (-K g) = 1 := by
    rw [(hasSum_unique _).tsum_eq]
    have : (Unique.instInhabited (α := End x)).default = default := Subsingleton.elim _ _
    rw [this, hK, neg_zero, Real.exp_zero]
  rw [this, Real.log_one]

/-- **congr**: Equivalent endomorphism groups with matching energies
    have equal partition functions. -/
theorem groupoidPartitionFn_congr
    {C D : Type*} [Groupoid C] [Groupoid D]
    (x : C) (y : D)
    (K_C : End x → ℝ) (K_D : End y → ℝ)
    (e : End x ≃ End y)
    (hK : ∀ g, K_D (e g) = K_C g)
    (hsum_C : Summable (fun g => Real.exp (-K_C g)))
    (hsum_D : Summable (fun g => Real.exp (-K_D g))) :
    groupoidPartitionFn x K_C hsum_C = groupoidPartitionFn y K_D hsum_D := by
  unfold groupoidPartitionFn
  conv_lhs =>
    rw [show (fun g => Real.exp (-K_C g)) = (fun g => Real.exp (-K_D (e g))) from by
      ext g; rw [hK]]
  exact e.tsum_eq (fun h => Real.exp (-K_D h))

/-- **congr**: Equivalent endomorphism groups with matching energies
    have equal complexity. -/
theorem groupoidComplexity_congr
    {C D : Type*} [Groupoid C] [Groupoid D]
    (x : C) (y : D)
    (K_C : End x → ℝ) (K_D : End y → ℝ)
    (e : End x ≃ End y)
    (hK : ∀ g, K_D (e g) = K_C g)
    (hsum_C : Summable (fun g => Real.exp (-K_C g)))
    (hsum_D : Summable (fun g => Real.exp (-K_D g))) :
    groupoidComplexity x K_C hsum_C = groupoidComplexity y K_D hsum_D := by
  unfold groupoidComplexity
  rw [groupoidPartitionFn_congr x y K_C K_D e hK hsum_C hsum_D]

/-- **prod_eq**: When the partition function factors, complexity is additive. -/
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

/-! ## Bridge to Abstract Hierarchy

Groupoid complexity instantiates `SGD.AdditiveComplexityOn` from Basic.lean,
the domain-generic additive complexity class. The algebraic gravity theorem
and unit laws from Basic.lean apply to groupoid objects via this instance. -/

section Bridge

/-- A groupoid object with energy function: the domain of groupoid complexity. -/
structure GroupoidObj where
  {G : Type u}
  [grpd : Groupoid G]
  base : G
  energy : @End G grpd.toCategoryStruct base → ℝ
  summable : Summable (fun g => Real.exp (-energy g))

attribute [instance] GroupoidObj.grpd

noncomputable def GroupoidObj.complexity (E : GroupoidObj) : ℝ :=
  groupoidComplexity (C := E.G) E.base E.energy E.summable

noncomputable def GroupoidObj.partFn (E : GroupoidObj) : ℝ :=
  groupoidPartitionFn (C := E.G) E.base E.energy E.summable

/-- The trivial groupoid object: one object, one morphism, zero energy. -/
noncomputable def GroupoidObj.trivial : GroupoidObj where
  G := SingleObj PUnit
  base := SingleObj.star PUnit
  energy := fun _ => 0
  summable := by
    have : (fun g : End (SingleObj.star PUnit) => Real.exp (-0 : ℝ)) = fun _ => 1 := by
      ext; simp
    rw [this]
    haveI : Fintype PUnit := inferInstance
    exact (hasSum_fintype (fun _ : PUnit => (1 : ℝ))).summable

private noncomputable instance trivialEndUnique :
    Unique (End (SingleObj.star PUnit)) := by
  change Unique PUnit; exact inferInstance

theorem GroupoidObj.trivial_complexity : GroupoidObj.trivial.complexity = 0 := by
  have : trivial.base = SingleObj.star PUnit := rfl
  haveI : Unique (End trivial.base) := by
    rw [this]; exact trivialEndUnique
  exact groupoidComplexity_trivial _ _ _ rfl

/-- Equivalence of groupoid objects: endomorphism equivalence preserving energy. -/
def GroupoidObj.Equiv (E₁ E₂ : GroupoidObj) : Prop :=
  ∃ (e : End E₁.base ≃ End E₂.base), ∀ g, E₂.energy (e g) = E₁.energy g

theorem GroupoidObj.congr_complexity {E₁ E₂ : GroupoidObj}
    (h : GroupoidObj.Equiv E₁ E₂) :
    E₁.complexity = E₂.complexity := by
  obtain ⟨e, hK⟩ := h
  exact groupoidComplexity_congr _ _ _ _ e hK _ _

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

/-- Groupoid complexity is an instance of the domain-generic additive complexity
    class from Basic.lean. The algebraic gravity theorem and unit laws
    from `AdditiveComplexityOn` apply to groupoid objects through this instance. -/
noncomputable instance : SGD.AdditiveComplexityOn GroupoidObj ℝ where
  C := GroupoidObj.complexity
  unit := GroupoidObj.trivial
  equiv := GroupoidObj.Equiv
  prod := GroupoidObj.prod
  unit_zero := GroupoidObj.trivial_complexity
  congr := GroupoidObj.congr_complexity
  prod_add := GroupoidObj.prod_complexity

end Bridge

end Simplicial
