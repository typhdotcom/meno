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

/-! ## Hierarchy Axioms

These mirror `SGD.ComplexityMeasure` (Basic.lean) for the groupoid setting:

| Basic.lean axiom | Groupoid analogue | Status |
| :--- | :--- | :--- |
| `unique_zero` | `groupoidComplexity_trivial` | Done |
| `congr` | `groupoidComplexity_congr` | Done |
| `prod_eq` | `groupoidComplexity_prod` | Done |
| `sigma_le` | `GroupoidObj.sigmaComplexity_le_logCard_max` | Finite-index analogue (log-sum-exp bound) |

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

open scoped BigOperators

/-- Finite-family sigma partition function on groupoid objects:
    sum of partition functions over an index type. -/
noncomputable def GroupoidObj.sigmaPartFn (D : Type*) [Fintype D]
    (P : D → GroupoidObj) : ℝ :=
  ∑ d : D, (P d).partFn

/-- Finite-family sigma complexity: log of `sigmaPartFn`. -/
noncomputable def GroupoidObj.sigmaComplexity (D : Type*) [Fintype D]
    (P : D → GroupoidObj) : ℝ :=
  Real.log (GroupoidObj.sigmaPartFn D P)

private theorem GroupoidObj.partFn_eq_exp_complexity (E : GroupoidObj) :
    E.partFn = Real.exp E.complexity := by
  unfold GroupoidObj.partFn GroupoidObj.complexity groupoidComplexity
  exact (Real.exp_log (groupoidPartitionFn_pos (x := E.base) (K := E.energy)
    (hsum := E.summable))).symm

theorem GroupoidObj.sigmaPartFn_pos (D : Type*) [Fintype D] [Nonempty D]
    (P : D → GroupoidObj) :
    0 < GroupoidObj.sigmaPartFn D P := by
  classical
  obtain ⟨d₀⟩ := ‹Nonempty D›
  have hd₀ : 0 < (P d₀).partFn := by
    unfold GroupoidObj.partFn
    exact groupoidPartitionFn_pos (x := (P d₀).base) (K := (P d₀).energy)
      (hsum := (P d₀).summable)
  have hle : (P d₀).partFn ≤ GroupoidObj.sigmaPartFn D P := by
    unfold GroupoidObj.sigmaPartFn
    simpa using (Finset.single_le_sum
      (f := fun d : D => (P d).partFn)
      (s := Finset.univ)
      (fun d hd => by
        exact le_of_lt (groupoidPartitionFn_pos (x := (P d).base) (K := (P d).energy)
          (hsum := (P d).summable)))
      (Finset.mem_univ d₀))
  exact lt_of_lt_of_le hd₀ hle

/-- Finite-family sigma bound for groupoid complexity:
    `log (∑ partFn) ≤ log |D| + max_d complexity(d)`.
    This is the groupoid analogue of sigma-subadditivity at finite index sets. -/
theorem GroupoidObj.sigmaComplexity_le_logCard_max (D : Type*) [Fintype D] [Nonempty D]
    (P : D → GroupoidObj) :
    GroupoidObj.sigmaComplexity D P ≤
      Real.log (Fintype.card D) +
        Finset.univ.sup' Finset.univ_nonempty (fun d : D => (P d).complexity) := by
  classical
  let hne : (Finset.univ : Finset D).Nonempty := Finset.univ_nonempty
  set M : ℝ := Finset.univ.sup' hne (fun d : D => (P d).complexity)
  have hsum_le :
      GroupoidObj.sigmaPartFn D P ≤ (Fintype.card D : ℝ) * Real.exp M := by
    unfold GroupoidObj.sigmaPartFn
    calc
      ∑ d : D, (P d).partFn ≤ ∑ d : D, Real.exp M := by
        refine Finset.sum_le_sum ?_
        intro d hd
        calc
          (P d).partFn = Real.exp ((P d).complexity) := GroupoidObj.partFn_eq_exp_complexity (P d)
          _ ≤ Real.exp M := by
            exact Real.exp_le_exp.mpr (by
              have : (P d).complexity ≤ M := by
                show (P d).complexity ≤ Finset.univ.sup' hne (fun d : D => (P d).complexity)
                exact Finset.le_sup' (f := fun d : D => (P d).complexity) (Finset.mem_univ d)
              simpa [M] using this)
      _ = (Fintype.card D : ℝ) * Real.exp M := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hpos : 0 < GroupoidObj.sigmaPartFn D P := GroupoidObj.sigmaPartFn_pos D P
  have hcard_pos : 0 < (Fintype.card D : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty D›
  have hlog_le :
      Real.log (GroupoidObj.sigmaPartFn D P) ≤
      Real.log ((Fintype.card D : ℝ) * Real.exp M) :=
    Real.log_le_log hpos hsum_le
  calc
    GroupoidObj.sigmaComplexity D P = Real.log (GroupoidObj.sigmaPartFn D P) := rfl
    _ ≤ Real.log ((Fintype.card D : ℝ) * Real.exp M) := hlog_le
    _ = Real.log (Fintype.card D) + M := by
      rw [Real.log_mul (ne_of_gt hcard_pos) (ne_of_gt (Real.exp_pos M)), Real.log_exp]
    _ = Real.log (Fintype.card D) +
        Finset.univ.sup' Finset.univ_nonempty (fun d : D => (P d).complexity) := by
      simp [M]

/-- Reindexing invariance for sigma complexity under a finite index equivalence. -/
theorem GroupoidObj.sigmaComplexity_equiv
    (I J : Type*) [Fintype I] [Fintype J]
    (e : I ≃ J) (P : I → GroupoidObj) :
    GroupoidObj.sigmaComplexity I P =
      GroupoidObj.sigmaComplexity J (fun j => P (e.symm j)) := by
  unfold GroupoidObj.sigmaComplexity GroupoidObj.sigmaPartFn
  congr 1
  exact Fintype.sum_equiv e
    (fun i => (P i).partFn)
    (fun j => (P (e.symm j)).partFn)
    (fun i => by simp)

/-- Dependent finite-index sigma bound:
    `C(Σ d, P d) ≤ log|D| + max_d C(P d)` for `sigmaComplexity`. -/
theorem GroupoidObj.sigmaComplexity_sigma_le_logCard_max
    (D : Type*) [Fintype D] [Nonempty D]
    (P : D → Type*) [∀ d, Fintype (P d)] [∀ d, Nonempty (P d)]
    (E : (Sigma P) → GroupoidObj) :
    GroupoidObj.sigmaComplexity (Sigma P) E ≤
      Real.log (Fintype.card D) +
        Finset.univ.sup' Finset.univ_nonempty
          (fun d : D => GroupoidObj.sigmaComplexity (P d) (fun p => E ⟨d, p⟩)) := by
  classical
  let S : D → ℝ := fun d => GroupoidObj.sigmaPartFn (P d) (fun p => E ⟨d, p⟩)
  have hS_pos : ∀ d : D, 0 < S d := by
    intro d
    exact GroupoidObj.sigmaPartFn_pos (D := P d) (P := fun p => E ⟨d, p⟩)
  have hsigmaPart :
      GroupoidObj.sigmaPartFn (Sigma P) E = ∑ d : D, S d := by
    unfold GroupoidObj.sigmaPartFn S
    simpa using (Fintype.sum_sigma' (f := fun d p => (E ⟨d, p⟩).partFn))
  set M : ℝ := Finset.univ.sup' Finset.univ_nonempty
    (fun d : D => GroupoidObj.sigmaComplexity (P d) (fun p => E ⟨d, p⟩))
  have hsum_le : ∑ d : D, S d ≤ (Fintype.card D : ℝ) * Real.exp M := by
    calc
      ∑ d : D, S d ≤ ∑ d : D, Real.exp M := by
        refine Finset.sum_le_sum ?_
        intro d hd
        have hSd :
            S d = Real.exp (GroupoidObj.sigmaComplexity (P d) (fun p => E ⟨d, p⟩)) := by
          unfold S GroupoidObj.sigmaComplexity
          exact (Real.exp_log (hS_pos d)).symm
        rw [hSd]
        exact Real.exp_le_exp.mpr
          (Finset.le_sup' (s := Finset.univ)
            (f := fun d : D => GroupoidObj.sigmaComplexity (P d) (fun p => E ⟨d, p⟩))
            (Finset.mem_univ d))
      _ = (Fintype.card D : ℝ) * Real.exp M := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hsum_pos : 0 < ∑ d : D, S d := by
    obtain ⟨d₀⟩ := ‹Nonempty D›
    have hle : S d₀ ≤ ∑ d : D, S d := by
      simpa using (Finset.single_le_sum
        (f := S)
        (s := (Finset.univ : Finset D))
        (fun d hd => le_of_lt (hS_pos d))
        (Finset.mem_univ d₀))
    exact lt_of_lt_of_le (hS_pos d₀) hle
  have hcard_pos : 0 < (Fintype.card D : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty D›
  have hlog_le :
      Real.log (∑ d : D, S d) ≤ Real.log ((Fintype.card D : ℝ) * Real.exp M) :=
    Real.log_le_log hsum_pos hsum_le
  calc
    GroupoidObj.sigmaComplexity (Sigma P) E = Real.log (GroupoidObj.sigmaPartFn (Sigma P) E) := rfl
    _ = Real.log (∑ d : D, S d) := by rw [hsigmaPart]
    _ ≤ Real.log ((Fintype.card D : ℝ) * Real.exp M) := hlog_le
    _ = Real.log (Fintype.card D) + M := by
      rw [Real.log_mul (ne_of_gt hcard_pos) (ne_of_gt (Real.exp_pos M)), Real.log_exp]
    _ = Real.log (Fintype.card D) +
        Finset.univ.sup' Finset.univ_nonempty
          (fun d : D => GroupoidObj.sigmaComplexity (P d) (fun p => E ⟨d, p⟩)) := by
      simp [M]

noncomputable instance instPullbackFintype
    {A B D : Type u} (f : A → D) (g : B → D)
    [Fintype A] [Fintype B] :
    Fintype (SGD.Pullback f g) :=
  Fintype.ofInjective
    (fun p : SGD.Pullback f g => p.val)
    (fun _ _ h => Subtype.ext h)

noncomputable instance instFiberFintype
    {A D : Type u} (f : A → D) (d : D)
    [Fintype A] :
    Fintype (SGD.Fiber f d) :=
  Fintype.ofInjective
    (fun a : SGD.Fiber f d => a.val)
    (fun _ _ h => Subtype.ext h)

noncomputable instance instFiberProdFintype
    {A B D : Type u} (f : A → D) (g : B → D) (d : D)
    [Fintype A] [Fintype B] :
    Fintype (SGD.FiberProd f g d) :=
  inferInstance

/-- Pullback-index specialization of the dependent finite sigma bound. -/
theorem GroupoidObj.sigmaComplexity_pullback_le_logCard_maxFiber
    {A B D : Type u} [Fintype A] [Fintype B] [Fintype D] [Nonempty D]
    (f : A → D) (g : B → D)
    [∀ d, Nonempty (SGD.FiberProd f g d)]
    (E : SGD.Pullback f g → GroupoidObj) :
    GroupoidObj.sigmaComplexity (SGD.Pullback f g) E ≤
      Real.log (Fintype.card D) +
        Finset.univ.sup' Finset.univ_nonempty
          (fun d : D =>
            GroupoidObj.sigmaComplexity (SGD.FiberProd f g d)
              (fun p => E ((SGD.Pullback.equivSigmaFiber f g).symm ⟨d, p⟩))) := by
  calc
    GroupoidObj.sigmaComplexity (SGD.Pullback f g) E
        = GroupoidObj.sigmaComplexity (Sigma (SGD.FiberProd f g))
            (fun s => E ((SGD.Pullback.equivSigmaFiber f g).symm s)) := by
          simpa using
            (GroupoidObj.sigmaComplexity_equiv
              (I := SGD.Pullback f g)
              (J := Sigma (SGD.FiberProd f g))
              (e := SGD.Pullback.equivSigmaFiber f g)
              (P := E))
    _ ≤ Real.log (Fintype.card D) +
          Finset.univ.sup' Finset.univ_nonempty
            (fun d : D =>
              GroupoidObj.sigmaComplexity (SGD.FiberProd f g d)
                (fun p => E ((SGD.Pullback.equivSigmaFiber f g).symm ⟨d, p⟩))) := by
          exact GroupoidObj.sigmaComplexity_sigma_le_logCard_max
            (D := D) (P := SGD.FiberProd f g)
            (E := fun s => E ((SGD.Pullback.equivSigmaFiber f g).symm s))

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
  ∃ (e : End E₁.base ≃* End E₂.base), ∀ g, E₂.energy (e g) = E₁.energy g

theorem GroupoidObj.congr_complexity {E₁ E₂ : GroupoidObj}
    (h : GroupoidObj.Equiv E₁ E₂) :
    E₁.complexity = E₂.complexity := by
  obtain ⟨e, hK⟩ := h
  exact groupoidComplexity_congr _ _ _ _ e.toEquiv hK _ _

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

/-- Fiberwise product-family sigma bound: finite-index analogue of the sharp
    refactoring pattern `base + sup_d pairedFiber(d)`. -/
theorem GroupoidObj.sigmaComplexity_prod_family_le_logCard_max_pair
    (D : Type*) [Fintype D] [Nonempty D]
    (P Q : D → GroupoidObj) :
    GroupoidObj.sigmaComplexity D (fun d => (P d).prod (Q d)) ≤
      Real.log (Fintype.card D) +
        Finset.univ.sup' Finset.univ_nonempty
          (fun d : D => (P d).complexity + (Q d).complexity) := by
  simpa [GroupoidObj.prod_complexity] using
    (GroupoidObj.sigmaComplexity_le_logCard_max (D := D)
      (P := fun d => (P d).prod (Q d)))

/-- Coarse product-family sigma bound: decouples paired fiber maxima into
    `max_d C(P d) + max_d C(Q d)`. -/
theorem GroupoidObj.sigmaComplexity_prod_family_le_logCard_max_split
    (D : Type*) [Fintype D] [Nonempty D]
    (P Q : D → GroupoidObj) :
    GroupoidObj.sigmaComplexity D (fun d => (P d).prod (Q d)) ≤
      Real.log (Fintype.card D) +
        Finset.univ.sup' Finset.univ_nonempty (fun d : D => (P d).complexity) +
        Finset.univ.sup' Finset.univ_nonempty (fun d : D => (Q d).complexity) := by
  let hne : (Finset.univ : Finset D).Nonempty := Finset.univ_nonempty
  have hpair := GroupoidObj.sigmaComplexity_prod_family_le_logCard_max_pair
    (D := D) P Q
  have hsplit :
      Finset.univ.sup' hne (fun d : D => (P d).complexity + (Q d).complexity) ≤
      Finset.univ.sup' hne (fun d : D => (P d).complexity) +
      Finset.univ.sup' hne (fun d : D => (Q d).complexity) := by
    refine Finset.sup'_le
      (s := (Finset.univ : Finset D))
      (H := hne)
      (f := fun d : D => (P d).complexity + (Q d).complexity) ?_
    intro d hd
    exact add_le_add
      (Finset.le_sup' (s := Finset.univ) (f := fun d : D => (P d).complexity) (Finset.mem_univ d))
      (Finset.le_sup' (s := Finset.univ) (f := fun d : D => (Q d).complexity) (Finset.mem_univ d))
  have hsplit' :
      Real.log (Fintype.card D) +
          Finset.univ.sup' hne (fun d : D => (P d).complexity + (Q d).complexity)
      ≤ Real.log (Fintype.card D) +
          (Finset.univ.sup' hne (fun d : D => (P d).complexity) +
           Finset.univ.sup' hne (fun d : D => (Q d).complexity)) :=
    by linarith [hsplit]
  calc
    GroupoidObj.sigmaComplexity D (fun d => (P d).prod (Q d))
        ≤ Real.log (Fintype.card D) +
          Finset.univ.sup' hne (fun d : D => (P d).complexity + (Q d).complexity) := hpair
    _ ≤ Real.log (Fintype.card D) +
          (Finset.univ.sup' hne (fun d : D => (P d).complexity) +
           Finset.univ.sup' hne (fun d : D => (Q d).complexity)) := hsplit'
    _ = Real.log (Fintype.card D) +
          Finset.univ.sup' hne (fun d : D => (P d).complexity) +
          Finset.univ.sup' hne (fun d : D => (Q d).complexity) := by
        rw [add_assoc]

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

/-- Lower bound on sigma complexity: at least the maximum fiber complexity.
    Complement to `sigmaComplexity_le_logCard_max` (upper bound).
    Proof is `log_le_log` applied to `single_le_sum`. -/
theorem GroupoidObj.sigmaComplexity_ge_sup (D : Type*) [Fintype D] [Nonempty D]
    (P : D → GroupoidObj) :
    Finset.univ.sup' Finset.univ_nonempty (fun d : D => (P d).complexity) ≤
    GroupoidObj.sigmaComplexity D P := by
  apply Finset.sup'_le
  intro d _
  unfold GroupoidObj.sigmaComplexity GroupoidObj.complexity groupoidComplexity
  apply Real.log_le_log
  · exact groupoidPartitionFn_pos (x := (P d).base) (K := (P d).energy)
      (hsum := (P d).summable)
  · unfold GroupoidObj.sigmaPartFn GroupoidObj.partFn
    exact Finset.single_le_sum
      (fun d' _ => le_of_lt (groupoidPartitionFn_pos (x := (P d').base) (K := (P d').energy)
        (hsum := (P d').summable)))
      (Finset.mem_univ d)

end Bridge

end Simplicial
