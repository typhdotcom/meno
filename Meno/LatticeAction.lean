import Meno.SiegelPoisson
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # The Quadratic-Lattice Action: real positivity, charts, and the intrinsic dual

The thesis's carrier bundle, made lattice-honest twice over (reviews
#8, #9): a `QuadLatticeAction` is a finite free `ℤ`-module with a
symmetric bi-additive `ℝ`-valued form whose **real scalar extension**
`ℝ ⊗[ℤ] Λ` is positive definite — positivity on integral points alone
is *not* stored, because it does not suffice (review #9's
counterexample: `B((m,n),(m',n')) = (m+√2n)(m'+√2n')` on `ℤ²` is
positive at every nonzero lattice point yet has a real null direction
and a divergent Boltzmann sum). From real positivity everything else
is **derived**:

* `form_posDef` — integral positivity, through the lattice embedding
  `a ↦ 1 ⊗ a` (injective for free modules);
* `gram_posDef` — every finite basis's Gram matrix is positive
  definite on `ℝ`;
* `summable` — the Boltzmann weight is summable, through any integral
  basis and the coordinate engine `summable_exp_neg_quadForm`;
* `bilinBaseChange_posDef_of_gram` — the converse discharge: one
  positive-definite Gram chart certifies the real extension, which is
  how `classQuadAction` (`Meno/BasisIndependence.lean`) supplies the
  field.

Finite bases are **charts** (`chartAction`): form-preserving readings
of the bundle as coordinate `QuadraticAction`s, with a chart-free
partition function (`partFn_chartAction`) and a basis-independent
discriminant (`disc`, `disc_eq`).

**The intrinsic dual** (review #9): `Q.dual` lives on the dual lattice
`Module.Dual ℤ Q.Λ`, carrying the `π²`-scaled inverse of the real
extension — inverse in the genuine sense, through the flat/sharp
isomorphism of the positive-definite pairing, with no basis in the
definition. Every dual basis charts it as the coordinate dual
(`chartAction_dual`: the Gram of `b.dualBasis` is `π² · (gram b)⁻¹`),
the intrinsic Siegel–Poisson duality holds
(`QuadLatticeAction.duality`, prefactor `√(disc / π^rank)`), and the
double dual returns the original form along the canonical reflexivity
equivalence (`dual_dual`). The per-chart coordinate duality of the
graph carrier (`basisGramData_duality`) is a corollary, in
`Meno/BasisIndependence.lean`. -/

namespace Meno

open scoped BigOperators TensorProduct
open Matrix

universe u

/-! ## The canonical bilinear extension to the real scalar extension -/

section BaseChange

variable {Λ : Type u} [AddCommGroup Λ] [Module ℤ Λ]

/-- Symmetric bi-additive real data on a `ℤ`-module, bundled as a
`ℤ`-bilinear map. Right-additivity is symmetry plus left-additivity;
`ℤ`-linearity of an additive map is automatic (`map_intCast_smul`),
for whichever `Module ℤ` instances are in scope. -/
noncomputable def intBilin (f : Λ → Λ → ℝ) (hcomm : ∀ a b, f a b = f b a)
    (hadd : ∀ a₁ a₂ b, f (a₁ + a₂) b = f a₁ b + f a₂ b) :
    Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℝ where
  toFun a :=
    { toFun := f a
      map_add' := fun b₁ b₂ => by
        rw [hcomm a (b₁ + b₂), hadd b₁ b₂ a, hcomm b₁ a, hcomm b₂ a]
      map_smul' := fun n x => by
        have h := map_intCast_smul
          (AddMonoidHom.mk' (f a) fun b₁ b₂ => by
            rw [hcomm a (b₁ + b₂), hadd b₁ b₂ a, hcomm b₁ a, hcomm b₂ a])
          ℤ ℤ n x
        simpa using h }
  map_add' a₁ a₂ := LinearMap.ext fun b => hadd a₁ a₂ b
  map_smul' n a := LinearMap.ext fun b => by
    have h := map_intCast_smul
      (AddMonoidHom.mk' (fun y => f y b) fun a₁ a₂ => hadd a₁ a₂ b) ℤ ℤ n a
    simpa using h

@[simp] theorem intBilin_apply (f : Λ → Λ → ℝ) (hcomm) (hadd) (a b : Λ) :
    intBilin f hcomm hadd a b = f a b := rfl

/-- **The canonical `ℝ`-bilinear extension** of symmetric bi-additive
real data on `Λ` to the real scalar extension `ℝ ⊗[ℤ] Λ` — by the
universal property of base change (`liftBaseChange`), applied in each
slot. No basis appears. -/
noncomputable def bilinBaseChange (f : Λ → Λ → ℝ) (hcomm : ∀ a b, f a b = f b a)
    (hadd : ∀ a₁ a₂ b, f (a₁ + a₂) b = f a₁ b + f a₂ b) :
    (ℝ ⊗[ℤ] Λ) →ₗ[ℝ] (ℝ ⊗[ℤ] Λ) →ₗ[ℝ] ℝ :=
  LinearMap.liftBaseChange ℝ
    (((LinearMap.liftBaseChangeEquiv ℝ).toLinearMap.restrictScalars ℤ).comp
      (intBilin f hcomm hadd))

@[simp] theorem bilinBaseChange_tmul (f : Λ → Λ → ℝ) (hcomm) (hadd)
    (r s : ℝ) (a b : Λ) :
    bilinBaseChange f hcomm hadd (r ⊗ₜ a) (s ⊗ₜ b) = r * s * f a b := by
  simp only [bilinBaseChange, LinearMap.liftBaseChange_tmul, LinearMap.coe_comp,
    LinearMap.coe_restrictScalars, Function.comp_apply, LinearEquiv.coe_coe,
    LinearMap.smul_apply, smul_eq_mul, intBilin_apply]
  ring

theorem bilinBaseChange_one_tmul (f : Λ → Λ → ℝ) (hcomm) (hadd) (a b : Λ) :
    bilinBaseChange f hcomm hadd ((1 : ℝ) ⊗ₜ a) ((1 : ℝ) ⊗ₜ b) = f a b := by
  rw [bilinBaseChange_tmul]
  ring

/-- The lattice embeds in its real scalar extension: `1 ⊗ a` vanishes
only at `a = 0`, read off the base-changed basis coordinates of any
`ℤ`-basis. -/
theorem one_tmul_ne_zero [Module.Free ℤ Λ] {a : Λ} (ha : a ≠ 0) :
    (1 : ℝ) ⊗ₜ[ℤ] a ≠ (0 : ℝ ⊗[ℤ] Λ) := by
  intro h0
  apply ha
  set b := Module.Free.chooseBasis ℤ Λ with hb
  apply b.repr.injective
  ext i
  have h := congrArg (fun z => (b.baseChange ℝ).repr z i) h0
  simp only [Module.Basis.baseChange_repr_tmul, map_zero, Finsupp.coe_zero,
    Pi.zero_apply, zsmul_eq_mul, mul_one] at h
  rw [map_zero]
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  exact_mod_cast h

/-- The base-changed coordinates of an embedded lattice point are the
casts of its integer coordinates. -/
theorem baseChange_equivFun_one_tmul {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
    (x : Λ) (i : Fin n) :
    (b.baseChange ℝ).equivFun ((1 : ℝ) ⊗ₜ x) i = ((b.repr x i : ℤ) : ℝ) := by
  rw [Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
    zsmul_eq_mul, mul_one]

/-- The extension in base-changed coordinates: a finite double sum
against the Gram entries of the underlying basis. -/
theorem bilinBaseChange_apply_equivFun {n : ℕ} (f : Λ → Λ → ℝ) (hcomm) (hadd)
    (b : Module.Basis (Fin n) ℤ Λ) (x y : ℝ ⊗[ℤ] Λ) :
    bilinBaseChange f hcomm hadd x y
      = ∑ i, ∑ j, (b.baseChange ℝ).equivFun x i * (b.baseChange ℝ).equivFun y j
          * f (b i) (b j) := by
  set bR := b.baseChange ℝ with hbR
  have hx := (bR.sum_equivFun x).symm
  have hy := (bR.sum_equivFun y).symm
  have h1 : bilinBaseChange f hcomm hadd x
      = ∑ i, bR.equivFun x i • bilinBaseChange f hcomm hadd (bR i) := by
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
  rw [h1, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply]
  conv_lhs => rw [hy]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_smul]
  have hij : bilinBaseChange f hcomm hadd (bR i) (bR j) = f (b i) (b j) := by
    rw [hbR, Module.Basis.baseChange_apply, Module.Basis.baseChange_apply]
    exact bilinBaseChange_one_tmul f hcomm hadd (b i) (b j)
  rw [hij, smul_eq_mul]

/-- **The Gram-chart discharge** (review #9): one basis whose real Gram
matrix is positive definite certifies positive-definiteness of the
whole real extension. This is how concrete carriers
(`classQuadAction`) supply the `posDef_baseChange` field. -/
theorem bilinBaseChange_posDef_of_gram {n : ℕ} (f : Λ → Λ → ℝ) (hcomm) (hadd)
    (b : Module.Basis (Fin n) ℤ Λ)
    (hgram : (Matrix.of fun i j => f (b i) (b j)).PosDef) :
    ∀ x : ℝ ⊗[ℤ] Λ, x ≠ 0 → 0 < bilinBaseChange f hcomm hadd x x := by
  intro x hx
  set bR := b.baseChange ℝ with hbR
  set c : Fin n → ℝ := bR.equivFun x with hc
  have hcne : c ≠ 0 := by
    intro h0
    apply hx
    have := congrArg bR.equivFun.symm (hc.symm.trans h0)
    rwa [LinearEquiv.symm_apply_apply, map_zero] at this
  have hquad : bilinBaseChange f hcomm hadd x x
      = c ⬝ᵥ (Matrix.of fun i j => f (b i) (b j)).mulVec c := by
    rw [bilinBaseChange_apply_equivFun f hcomm hadd b x x,
      ← quadForm_dotProduct]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.of_apply]
    ring
  have hpos := (posDef_iff_dotProduct_mulVec.mp hgram).2 hcne
  have hstar : star c = c := funext fun i => star_trivial _
  rw [hstar] at hpos
  rw [hquad]
  exact hpos

end BaseChange

/-! ## The bundle -/

/-- An **integral quadratic-lattice action**: a finite free `ℤ`-module
of sectors — a genuine integral lattice (review #8) — with an
`ℝ`-valued symmetric bi-additive form whose **real scalar extension is
positive definite** (review #9: integral positivity is derived, never
stored, and stored summability is gone — both were assertion debt).
`toSectorAction` is the analytic projection, `QuadLatticeAction.rank`
the rank, `chartAction` the coordinate charts, `dual` the intrinsic
dual. -/
structure QuadLatticeAction where
  /-- The sector lattice. -/
  Λ : Type u
  [addCommGroup : AddCommGroup Λ]
  [module : Module ℤ Λ]
  [free : Module.Free ℤ Λ]
  [finite : Module.Finite ℤ Λ]
  /-- The bilinear form. -/
  form : Λ → Λ → ℝ
  form_comm : ∀ a b, form a b = form b a
  form_add_left : ∀ a₁ a₂ b, form (a₁ + a₂) b = form a₁ b + form a₂ b
  /-- Positive-definiteness on the **real scalar extension** — the
  genuinely lattice-honest positivity (review #9). -/
  posDef_baseChange : ∀ x : ℝ ⊗[ℤ] Λ, x ≠ 0 →
    0 < bilinBaseChange form form_comm form_add_left x x

namespace QuadLatticeAction

attribute [instance] QuadLatticeAction.addCommGroup QuadLatticeAction.module
  QuadLatticeAction.free QuadLatticeAction.finite

variable (Q : QuadLatticeAction.{u})

/-- The rank of the sector lattice — finite and free by the bundle
(review #8): the lattice is a genuine finite integral lattice. -/
noncomputable def rank : ℕ := Module.finrank ℤ Q.Λ

/-- The bundled `ℤ`-bilinear form. -/
noncomputable def bilin : Q.Λ →ₗ[ℤ] Q.Λ →ₗ[ℤ] ℝ :=
  intBilin Q.form Q.form_comm Q.form_add_left

@[simp] theorem bilin_apply (a b : Q.Λ) : Q.bilin a b = Q.form a b := rfl

/-- The real scalar extension of the form — canonical, basis-free. -/
noncomputable def formExt : (ℝ ⊗[ℤ] Q.Λ) →ₗ[ℝ] (ℝ ⊗[ℤ] Q.Λ) →ₗ[ℝ] ℝ :=
  bilinBaseChange Q.form Q.form_comm Q.form_add_left

@[simp] theorem formExt_tmul (r s : ℝ) (a b : Q.Λ) :
    Q.formExt (r ⊗ₜ a) (s ⊗ₜ b) = r * s * Q.form a b :=
  bilinBaseChange_tmul _ _ _ r s a b

theorem formExt_posDef (x : ℝ ⊗[ℤ] Q.Λ) (hx : x ≠ 0) : 0 < Q.formExt x x :=
  Q.posDef_baseChange x hx

theorem form_add_right (a b₁ b₂ : Q.Λ) :
    Q.form a (b₁ + b₂) = Q.form a b₁ + Q.form a b₂ := by
  rw [Q.form_comm, Q.form_add_left, Q.form_comm b₁ a, Q.form_comm b₂ a]

theorem form_zero_left (b : Q.Λ) : Q.form 0 b = 0 := by
  have h := Q.form_add_left 0 0 b
  rw [add_zero] at h
  linarith

/-- **Integral positivity is a theorem** (review #9): through the
lattice embedding `a ↦ 1 ⊗ a` into the real scalar extension. Same
name and statement as the retired field, so consumers are unchanged. -/
theorem form_posDef (a : Q.Λ) (ha : a ≠ 0) : 0 < Q.form a a := by
  have h := Q.posDef_baseChange ((1 : ℝ) ⊗ₜ a) (one_tmul_ne_zero ha)
  rwa [bilinBaseChange_one_tmul] at h

theorem form_self_nonneg (a : Q.Λ) : 0 ≤ Q.form a a := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [Q.form_zero_left]
  · exact (Q.form_posDef a ha).le

/-! ## Charts: finite bases read the bundle in coordinates -/

/-- The Gram matrix of the form at a finite basis. -/
noncomputable def gram {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Q.form (b i) (b j)

@[simp] theorem gram_apply {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ)
    (i j : Fin n) : Q.gram b i j = Q.form (b i) (b j) := rfl

theorem gram_transpose {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ) :
    (Q.gram b)ᵀ = Q.gram b := by
  ext i j
  exact Q.form_comm (b j) (b i)

/-- The integral coordinate expansion of the form at any finite basis. -/
theorem form_repr {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ) (x y : Q.Λ) :
    Q.form x y
      = ∑ i, ∑ j, ((b.repr x i : ℤ) : ℝ) * ((b.repr y j : ℤ) : ℝ)
          * Q.form (b i) (b j) := by
  have h := bilinBaseChange_apply_equivFun Q.form Q.form_comm Q.form_add_left b
    ((1 : ℝ) ⊗ₜ x) ((1 : ℝ) ⊗ₜ y)
  rw [bilinBaseChange_one_tmul] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [baseChange_equivFun_one_tmul, baseChange_equivFun_one_tmul]

/-- **Every Gram chart is positive definite on `ℝ`** — a theorem of the
real extension, consumed by the summability engine and the dual. -/
theorem gram_posDef {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ) :
    (Q.gram b).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun c hc => ?_⟩
  · show (Q.gram b)ᴴ = Q.gram b
    ext i j
    calc (Q.gram b)ᴴ i j = star ((Q.gram b) j i) := rfl
      _ = (Q.gram b) j i := star_trivial _
      _ = (Q.gram b) i j := Q.form_comm (b j) (b i)
  · set bR := b.baseChange ℝ with hbR
    set x : ℝ ⊗[ℤ] Q.Λ := bR.equivFun.symm c with hx
    have hxne : x ≠ 0 := by
      intro h0
      apply hc
      have := congrArg bR.equivFun (hx.symm.trans h0)
      rwa [LinearEquiv.apply_symm_apply, map_zero] at this
    have hpos := Q.posDef_baseChange x hxne
    have hcoord : bR.equivFun x = c := by
      rw [hx, LinearEquiv.apply_symm_apply]
    have hquad : Q.formExt x x = c ⬝ᵥ (Q.gram b).mulVec c := by
      show bilinBaseChange Q.form Q.form_comm Q.form_add_left x x = _
      rw [bilinBaseChange_apply_equivFun Q.form Q.form_comm Q.form_add_left b x x,
        ← quadForm_dotProduct]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← hbR, hcoord, gram_apply]
      ring
    have hstar : star c = c := funext fun i => star_trivial _
    rw [hstar]
    rw [← hquad]
    exact hpos

/-- **Summability is a theorem** (review #9): through any integral
basis, by the coordinate engine `summable_exp_neg_quadForm` at the
(positive-definite) Gram chart. Same name and statement as the retired
field, so consumers are unchanged. -/
theorem summable : Summable (fun a : Q.Λ => Real.exp (-(Q.form a a))) := by
  set b := Module.finBasis ℤ Q.Λ with hb
  have hsum := summable_exp_neg_quadForm (Q.gram_posDef b)
  have h := (Equiv.summable_iff b.equivFun.toEquiv).mpr hsum
  refine h.congr fun a => ?_
  show Real.exp (-(∑ i, ∑ j, Q.gram b i j * ((b.equivFun a i : ℤ) : ℝ)
      * ((b.equivFun a j : ℤ) : ℝ))) = Real.exp (-(Q.form a a))
  congr 1
  rw [neg_inj, Q.form_repr b a a]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Module.Basis.equivFun_apply, gram_apply]
  ring

/-- The analytic projection: forget the lattice and the bilinear
structure, keep sectors, energies `E a := form a a`, and the sum. -/
noncomputable def toSectorAction : SectorAction.{u} where
  Λ := Q.Λ
  E := fun a => Q.form a a
  E_zero := ⟨0, by rw [Q.form_zero_left]⟩
  E_nonneg := Q.form_self_nonneg
  summable := Q.summable

/-- **The chart at a finite basis**: the bundle read in coordinates, as
a `QuadraticAction` on the Gram matrix — form-preserving by
construction (`gram_apply`, `form_repr`). -/
noncomputable def chartAction {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ) :
    QuadraticAction n where
  Q := Q.gram b
  Q_posDef := Q.gram_posDef b

@[simp] theorem chartAction_Q {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ) :
    (Q.chartAction b).Q = Q.gram b := rfl

/-- **The chart computes the partition function**: the coordinate
Boltzmann sum of any chart is the intrinsic Boltzmann sum. -/
theorem partFn_chartAction {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ) :
    (Q.chartAction b).toSectorAction.partFn = Q.toSectorAction.partFn := by
  show ∑' k : Fin n → ℤ, Real.exp (-(Q.chartAction b).energy k)
    = ∑' a : Q.Λ, Real.exp (-(Q.form a a))
  rw [← Equiv.tsum_eq b.equivFun.toEquiv
    (fun k => Real.exp (-(Q.chartAction b).energy k))]
  refine tsum_congr fun a => ?_
  congr 1
  rw [neg_inj]
  show ∑ i, ∑ j, Q.gram b i j * ((b.equivFun a i : ℤ) : ℝ)
      * ((b.equivFun a j : ℤ) : ℝ) = Q.form a a
  rw [Q.form_repr b a a]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Module.Basis.equivFun_apply, gram_apply]
  ring

/-- Any finite basis of the lattice has exactly `rank` elements. -/
theorem card_eq_rank {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ) :
    n = Q.rank := by
  have h := Module.finrank_eq_card_basis b
  rw [Fintype.card_fin] at h
  exact h.symm

/-! ## The discriminant -/

/-- **The discriminant**: the Gram determinant at the canonical finite
basis — basis-independent by `disc_eq`. -/
noncomputable def disc : ℝ := (Q.gram (Module.finBasis ℤ Q.Λ)).det

theorem disc_pos : 0 < Q.disc := (Q.gram_posDef _).det_pos

/-- Gram matrices of two same-index bases are congruent by the integral
change-of-basis matrix. -/
theorem gram_congr {n : ℕ} (b b' : Module.Basis (Fin n) ℤ Q.Λ) :
    Q.gram b' = ((b.toMatrix ⇑b').map (Int.cast : ℤ → ℝ))ᵀ * Q.gram b
      * ((b.toMatrix ⇑b').map (Int.cast : ℤ → ℝ)) := by
  ext i j
  have hexp : Q.form (b' i) (b' j)
      = ∑ l, ∑ m, ((b.toMatrix ⇑b' l i : ℤ) : ℝ)
          * (((b.toMatrix ⇑b' m j : ℤ) : ℝ) * Q.form (b l) (b m)) := by
    conv_lhs => rw [← b.sum_toMatrix_smul_self ⇑b' i,
      ← b.sum_toMatrix_smul_self ⇑b' j]
    show Q.bilin _ _ = _
    rw [map_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [LinearMap.map_smul, map_sum, LinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [LinearMap.map_smul, LinearMap.smul_apply, bilin_apply,
      zsmul_eq_mul, zsmul_eq_mul]
    ring
  rw [gram_apply, hexp, Finset.sum_comm]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    gram_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **The discriminant is basis-independent** (review #9): any two
finite bases are related by a unimodular integral matrix, whose
squared determinant is `1`. -/
theorem disc_eq {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ) :
    Q.disc = (Q.gram b).det := by
  set e : Fin Q.rank ≃ Fin n := finCongr (Q.card_eq_rank b).symm with he
  set b₀' : Module.Basis (Fin n) ℤ Q.Λ := (Module.finBasis ℤ Q.Λ).reindex e
    with hb₀'
  have h0 : Q.disc = (Q.gram b₀').det := by
    have hsub : Q.gram b₀'
        = (Q.gram (Module.finBasis ℤ Q.Λ)).submatrix ⇑e.symm ⇑e.symm := by
      ext i j
      rw [Matrix.submatrix_apply]
      show Q.form (b₀' i) (b₀' j)
        = Q.form (Module.finBasis ℤ Q.Λ (e.symm i))
            (Module.finBasis ℤ Q.Λ (e.symm j))
      rw [hb₀', Module.Basis.reindex_apply, Module.Basis.reindex_apply]
      rfl
    rw [hsub]
    exact (Matrix.det_submatrix_equiv_self e.symm _).symm
  have hcongr := Q.gram_congr b₀' b
  set P := (b₀'.toMatrix ⇑b).map (Int.cast : ℤ → ℝ) with hP
  have hdetP : P.det = ((b₀'.toMatrix ⇑b).det : ℝ) :=
    ((Int.castRingHom ℝ).map_det (b₀'.toMatrix ⇑b)).symm
  have hunit : IsUnit (b₀'.toMatrix ⇑b).det := by
    letI := b₀'.invertibleToMatrix b
    exact Matrix.isUnit_det_of_invertible _
  have hsq : P.det * P.det = 1 := by
    rcases Int.isUnit_iff.mp hunit with h1 | h1 <;>
      rw [hdetP, h1] <;> norm_num
  rw [h0, hcongr, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  linear_combination (-(Q.gram b₀').det) * hsq

/-! ## The intrinsic dual -/

/-- The real scalar extension is finite-dimensional over `ℝ`, by the
base-changed canonical basis. -/
noncomputable instance : Module.Finite ℝ (ℝ ⊗[ℤ] Q.Λ) :=
  Module.Finite.of_basis ((Module.finBasis ℤ Q.Λ).baseChange ℝ)

/-- Real extension of integral functionals, `ℤ`-linearly:
`Dual ℤ Λ → Dual ℝ (ℝ ⊗ Λ)` by base change of `φ` postcomposed with
`ℤ → ℝ`. -/
noncomputable def dualCastHom :
    Module.Dual ℤ Q.Λ →ₗ[ℤ] Module.Dual ℝ (ℝ ⊗[ℤ] Q.Λ) :=
  ((LinearMap.liftBaseChangeEquiv ℝ).toLinearMap.restrictScalars ℤ).comp
    (LinearMap.llcomp ℤ Q.Λ ℤ ℝ (Algebra.linearMap ℤ ℝ))

theorem dualCastHom_tmul (φ : Module.Dual ℤ Q.Λ) (r : ℝ) (a : Q.Λ) :
    Q.dualCastHom φ (r ⊗ₜ a) = r * ((φ a : ℤ) : ℝ) := by
  show r • (Algebra.linearMap ℤ ℝ) (φ a) = r * ((φ a : ℤ) : ℝ)
  rw [smul_eq_mul]
  congr 1

/-- **The flat isomorphism** of the positive-definite real extension:
`x ↦ B(x, ·)` is injective by positivity, hence an isomorphism onto
the dual space in finite dimension. Its inverse is the sharp map. -/
noncomputable def flatEquiv :
    (ℝ ⊗[ℤ] Q.Λ) ≃ₗ[ℝ] Module.Dual ℝ (ℝ ⊗[ℤ] Q.Λ) :=
  LinearMap.linearEquivOfInjective Q.formExt
    (fun x y hxy => by
      by_contra hne
      have hpos := Q.formExt_posDef (x - y) (sub_ne_zero.mpr hne)
      have h0 : Q.formExt (x - y) (x - y) = 0 := by
        simp only [map_sub, LinearMap.sub_apply, hxy]
        ring
      rw [h0] at hpos
      exact lt_irrefl 0 hpos)
    Subspace.dual_finrank_eq.symm

theorem flatEquiv_apply (x y : ℝ ⊗[ℤ] Q.Λ) :
    Q.flatEquiv x y = Q.formExt x y := rfl

/-- The extension is symmetric — inherited from `form_comm` through
the coordinate expansion. -/
theorem formExt_comm (x y : ℝ ⊗[ℤ] Q.Λ) : Q.formExt x y = Q.formExt y x := by
  show bilinBaseChange Q.form Q.form_comm Q.form_add_left x y
    = bilinBaseChange Q.form Q.form_comm Q.form_add_left y x
  rw [bilinBaseChange_apply_equivFun Q.form Q.form_comm Q.form_add_left
      (Module.finBasis ℤ Q.Λ) x y,
    bilinBaseChange_apply_equivFun Q.form Q.form_comm Q.form_add_left
      (Module.finBasis ℤ Q.Λ) y x,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Q.form_comm (Module.finBasis ℤ Q.Λ i) (Module.finBasis ℤ Q.Λ j)]
  ring

/-- The extension against an embedded basis vector, in coordinates. -/
theorem formExt_basis {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ) (l : Fin n)
    (y : ℝ ⊗[ℤ] Q.Λ) :
    Q.formExt ((b.baseChange ℝ) l) y
      = ∑ m, (b.baseChange ℝ).equivFun y m * Q.gram b l m := by
  conv_lhs => rw [← (b.baseChange ℝ).sum_equivFun y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [LinearMap.map_smul, smul_eq_mul]
  congr 1
  rw [Module.Basis.baseChange_apply, Module.Basis.baseChange_apply]
  exact bilinBaseChange_one_tmul Q.form Q.form_comm Q.form_add_left (b l) (b m)

/-- **The intrinsic dual form** on the dual lattice: `π²` times the
inverse real pairing — each functional's real extension pulled back
through the sharp map and paired by the form. No basis appears. -/
noncomputable def dualForm (φ ψ : Module.Dual ℤ Q.Λ) : ℝ :=
  Real.pi ^ 2 * Q.formExt (Q.flatEquiv.symm (Q.dualCastHom φ))
    (Q.flatEquiv.symm (Q.dualCastHom ψ))

theorem dualForm_comm (φ ψ : Module.Dual ℤ Q.Λ) :
    Q.dualForm φ ψ = Q.dualForm ψ φ := by
  unfold dualForm
  rw [Q.formExt_comm]

theorem dualForm_add_left (φ₁ φ₂ ψ : Module.Dual ℤ Q.Λ) :
    Q.dualForm (φ₁ + φ₂) ψ = Q.dualForm φ₁ ψ + Q.dualForm φ₂ ψ := by
  unfold dualForm
  rw [map_add, map_add, map_add, LinearMap.add_apply]
  ring

/-- **The dual chart entries** (review #9): at any basis, the dual
form of the dual basis is exactly `π²` times the inverse Gram matrix. -/
theorem dualForm_dualBasis {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ)
    (i j : Fin n) :
    Q.dualForm (b.dualBasis i) (b.dualBasis j)
      = Real.pi ^ 2 * (Q.gram b)⁻¹ i j := by
  have hdet : IsUnit (Q.gram b).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (Q.gram_posDef b).det_pos)
  have hGinv_symm : ∀ k l, (Q.gram b)⁻¹ k l = (Q.gram b)⁻¹ l k := by
    intro k l
    calc (Q.gram b)⁻¹ k l = ((Q.gram b)⁻¹)ᵀ l k := rfl
      _ = ((Q.gram b)ᵀ)⁻¹ l k := by rw [Matrix.transpose_nonsing_inv]
      _ = (Q.gram b)⁻¹ l k := by rw [Q.gram_transpose]
  -- the sharp of a dual-basis functional, explicitly
  set w : Fin n → ℝ ⊗[ℤ] Q.Λ := fun k =>
    (b.baseChange ℝ).equivFun.symm (fun l => (Q.gram b)⁻¹ l k) with hw
  have hwcoord : ∀ k, (b.baseChange ℝ).equivFun (w k)
      = fun l => (Q.gram b)⁻¹ l k := by
    intro k
    rw [hw, LinearEquiv.apply_symm_apply]
  have hflat : ∀ k, Q.flatEquiv (w k) = Q.dualCastHom (b.dualBasis k) := by
    intro k
    refine (b.baseChange ℝ).ext fun l => ?_
    rw [Module.Basis.baseChange_apply]
    have hL : Q.flatEquiv (w k) ((1 : ℝ) ⊗ₜ b l)
        = if l = k then 1 else 0 := by
      rw [flatEquiv_apply, Q.formExt_comm,
        ← Module.Basis.baseChange_apply (S := ℝ) b l, Q.formExt_basis b l (w k)]
      have : ∀ m, (b.baseChange ℝ).equivFun (w k) m * Q.gram b l m
          = Q.gram b l m * (Q.gram b)⁻¹ m k := by
        intro m
        rw [hwcoord k]
        ring
      rw [Finset.sum_congr rfl fun m _ => this m,
        ← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hdet, Matrix.one_apply]
    have hR : Q.dualCastHom (b.dualBasis k) ((1 : ℝ) ⊗ₜ b l)
        = if l = k then 1 else 0 := by
      rw [Q.dualCastHom_tmul, one_mul, Module.Basis.dualBasis_apply_self]
      split_ifs <;> norm_num
    rw [hL, hR]
  have hsharp : ∀ k, Q.flatEquiv.symm (Q.dualCastHom (b.dualBasis k)) = w k := by
    intro k
    rw [← hflat k, LinearEquiv.symm_apply_apply]
  unfold dualForm
  rw [hsharp i, hsharp j]
  congr 1
  -- B(w i, w j) = (G⁻¹)ᵢⱼ
  have h1 : Q.formExt (w i) (w j)
      = ∑ k, (Q.gram b)⁻¹ k i * ∑ m, (Q.gram b)⁻¹ m j * Q.gram b k m := by
    have hexp : ∀ v : Fin n → ℝ, ∀ y : ℝ ⊗[ℤ] Q.Λ,
        Q.formExt ((b.baseChange ℝ).equivFun.symm v) y
          = ∑ k, v k * ∑ m, (b.baseChange ℝ).equivFun y m * Q.gram b k m := by
      intro v y
      rw [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul]
      congr 1
      exact Q.formExt_basis b k y
    have hwj := hwcoord j
    simp only [hw]
    rw [hexp (fun l => (Q.gram b)⁻¹ l i) _]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    rw [LinearEquiv.apply_symm_apply]
  rw [h1]
  have hinner : ∀ k, ∑ m, (Q.gram b)⁻¹ m j * Q.gram b k m
      = (1 : Matrix (Fin n) (Fin n) ℝ) k j := by
    intro k
    rw [Finset.sum_congr rfl fun m _ =>
        (by ring : (Q.gram b)⁻¹ m j * Q.gram b k m
          = Q.gram b k m * (Q.gram b)⁻¹ m j),
      ← Matrix.mul_apply, Matrix.mul_nonsing_inv _ hdet]
  rw [Finset.sum_congr rfl fun k _ => by rw [hinner k]]
  rw [Finset.sum_eq_single j
    (fun k _ hk => by rw [Matrix.one_apply_ne hk, mul_zero])
    (fun h => absurd (Finset.mem_univ j) h)]
  rw [Matrix.one_apply_eq, mul_one, hGinv_symm j i]

/-- **THE INTRINSIC DUAL** (review #9): the dual lattice
`Module.Dual ℤ Λ`, carrying `π²` times the inverse real form. The
instances come from the dual of a finite free module; positivity
discharges through the dual Gram chart `π² · (gram b)⁻¹`. -/
noncomputable def dual : QuadLatticeAction.{u} where
  Λ := Module.Dual ℤ Q.Λ
  form := Q.dualForm
  form_comm := Q.dualForm_comm
  form_add_left := Q.dualForm_add_left
  posDef_baseChange := by
    refine bilinBaseChange_posDef_of_gram _ _ _
      (Module.finBasis ℤ Q.Λ).dualBasis ?_
    have hmat : (Matrix.of fun i j =>
          Q.dualForm ((Module.finBasis ℤ Q.Λ).dualBasis i)
            ((Module.finBasis ℤ Q.Λ).dualBasis j))
        = Real.pi ^ 2 • (Q.gram (Module.finBasis ℤ Q.Λ))⁻¹ := by
      ext i j
      rw [Matrix.of_apply, Q.dualForm_dualBasis (Module.finBasis ℤ Q.Λ) i j,
        Matrix.smul_apply, smul_eq_mul]
    rw [hmat]
    exact posDef_smul' (posDef_inv (Q.gram_posDef (Module.finBasis ℤ Q.Λ)))
      (by positivity)

@[simp] theorem dual_Λ : Q.dual.Λ = Module.Dual ℤ Q.Λ := rfl

@[simp] theorem dual_form (φ ψ : Module.Dual ℤ Q.Λ) :
    Q.dual.form φ ψ = Q.dualForm φ ψ := rfl

/-- **The dual Gram chart, in matrix form**: at any basis `b`, the dual
bundle's Gram at the dual basis is `π²` times the inverse Gram. -/
theorem gram_dual {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ) :
    Q.dual.gram b.dualBasis = Real.pi ^ 2 • (Q.gram b)⁻¹ := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact Q.dualForm_dualBasis b i j

/-- **Every dual basis charts the dual as the coordinate dual**
(review #9): the chart of `Q.dual` at `b.dualBasis` **is**
`QuadraticAction.dual` of the chart of `Q` at `b`. -/
theorem chartAction_dual {n : ℕ} (b : Module.Basis (Fin n) ℤ Q.Λ) :
    Q.dual.chartAction b.dualBasis = (Q.chartAction b).dual :=
  QuadraticAction.eq_of_Q_eq (by
    rw [chartAction_Q, QuadraticAction.dual_Q, chartAction_Q, Q.gram_dual b])

/-- **THE INTRINSIC SIEGEL–POISSON DUALITY** (review #9): the dual
bundle's partition function against the original's, with the
basis-independent prefactor `√(disc / π^rank)` — stated with no basis,
proved through one chart and the coordinate duality
(`QuadraticAction.duality`). -/
theorem duality :
    (↑(Q.dual.toSectorAction.partFn) : ℂ)
      = ↑(Q.disc / Real.pi ^ Q.rank : ℝ) ^ ((1 : ℂ) / 2)
        * ↑(Q.toSectorAction.partFn) := by
  have h1 : Q.toSectorAction.partFn
      = (Q.chartAction (Module.finBasis ℤ Q.Λ)).toSectorAction.partFn :=
    (Q.partFn_chartAction (Module.finBasis ℤ Q.Λ)).symm
  have h2 : Q.dual.toSectorAction.partFn
      = (Q.chartAction (Module.finBasis ℤ Q.Λ)).dual.toSectorAction.partFn := by
    rw [← Q.chartAction_dual (Module.finBasis ℤ Q.Λ)]
    exact (Q.dual.partFn_chartAction (Module.finBasis ℤ Q.Λ).dualBasis).symm
  rw [h1, h2, (Q.chartAction (Module.finBasis ℤ Q.Λ)).duality]
  rfl

/-- **The double dual is the original** (review #9): along the
canonical reflexivity equivalence, the double-dual form is the
original form — `π² · (π² · B⁻¹)⁻¹ = B`, verified at the double-dual
chart, stated intrinsically. -/
theorem dual_dual (x y : Q.Λ) :
    Q.dual.dual.form (Module.evalEquiv ℤ Q.Λ x) (Module.evalEquiv ℤ Q.Λ y)
      = Q.form x y := by
  have hπ : (Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  have hgram : Q.dual.dual.gram (Module.finBasis ℤ Q.Λ).dualBasis.dualBasis
      = Q.gram (Module.finBasis ℤ Q.Λ) := by
    rw [Q.dual.gram_dual (Module.finBasis ℤ Q.Λ).dualBasis,
      Q.gram_dual (Module.finBasis ℤ Q.Λ),
      smul_inv_of_isUnit hπ (isUnit_iff_ne_zero.mpr
        (ne_of_gt (posDef_inv (Q.gram_posDef (Module.finBasis ℤ Q.Λ))).det_pos)),
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr
        (ne_of_gt (Q.gram_posDef (Module.finBasis ℤ Q.Λ)).det_pos)),
      smul_smul, mul_inv_cancel₀ hπ, one_smul]
  have hcoord : ∀ z : Q.Λ, ∀ i,
      (Module.finBasis ℤ Q.Λ).dualBasis.dualBasis.repr
          (Module.evalEquiv ℤ Q.Λ z) i
        = (Module.finBasis ℤ Q.Λ).repr z i := by
    intro z i
    rw [Module.Basis.dualBasis_repr, Module.evalEquiv_apply,
      Module.Dual.eval_apply, Module.Basis.dualBasis_apply]
  rw [Q.dual.dual.form_repr (Module.finBasis ℤ Q.Λ).dualBasis.dualBasis
      (Module.evalEquiv ℤ Q.Λ x) (Module.evalEquiv ℤ Q.Λ y),
    Q.form_repr (Module.finBasis ℤ Q.Λ) x y]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  · congr 1
    · exact congrArg _ (hcoord x i)
    · exact congrArg _ (hcoord y j)
  · exact congrFun (congrFun hgram i) j

/-- The dual lattice has the same rank. -/
theorem dual_rank : Q.dual.rank = Q.rank := by
  show Module.finrank ℤ (Module.Dual ℤ Q.Λ) = Module.finrank ℤ Q.Λ
  rw [Module.finrank_eq_card_basis (Module.finBasis ℤ Q.Λ).dualBasis,
    Fintype.card_fin]

/-! ## Form-preserving equivalences and the dual involution (review #10) -/

/-- A **form-preserving equivalence** of quadratic-lattice actions
(review #10): a `ℤ`-linear equivalence of the lattices that carries
one form to the other. Rank, energy, partition function, and
discriminant are invariants (`Equiv.rank_eq`, `Equiv.form_eq`,
`Equiv.partFn_eq`, `Equiv.disc_eq`). -/
structure Equiv (Q Q' : QuadLatticeAction.{u}) where
  /-- The underlying linear equivalence of sector lattices. -/
  toLinearEquiv : Q.Λ ≃ₗ[ℤ] Q'.Λ
  form_eq : ∀ a b : Q.Λ,
    Q'.form (toLinearEquiv a) (toLinearEquiv b) = Q.form a b

namespace Equiv

variable {Q Q' Q'' : QuadLatticeAction.{u}}

theorem ext {e e' : Q.Equiv Q'} (h : e.toLinearEquiv = e'.toLinearEquiv) :
    e = e' := by
  cases e
  cases e'
  simpa using h

/-- The identity equivalence (review #11). -/
def refl (Q : QuadLatticeAction.{u}) : Q.Equiv Q where
  toLinearEquiv := LinearEquiv.refl ℤ Q.Λ
  form_eq _ _ := rfl

/-- Form-preserving equivalences invert. -/
def symm (e : Q.Equiv Q') : Q'.Equiv Q where
  toLinearEquiv := e.toLinearEquiv.symm
  form_eq a b := by
    have h := e.form_eq (e.toLinearEquiv.symm a) (e.toLinearEquiv.symm b)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    exact h.symm

/-- Form-preserving equivalences compose (review #11). -/
def trans (e : Q.Equiv Q') (e' : Q'.Equiv Q'') : Q.Equiv Q'' where
  toLinearEquiv := e.toLinearEquiv.trans e'.toLinearEquiv
  form_eq a b := by
    show Q''.form (e'.toLinearEquiv (e.toLinearEquiv a))
      (e'.toLinearEquiv (e.toLinearEquiv b)) = Q.form a b
    rw [e'.form_eq, e.form_eq]

@[simp] theorem refl_trans (e : Q.Equiv Q') : (refl Q).trans e = e :=
  ext (by ext x; rfl)

@[simp] theorem trans_refl (e : Q.Equiv Q') : e.trans (refl Q') = e :=
  ext (by ext x; rfl)

theorem trans_assoc (e : Q.Equiv Q') (e' : Q'.Equiv Q'')
    {Q''' : QuadLatticeAction.{u}} (e'' : Q''.Equiv Q''') :
    (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  ext (by ext x; rfl)

/-- **Rank invariance.** -/
theorem rank_eq (e : Q.Equiv Q') : Q.rank = Q'.rank := by
  show Module.finrank ℤ Q.Λ = Module.finrank ℤ Q'.Λ
  exact e.toLinearEquiv.finrank_eq

/-- **Energy invariance** — the diagonal of `form_eq`. -/
theorem energy_eq (e : Q.Equiv Q') (a : Q.Λ) :
    Q'.form (e.toLinearEquiv a) (e.toLinearEquiv a) = Q.form a a :=
  e.form_eq a a

/-- **Partition-function invariance**: reindex the Boltzmann sum along
the underlying equivalence and transport each term by `form_eq`. -/
theorem partFn_eq (e : Q.Equiv Q') :
    Q'.toSectorAction.partFn = Q.toSectorAction.partFn := by
  show ∑' a' : Q'.Λ, Real.exp (-(Q'.form a' a'))
    = ∑' a : Q.Λ, Real.exp (-(Q.form a a))
  rw [← _root_.Equiv.tsum_eq e.toLinearEquiv.toEquiv
    (fun a' => Real.exp (-(Q'.form a' a')))]
  exact tsum_congr fun a => by
    rw [show (e.toLinearEquiv.toEquiv a : Q'.Λ) = e.toLinearEquiv a from rfl,
      e.energy_eq a]

/-- Gram matrices transport along the mapped basis. -/
theorem gram_map (e : Q.Equiv Q') {n : ℕ}
    (b : Module.Basis (Fin n) ℤ Q.Λ) :
    Q'.gram (b.map e.toLinearEquiv) = Q.gram b := by
  ext i j
  show Q'.form ((b.map e.toLinearEquiv) i) ((b.map e.toLinearEquiv) j)
    = Q.form (b i) (b j)
  rw [Module.Basis.map_apply, Module.Basis.map_apply]
  exact e.form_eq (b i) (b j)

/-- **Discriminant invariance.** -/
theorem disc_eq (e : Q.Equiv Q') : Q'.disc = Q.disc := by
  rw [Q'.disc_eq ((Module.finBasis ℤ Q.Λ).map e.toLinearEquiv), e.gram_map]
  exact (Q.disc_eq (Module.finBasis ℤ Q.Λ)).symm

/-- **Form-preserving equivalences dualize, contravariantly**
(review #11): the dual map of the underlying equivalence carries the
dual forms to each other — chart both dual forms at a basis and its
image, where the Grams agree (`gram_map`). -/
noncomputable def dual (e : Q.Equiv Q') : (Q'.dual).Equiv (Q.dual) where
  toLinearEquiv := e.toLinearEquiv.dualMap
  form_eq φ ψ := by
    have hcoord : ∀ (χ : Module.Dual ℤ Q'.Λ)
        (i : Fin (Module.finrank ℤ Q.Λ)),
        (Module.finBasis ℤ Q.Λ).dualBasis.repr (e.toLinearEquiv.dualMap χ) i
          = ((Module.finBasis ℤ Q.Λ).map e.toLinearEquiv).dualBasis.repr χ i := by
      intro χ i
      rw [Module.Basis.dualBasis_repr, Module.Basis.dualBasis_repr]
      show χ (e.toLinearEquiv (Module.finBasis ℤ Q.Λ i)) = χ _
      rw [Module.Basis.map_apply]
    have hL := Q.dual.form_repr (Module.finBasis ℤ Q.Λ).dualBasis
      (e.toLinearEquiv.dualMap φ) (e.toLinearEquiv.dualMap ψ)
    have hR := Q'.dual.form_repr
      ((Module.finBasis ℤ Q.Λ).map e.toLinearEquiv).dualBasis φ ψ
    refine hL.trans (Eq.trans ?_ hR.symm)
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    · congr 1
      · exact congrArg _ (hcoord φ i)
      · exact congrArg _ (hcoord ψ j)
    · show Q.dualForm ((Module.finBasis ℤ Q.Λ).dualBasis i)
          ((Module.finBasis ℤ Q.Λ).dualBasis j)
        = Q'.dualForm
            (((Module.finBasis ℤ Q.Λ).map e.toLinearEquiv).dualBasis i)
            (((Module.finBasis ℤ Q.Λ).map e.toLinearEquiv).dualBasis j)
      rw [Q.dualForm_dualBasis (Module.finBasis ℤ Q.Λ) i j,
        Q'.dualForm_dualBasis ((Module.finBasis ℤ Q.Λ).map e.toLinearEquiv) i j,
        e.gram_map (Module.finBasis ℤ Q.Λ)]

end Equiv

/-- **THE DUAL INVOLUTION, BUNDLED** (review #10): the canonical
reflexivity equivalence is a form-preserving equivalence
`Q.dual.dual ≃q Q` — the double dual *is* the original action, with
rank, energy, discriminant, and partition function transported by the
`Equiv` invariants. -/
noncomputable def dualDual : (Q.dual.dual).Equiv Q :=
  (⟨Module.evalEquiv ℤ Q.Λ, Q.dual_dual⟩ : Q.Equiv Q.dual.dual).symm

/-- The double dual's partition function is the original's — through
the bundled involution. -/
theorem partFn_dualDual :
    Q.dual.dual.toSectorAction.partFn = Q.toSectorAction.partFn :=
  (Q.dualDual).partFn_eq.symm

/-- **Dual-double naturality** (review #11): the involution commutes
with every form-preserving equivalence — reflexivity is natural. -/
theorem dualDual_naturality {Q' : QuadLatticeAction.{u}} (e : Q.Equiv Q') :
    (Q.dualDual).trans e = (e.dual.dual).trans Q'.dualDual := by
  refine Equiv.ext ?_
  refine LinearEquiv.toLinearMap_injective ?_
  ext x
  show e.toLinearEquiv ((Module.evalEquiv ℤ Q.Λ).symm x)
    = (Module.evalEquiv ℤ Q'.Λ).symm
        (e.toLinearEquiv.dualMap.dualMap x)
  apply (Module.evalEquiv ℤ Q'.Λ).injective
  rw [LinearEquiv.apply_symm_apply]
  have h := Module.Dual.eval_comp_comp_evalEquiv_eq
    (f := e.toLinearEquiv.toLinearMap)
  have hx := congrArg (fun L => L x) h
  simp only [LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe] at hx
  rw [Module.evalEquiv_apply]
  exact hx

/-- **The reciprocal-discriminant law** (review #10):
`disc(Q^∨) = π^{2·rank} / disc(Q)`. -/
theorem disc_dual : Q.dual.disc = Real.pi ^ (2 * Q.rank) / Q.disc := by
  rw [Q.dual.disc_eq (Module.finBasis ℤ Q.Λ).dualBasis, Q.gram_dual,
    Matrix.det_smul, Matrix.det_nonsing_inv, Fintype.card_fin,
    Ring.inverse_eq_inv]
  rw [show Q.disc = (Q.gram (Module.finBasis ℤ Q.Λ)).det from rfl,
    div_eq_mul_inv, ← pow_mul]
  rfl

/-- **The two duality prefactors multiply to one** (review #11): the
analytic cancellation exposed as its own theorem —
`√(disc(Q^∨)/π^r) · √(disc(Q)/π^r) = 1`, through the
reciprocal-discriminant law and `dual_rank`. -/
theorem dual_prefactor_mul_one :
    ((Q.dual.disc / Real.pi ^ Q.dual.rank : ℝ) : ℂ) ^ ((1 : ℂ) / 2)
      * ((Q.disc / Real.pi ^ Q.rank : ℝ) : ℂ) ^ ((1 : ℂ) / 2) = 1 := by
  rw [Q.disc_dual, Q.dual_rank]
  have hpos : (0 : ℝ) < Q.disc / Real.pi ^ Q.rank :=
    div_pos Q.disc_pos (pow_pos Real.pi_pos _)
  have h1 : Real.pi ^ (2 * Q.rank) / Q.disc / Real.pi ^ Q.rank
      = (Q.disc / Real.pi ^ Q.rank)⁻¹ := by
    rw [two_mul, pow_add]
    field_simp
  rw [h1, ← Complex.mul_cpow_ofReal_nonneg (inv_nonneg.mpr hpos.le) hpos.le,
    ← Complex.ofReal_mul, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one,
    Complex.one_cpow]

/-- **Applying the intrinsic duality twice returns the original**
(review #10): two applications of `duality`, with the prefactors
cancelling through `dual_prefactor_mul_one` (review #11 — the
prefactor content is now a named theorem, not a proof route). -/
theorem duality_dualDual :
    (↑(Q.dual.dual.toSectorAction.partFn) : ℂ)
      = ↑(Q.toSectorAction.partFn) := by
  rw [Q.dual.duality, Q.duality, ← mul_assoc, Q.dual_prefactor_mul_one,
    one_mul]

end QuadLatticeAction

/-- Notation for form-preserving equivalences of quadratic-lattice
actions (review #10). -/
scoped infixl:25 " ≃q " => QuadLatticeAction.Equiv

end Meno
