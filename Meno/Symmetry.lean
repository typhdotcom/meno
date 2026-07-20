import Meno.ResolutionCount
import Meno.GraphInstances

/-! # Symmetry: the no-go for symmetric descriptions

The symmetry face of the obstruction program. The generic
infrastructure is `IncidenceGraph.Auto` — a graph automorphism: vertex
and edge equivalences commuting with `src` and `tgt` — with its
pullback action on `R`-cochains (`Auto.cochainMap`), the commutation
with the gradient (`Auto.cochainMap_grad`), and the descended actions
on the description quotient (`Auto.h1Map`) and on the finite reduction
of the intrinsic carrier (`Auto.h1ReductionMap`).

On the cycle graph the rotation `cycleRot` (successor on vertices and
edges) acts transitively on edges — an invariant cochain is constant
(`cycleRot_invariant_eq_const`) — and trivially on classes
(`cycleRot_h1Map_int`, `cycleRot_h1ReductionMap`). The face's anchors:

* **The impossibility** (`cycle_no_invariant_representative`): at any
  resolution sharing a factor with `n`, the winding-one generator of
  `H¹(C_n; ZMod q)` has **no rotation-invariant representative** — an
  invariant cochain is constant, a constant's winding is `n·c`, and
  `1 ∈ n · ZMod q` exactly when `gcd n q = 1`.
* **The exact law** (`cycle_equivariant_section_iff`): a
  rotation-equivariant section of the resolution-`q` compression
  `carrierCompression` exists **iff** `gcd n q = 1`; the forward
  construction is the constant cochain scaled by `n⁻¹ mod q`.
* **The strictness witness** (`cycle_four_two_no_equivariant_section`,
  `cycle_four_two_no_invariant_representative`): at `(n, q) = (4, 2)`
  there is no equivariant section and no invariant representative.
* **The boundary witness** (`cycle_three_two_equivariant_section`):
  at `(n, q) = (3, 2)` the equivariant section exists.

The reading, stated as fact: descriptions exist and are priced;
a description respecting the system's own symmetry can fail to exist at
all; where it fails, every encoding breaks the symmetry — the choice of
bit is physical. -/

namespace Meno

open scoped BigOperators

universe u v

namespace IncidenceGraph

variable (G : IncidenceGraph.{u, v})

/-! ## Graph automorphisms and their actions -/

/-- **A graph automorphism**: vertex and edge equivalences commuting
with `src` and `tgt`. -/
structure Auto where
  /-- The vertex equivalence. -/
  vertexEquiv : G.V ≃ G.V
  /-- The edge equivalence. -/
  edgeEquiv : G.E ≃ G.E
  /-- Sources are respected. -/
  src_comm : ∀ e, G.src (edgeEquiv e) = vertexEquiv (G.src e)
  /-- Targets are respected. -/
  tgt_comm : ∀ e, G.tgt (edgeEquiv e) = vertexEquiv (G.tgt e)

/-- **The class of a resolution-`q` description**: the compression onto
the resolution quotient, as a linear map (the mod-`q` class map). -/
def h1ResClass (q : ℕ) :
    (G.E → ZMod q) →ₗ[ZMod q]
      ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) :=
  Submodule.mkQ _

namespace Auto

variable {G : IncidenceGraph.{u, v}} (φ : G.Auto)

/-- **The pullback action on `R`-cochains**: precomposition with the
edge equivalence, linear over any commutative ring. -/
def cochainMap (R : Type*) [CommRing R] : (G.E → R) →ₗ[R] (G.E → R) where
  toFun ω := fun e => ω (φ.edgeEquiv e)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem cochainMap_apply (R : Type*) [CommRing R]
    (ω : G.E → R) (e : G.E) :
    φ.cochainMap R ω e = ω (φ.edgeEquiv e) := rfl

/-- **Pullback commutes with the gradient**: the pullback of a
potential's gradient is the gradient of the pulled-back potential. -/
theorem cochainMap_grad (R : Type*) [CommRing R] (f : G.V → R) :
    φ.cochainMap R (G.grad f) = G.grad (fun v => f (φ.vertexEquiv v)) := by
  funext e
  show f (G.tgt (φ.edgeEquiv e)) - f (G.src (φ.edgeEquiv e))
    = f (φ.vertexEquiv (G.tgt e)) - f (φ.vertexEquiv (G.src e))
  rw [φ.tgt_comm, φ.src_comm]

/-- **The descended action on the description quotient**: gradients
pull back to gradients, so the pullback acts on `H¹(G; R)`. -/
noncomputable def h1Map (R : Type*) [CommRing R] :
    ((G.E → R) ⧸ LinearMap.range (G.gradLin R)) →ₗ[R]
      ((G.E → R) ⧸ LinearMap.range (G.gradLin R)) :=
  Submodule.mapQ _ _ (φ.cochainMap R) (by
    rintro ω ⟨f, rfl⟩
    exact Submodule.mem_comap.mpr
      ⟨fun v => f (φ.vertexEquiv v), (φ.cochainMap_grad R f).symm⟩)

/-- The descended action on representatives. -/
theorem h1Map_mk (R : Type*) [CommRing R] (ω : G.E → R) :
    φ.h1Map R (Submodule.Quotient.mk ω)
      = Submodule.Quotient.mk (φ.cochainMap R ω) := rfl

/-- **The descended action on the finite reduction of the intrinsic
carrier** `H¹(G;ℤ) ⧸ q·H¹(G;ℤ)`: the integral class action preserves
`q`-th multiples. -/
noncomputable def h1ReductionMap (q : ℕ) [NeZero q] :
    H1Reduction G q →ₗ[ℤ] H1Reduction G q :=
  Submodule.mapQ _ _ (φ.h1Map ℤ) (by
    rintro κ ⟨κ', rfl⟩
    refine Submodule.mem_comap.mpr ⟨φ.h1Map ℤ κ', ?_⟩
    show (q : ℤ) • φ.h1Map ℤ κ' = φ.h1Map ℤ ((q : ℤ) • κ')
    exact (map_smul (φ.h1Map ℤ) _ _).symm)

/-- The reduction action on representatives. -/
theorem h1ReductionMap_mk (q : ℕ) [NeZero q]
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)) :
    φ.h1ReductionMap q (Submodule.Quotient.mk κ)
      = Submodule.Quotient.mk (φ.h1Map ℤ κ) := rfl

end Auto

end IncidenceGraph

/-! ## The rotation of the cycle graph -/

/-- **The rotation automorphism of `C_n`**: successor on vertices and
edges. It acts transitively on edges (`cycleRot_invariant_eq_const`)
and trivially on classes (`cycleRot_h1Map_int`). -/
def cycleRot (n : ℕ) (hn : 0 < n) : (cycleGraph n hn).Auto :=
  haveI : NeZero n := ⟨hn.ne'⟩
  { vertexEquiv := Equiv.addRight (1 : Fin n)
    edgeEquiv := Equiv.addRight (1 : Fin n)
    src_comm := fun _ => rfl
    tgt_comm := fun _ => rfl }

/-- **Rotation-invariance forces constancy**: the rotation acts
transitively on the edges of `C_n`, so an invariant cochain takes one
value — over any commutative ring. -/
theorem cycleRot_invariant_eq_const {R : Type*} [CommRing R]
    (n : ℕ) (hn : 0 < n) [NeZero n] (ω : Fin n → R)
    (hω : (cycleRot n hn).cochainMap R ω = ω) :
    ω = fun _ => ω 0 := by
  have hsucc : ∀ e : Fin n, ω (e + 1) = ω e := fun e => congrFun hω e
  have hval : ∀ (m : ℕ) (hm : m < n), ω ⟨m, hm⟩ = ω 0 := by
    intro m
    induction m with
    | zero =>
      intro hm
      have h0 : (⟨0, hm⟩ : Fin n) = 0 := Fin.ext (by simp)
      rw [h0]
    | succ m ih =>
      intro hm
      have hm' : m < n := Nat.lt_of_succ_lt hm
      have hmk : (⟨m + 1, hm⟩ : Fin n) = ⟨m, hm'⟩ + 1 := by
        apply Fin.ext
        rw [Fin.val_add]
        have h1 : (1 : Fin n).val = 1 := by
          rw [Fin.val_one']
          exact Nat.mod_eq_of_lt (by omega)
        rw [h1]
        exact (Nat.mod_eq_of_lt hm).symm
      rw [hmk, hsucc ⟨m, hm'⟩]
      exact ih hm'
  funext e
  rw [show e = ⟨e.val, e.isLt⟩ from (Fin.eta e e.isLt).symm,
    hval e.val e.isLt]

/-- **The rotation acts trivially on integral classes**: precomposition
with the successor permutes the winding sum, so periods — hence
classes, by the ℤ-form keystone — are fixed. -/
theorem cycleRot_h1Map_int (n : ℕ) (hn : 0 < n)
    (κ : (Fin n → ℤ) ⧸ LinearMap.range ((cycleGraph n hn).gradLin ℤ)) :
    (cycleRot n hn).h1Map ℤ κ = κ := by
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨τ, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  rw [IncidenceGraph.Auto.h1Map_mk]
  apply ((cycleGraph n hn).latticeQuotEquiv (cycleLatticeBasis n hn)).injective
  funext j
  show (∑ e, τ (e + 1) * (cycleGraph n hn).cyclesZ (cycleLatticeBasis n hn) j e)
    = ∑ e, τ e * (cycleGraph n hn).cyclesZ (cycleLatticeBasis n hn) j e
  rw [cyclesZ_cycleLatticeBasis]
  show (∑ e, τ (e + 1) * 1) = ∑ e, τ e * 1
  simp only [mul_one]
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin n)) τ

/-- **The rotation acts trivially on the finite reduction** of the
intrinsic carrier — the descended fixed-point statement consumed by
the equivariant-section law. -/
theorem cycleRot_h1ReductionMap (n q : ℕ) (hn : 0 < n) [NeZero q]
    (ξ : IncidenceGraph.H1Reduction (cycleGraph n hn) q) :
    (cycleRot n hn).h1ReductionMap q ξ = ξ := by
  obtain ⟨κ, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rw [IncidenceGraph.Auto.h1ReductionMap_mk, cycleRot_h1Map_int]

/-! ## The winding coordinate and the generator class -/

/-- **The winding-one generator class** of `H¹(C_n; ZMod q)`: the
class of the single-edge indicator cochain. -/
def windingOneClass (n : ℕ) (hn : 0 < n) (q : ℕ) :
    (Fin n → ZMod q) ⧸ LinearMap.range ((cycleGraph n hn).gradLin (ZMod q)) :=
  haveI : NeZero n := ⟨hn.ne'⟩
  (cycleGraph n hn).h1ResClass q (Pi.single 0 1)

/-- **The keystone coordinate on `C_n` is the winding**: through the
all-ones lattice basis, the mod-`q` coordinate of a class is the sum
of any representative's edge values. -/
theorem cycle_latticeQuotEquivQ_mk (n q : ℕ) (hn : 0 < n) [NeZero q]
    (ω : Fin n → ZMod q) (j : Fin 1) :
    (cycleGraph n hn).latticeQuotEquivQ (cycleLatticeBasis n hn) q
      (Submodule.Quotient.mk ω) j = ∑ e, ω e := by
  show (∑ e, ω e * (cycleGraph n hn).cyclesQ (cycleLatticeBasis n hn) q j e)
    = ∑ e, ω e
  refine Finset.sum_congr rfl fun e _ => ?_
  have h1 : (cycleGraph n hn).cyclesQ (cycleLatticeBasis n hn) q j e = 1 := by
    show (((cycleGraph n hn).cyclesZ (cycleLatticeBasis n hn) j e : ℤ)
      : ZMod q) = 1
    rw [cyclesZ_cycleLatticeBasis]
    exact Int.cast_one
  rw [h1, mul_one]

/-! ## The impossibility: no symmetric description -/

/-- **THE SYMMETRY NO-GO** (the impossibility): at any resolution
sharing a factor with `n`, the winding-one generator class of
`H¹(C_n; ZMod q)` has **no rotation-invariant representative**.
Rotation-invariance on the transitive edge action forces a constant
cochain; a constant `c` has winding `n·c`; and `n·c = 1` in `ZMod q`
is invertibility of `n`, impossible when `1 < gcd n q`. Where the
symmetric description fails to exist, every encoding of the class
breaks the symmetry — the choice of bit is physical. -/
theorem cycle_no_invariant_representative (n q : ℕ) (hn : 0 < n)
    [NeZero q] (h : 1 < Nat.gcd n q) :
    ¬ ∃ ω : Fin n → ZMod q,
      (cycleRot n hn).cochainMap (ZMod q) ω = ω ∧
      (cycleGraph n hn).h1ResClass q ω = windingOneClass n hn q := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rintro ⟨ω, hinv, hclass⟩
  have hconst := cycleRot_invariant_eq_const n hn ω hinv
  have hclass' : (Submodule.Quotient.mk ω :
      (Fin n → ZMod q) ⧸ LinearMap.range ((cycleGraph n hn).gradLin (ZMod q)))
      = Submodule.Quotient.mk (Pi.single 0 1) := hclass
  have key : (n : ZMod q) * ω 0 = 1 := by
    calc (n : ZMod q) * ω 0
        = ∑ _e : Fin n, ω 0 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
      _ = ∑ e, ω e :=
          Finset.sum_congr rfl fun e _ => (congrFun hconst e).symm
      _ = (cycleGraph n hn).latticeQuotEquivQ (cycleLatticeBasis n hn) q
            (Submodule.Quotient.mk ω) 0 :=
          (cycle_latticeQuotEquivQ_mk n q hn ω 0).symm
      _ = (cycleGraph n hn).latticeQuotEquivQ (cycleLatticeBasis n hn) q
            (Submodule.Quotient.mk (Pi.single 0 1)) 0 := by rw [hclass']
      _ = ∑ e, Pi.single (0 : Fin n) (1 : ZMod q) e :=
          cycle_latticeQuotEquivQ_mk n q hn _ 0
      _ = 1 := Fintype.sum_pi_single' 0 1
  have hcop : Nat.Coprime n q :=
    (ZMod.isUnit_iff_coprime n q).mp (IsUnit.of_mul_eq_one (ω 0) key)
  have hone : Nat.gcd n q = 1 := hcop
  omega

/-! ## The exact law: equivariant sections exist exactly at coprimality -/

/-- **THE EQUIVARIANT-SECTION LAW** (the exact law): a
rotation-equivariant section of the resolution-`q` compression of
`C_n` exists **iff** `gcd n q = 1`. Forward: an equivariant section's
value at the generator's reduction is an invariant representative,
foreclosed by the no-go off coprimality. Backward: the constant
cochain scaled by `n⁻¹ mod q` realizes every class symmetrically. -/
theorem cycle_equivariant_section_iff (n q : ℕ) (hn : 0 < n) [NeZero q] :
    (∃ s : IncidenceGraph.H1Reduction (cycleGraph n hn) q →
        (Fin n → ZMod q),
      (∀ ξ, (cycleGraph n hn).carrierCompression q (s ξ) = ξ) ∧
      (∀ ξ, (cycleRot n hn).cochainMap (ZMod q) (s ξ)
        = s ((cycleRot n hn).h1ReductionMap q ξ)))
      ↔ Nat.gcd n q = 1 := by
  haveI : NeZero n := ⟨hn.ne'⟩
  constructor
  · rintro ⟨s, hsec, hequi⟩
    by_contra hne
    have hgcd : 1 < Nat.gcd n q := by
      have h0 : 0 < Nat.gcd n q := Nat.gcd_pos_of_pos_left q hn
      omega
    refine cycle_no_invariant_representative n q hn hgcd
      ⟨s ((cycleGraph n hn).carrierCompression q (Pi.single 0 1)), ?_, ?_⟩
    · rw [hequi, cycleRot_h1ReductionMap]
    · have h2 := hsec ((cycleGraph n hn).carrierCompression q (Pi.single 0 1))
      exact ((cycleGraph n hn).h1ResQuotEquivZMod q).symm.injective h2
  · intro hcop
    obtain ⟨v, hv⟩ := (ZMod.isUnit_iff_coprime n q).mpr hcop
    refine ⟨fun ξ => fun _ =>
      (↑v⁻¹ : ZMod q) * (cycleGraph n hn).latticeQuotEquivQ
        (cycleLatticeBasis n hn) q
        ((cycleGraph n hn).h1ResQuotEquivZMod q ξ) 0,
      fun ξ => ?_, fun ξ => ?_⟩
    · rw [(cycleGraph n hn).carrierCompression_apply q,
        LinearEquiv.symm_apply_eq]
      apply ((cycleGraph n hn).latticeQuotEquivQ
        (cycleLatticeBasis n hn) q).injective
      funext j
      rw [show j = 0 from Subsingleton.elim j 0]
      calc (cycleGraph n hn).latticeQuotEquivQ (cycleLatticeBasis n hn) q
            (Submodule.Quotient.mk (fun _ =>
              (↑v⁻¹ : ZMod q) * (cycleGraph n hn).latticeQuotEquivQ
                (cycleLatticeBasis n hn) q
                ((cycleGraph n hn).h1ResQuotEquivZMod q ξ) 0)) 0
          = ∑ _e : Fin n, (↑v⁻¹ : ZMod q)
              * (cycleGraph n hn).latticeQuotEquivQ
                (cycleLatticeBasis n hn) q
                ((cycleGraph n hn).h1ResQuotEquivZMod q ξ) 0 :=
            cycle_latticeQuotEquivQ_mk n q hn _ 0
        _ = (n : ZMod q) * ((↑v⁻¹ : ZMod q)
              * (cycleGraph n hn).latticeQuotEquivQ
                (cycleLatticeBasis n hn) q
                ((cycleGraph n hn).h1ResQuotEquivZMod q ξ) 0) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
        _ = ((n : ZMod q) * (↑v⁻¹ : ZMod q))
              * (cycleGraph n hn).latticeQuotEquivQ
                (cycleLatticeBasis n hn) q
                ((cycleGraph n hn).h1ResQuotEquivZMod q ξ) 0 :=
            (mul_assoc _ _ _).symm
        _ = (cycleGraph n hn).latticeQuotEquivQ (cycleLatticeBasis n hn) q
              ((cycleGraph n hn).h1ResQuotEquivZMod q ξ) 0 := by
            rw [← hv, Units.mul_inv, one_mul]
    · rw [cycleRot_h1ReductionMap]
      rfl

/-! ## The witnesses -/

/-- **The strictness witness, representative form**: at
`(n, q) = (4, 2)` the generator class has no rotation-invariant
representative — `gcd 4 2 = 2`. -/
theorem cycle_four_two_no_invariant_representative :
    ¬ ∃ ω : Fin 4 → ZMod 2,
      (cycleRot 4 (by norm_num)).cochainMap (ZMod 2) ω = ω ∧
      (cycleGraph 4 (by norm_num)).h1ResClass 2 ω
        = windingOneClass 4 (by norm_num) 2 :=
  cycle_no_invariant_representative 4 2 (by norm_num) (by decide)

/-- **The strictness witness, section form**: at `(n, q) = (4, 2)`
there is no rotation-equivariant section of the compression. -/
theorem cycle_four_two_no_equivariant_section :
    ¬ ∃ s : IncidenceGraph.H1Reduction (cycleGraph 4 (by norm_num)) 2 →
        (Fin 4 → ZMod 2),
      (∀ ξ, (cycleGraph 4 (by norm_num)).carrierCompression 2 (s ξ) = ξ) ∧
      (∀ ξ, (cycleRot 4 (by norm_num)).cochainMap (ZMod 2) (s ξ)
        = s ((cycleRot 4 (by norm_num)).h1ReductionMap 2 ξ)) := fun hs => by
  have h := (cycle_equivariant_section_iff 4 2 (by norm_num)).mp hs
  exact absurd h (by decide)

/-- **The boundary witness**: at `(n, q) = (3, 2)` the
rotation-equivariant section exists — `gcd 3 2 = 1`, and the section
is the constant cochain scaled by `3⁻¹ = 1 mod 2`. -/
theorem cycle_three_two_equivariant_section :
    ∃ s : IncidenceGraph.H1Reduction (cycleGraph 3 (by norm_num)) 2 →
        (Fin 3 → ZMod 2),
      (∀ ξ, (cycleGraph 3 (by norm_num)).carrierCompression 2 (s ξ) = ξ) ∧
      (∀ ξ, (cycleRot 3 (by norm_num)).cochainMap (ZMod 2) (s ξ)
        = s ((cycleRot 3 (by norm_num)).h1ReductionMap 2 ξ)) :=
  (cycle_equivariant_section_iff 3 2 (by norm_num)).mpr (by decide)

end Meno
