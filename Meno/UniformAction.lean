import Meno.SectorAction
import Meno.Basic

/-! # The Uniform Sector Action: type-level gravity, realized (C9)

**TypeKernel's valid replacement.** The falsified Phase-10 design put
energies on endofunctions (`E(id) = log|A|` contradicted
`energy_id`; endofunction sums broke summability). The correct
realization is simpler: a finite nonempty type is a sector lattice
with **zero energy everywhere** — every state equally costly to
name — so its partition function *is* its cardinality and its
complexity *is* `log |A|` (`uniformAction_partFn`,
`uniformAction_complexity`). The log-cardinality complexity of
`Basic.lean` was a sector action all along.

On this realization the type-level gravity of `Basic.lean` becomes an
identity of partition functions:

* `gravity_partFn` — for uniform fibers,
  `Z(A ×_D B) · Z(D) = Z(A) · Z(B)`: the pullback shares one copy of
  the base.
* `gravity_complexity` — its log:
  `K(A ×_D B) + K(D) = K(A) + K(B)` — exactly the shape of the
  abstract `SGD.gravity`, now with real numbers computed from a
  `SectorAction`.
* `gravity_uniform_complexity` — the product-projection corollary:
  the numeric shadow of `SGD.gravity_uniform`.
* `uniform_refactoring_bound` — the refactoring bound over the
  uniform action: `K(A ×_D B) ≤ K(D) + log(max_d |fiber product|)`,
  the concrete form of `SGD.refactoring_bound`'s
  `C(pullback) ≤ C(base) + sup(fiber costs)`.

Product additivity needs no new work: `SectorAction.prod` (Phase 1)
already multiplies partition functions, and
`uniformAction_prod_partFn` checks the uniform action agrees. -/

namespace Meno

open scoped BigOperators

universe u

/-- **The uniform sector action** of a finite nonempty type: every
element a sector, every sector free. The Boltzmann sum then simply
counts. -/
noncomputable def uniformAction (A : Type u) [Fintype A] [Nonempty A] :
    SectorAction where
  Λ := A
  E := fun _ => 0
  E_zero := ⟨Classical.arbitrary A, rfl⟩
  E_nonneg := fun _ => le_refl 0
  summable := (hasSum_fintype _).summable

/-- The uniform partition function is the cardinality. -/
theorem uniformAction_partFn (A : Type u) [Fintype A] [Nonempty A] :
    (uniformAction A).partFn = Fintype.card A := by
  show ∑' _ : A, Real.exp (-(0 : ℝ)) = (Fintype.card A : ℝ)
  rw [tsum_fintype]
  simp

/-- The uniform complexity is the log-cardinality — `Basic.lean`'s
complexity measure, realized as a sector action. -/
theorem uniformAction_complexity (A : Type u) [Fintype A] [Nonempty A] :
    (uniformAction A).complexity = Real.log (Fintype.card A) := by
  show Real.log (uniformAction A).partFn = _
  rw [uniformAction_partFn]

/-- The uniform action is multiplicative on products — agreeing with
`SectorAction.prod`'s partition function. -/
theorem uniformAction_prod_partFn (A B : Type u)
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] :
    (uniformAction (A × B)).partFn
      = (uniformAction A).partFn * (uniformAction B).partFn := by
  rw [uniformAction_partFn, uniformAction_partFn, uniformAction_partFn,
    Fintype.card_prod, Nat.cast_mul]

/-! ## Gravity -/

/-- The pullback of finite types is finite (seen through the
definition, which instance search cannot unfold on its own). -/
instance pullbackFintype {A B D : Type u} [Fintype A] [Fintype B]
    [DecidableEq D] {f : A → D} {g : B → D} :
    Fintype (SGD.Pullback f g) :=
  inferInstanceAs (Fintype {p : A × B // f p.1 = g p.2})

/-- A pullback with nonempty base and uniform nonempty fibers is
nonempty. -/
theorem pullback_nonempty {A B D F G : Type u} (f : A → D) (g : B → D)
    (ef : ∀ d, SGD.Fiber f d ≃ F) (eg : ∀ d, SGD.Fiber g d ≃ G)
    [Nonempty D] [Nonempty F] [Nonempty G] :
    Nonempty (SGD.Pullback f g) := by
  obtain ⟨d⟩ := ‹Nonempty D›
  obtain ⟨x⟩ := ‹Nonempty F›
  obtain ⟨y⟩ := ‹Nonempty G›
  exact ⟨(SGD.Pullback.equivSigmaFiber f g).symm
    ⟨d, (ef d).symm x, (eg d).symm y⟩⟩

/-- **The cardinality identity behind gravity**: for uniform fibers,
`|A ×_D B| · |D| = |A| · |B|`. -/
theorem card_pullback_mul_card_base {A B D F G : Type u}
    [Fintype A] [Fintype B] [Fintype D] [Fintype F] [Fintype G]
    [DecidableEq D]
    (f : A → D) (g : B → D)
    (ef : ∀ d, SGD.Fiber f d ≃ F) (eg : ∀ d, SGD.Fiber g d ≃ G) :
    Fintype.card (SGD.Pullback f g) * Fintype.card D
      = Fintype.card A * Fintype.card B := by
  have hA : Fintype.card A = Fintype.card D * Fintype.card F := by
    rw [Fintype.card_congr ((Equiv.sigmaFiberEquiv f).symm.trans
      ((Equiv.sigmaCongrRight ef).trans (Equiv.sigmaEquivProd D F))),
      Fintype.card_prod]
  have hB : Fintype.card B = Fintype.card D * Fintype.card G := by
    rw [Fintype.card_congr ((Equiv.sigmaFiberEquiv g).symm.trans
      ((Equiv.sigmaCongrRight eg).trans (Equiv.sigmaEquivProd D G))),
      Fintype.card_prod]
  have hP : Fintype.card (SGD.Pullback f g)
      = Fintype.card D * (Fintype.card F * Fintype.card G) := by
    rw [Fintype.card_congr ((SGD.Pullback.equivSigmaFiber f g).trans
      ((Equiv.sigmaCongrRight
        (fun d => Equiv.prodCongr (ef d) (eg d))).trans
        (Equiv.sigmaEquivProd D (F × G)))),
      Fintype.card_prod, Fintype.card_prod]
  rw [hA, hB, hP]
  ring

/-- **GRAVITY AS A PARTITION-FUNCTION IDENTITY** (C9): with uniform
fibers, the pullback and the base together weigh exactly what the two
factors weigh — `Z(A ×_D B) · Z(D) = Z(A) · Z(B)`. Sharing the base
is worth precisely one copy of `Z(D)`. -/
theorem gravity_partFn {A B D F G : Type u}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [Fintype D] [Nonempty D] [Fintype F] [Fintype G] [DecidableEq D]
    (f : A → D) (g : B → D)
    (ef : ∀ d, SGD.Fiber f d ≃ F) (eg : ∀ d, SGD.Fiber g d ≃ G)
    [Nonempty (SGD.Pullback f g)] :
    (uniformAction (SGD.Pullback f g)).partFn * (uniformAction D).partFn
      = (uniformAction A).partFn * (uniformAction B).partFn := by
  rw [uniformAction_partFn, uniformAction_partFn, uniformAction_partFn,
    uniformAction_partFn, ← Nat.cast_mul, ← Nat.cast_mul,
    card_pullback_mul_card_base f g ef eg]

/-- **Gravity in complexity form** (C9): `K(A ×_D B) + K(D) =
K(A) + K(B)` — the exact shape of the abstract `SGD.gravity`, with
the complexities now computed numbers. The saving from sharing a base
is exactly `K(D)`. -/
theorem gravity_complexity {A B D F G : Type u}
    [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [Fintype D] [Nonempty D] [Fintype F] [Fintype G] [DecidableEq D]
    (f : A → D) (g : B → D)
    (ef : ∀ d, SGD.Fiber f d ≃ F) (eg : ∀ d, SGD.Fiber g d ≃ G)
    [Nonempty (SGD.Pullback f g)] :
    (uniformAction (SGD.Pullback f g)).complexity
        + (uniformAction D).complexity
      = (uniformAction A).complexity + (uniformAction B).complexity := by
  have h := gravity_partFn f g ef eg
  have hP := (uniformAction (SGD.Pullback f g)).partFn_pos
  have hD := (uniformAction D).partFn_pos
  have hA := (uniformAction A).partFn_pos
  have hB := (uniformAction B).partFn_pos
  have hlog := congrArg Real.log h
  rw [Real.log_mul hP.ne' hD.ne', Real.log_mul hA.ne' hB.ne'] at hlog
  exact hlog

instance {D F G : Type u} [Nonempty D] [Nonempty F] [Nonempty G] :
    Nonempty (SGD.Pullback (fun p : D × F => p.1) (fun p : D × G => p.1)) :=
  pullback_nonempty _ _ (SGD.fstFiberEquiv D F) (SGD.fstFiberEquiv D G)

/-- The product-projection corollary: the numeric shadow of
`SGD.gravity_uniform`. -/
theorem gravity_uniform_complexity (D F G : Type u)
    [Fintype D] [Nonempty D] [Fintype F] [Nonempty F]
    [Fintype G] [Nonempty G] [DecidableEq D] :
    (uniformAction (SGD.Pullback
          (fun p : D × F => p.1) (fun p : D × G => p.1))).complexity
        + (uniformAction D).complexity
      = (uniformAction (D × F)).complexity
        + (uniformAction (D × G)).complexity :=
  gravity_complexity _ _ (SGD.fstFiberEquiv D F) (SGD.fstFiberEquiv D G)

/-! ## The refactoring bound, uniformly -/

/-- The pullback's cardinality is the sum of the fiber products'. -/
theorem card_pullback_eq_sum {A B D : Type u}
    [Fintype A] [Fintype B] [Fintype D] [DecidableEq D]
    (f : A → D) (g : B → D) :
    Fintype.card (SGD.Pullback f g)
      = ∑ d, Fintype.card (SGD.FiberProd f g d) := by
  rw [Fintype.card_congr (SGD.Pullback.equivSigmaFiber f g),
    Fintype.card_sigma]

/-- **The refactoring bound over the uniform action** (C9's concrete
form of `SGD.refactoring_bound`): the pullback's complexity is at
most the base's plus the log of the largest paired fiber. -/
theorem uniform_refactoring_bound {A B D : Type u}
    [Fintype A] [Fintype B] [Fintype D] [DecidableEq D] [Nonempty D]
    (f : A → D) (g : B → D) [Nonempty (SGD.Pullback f g)] :
    (uniformAction (SGD.Pullback f g)).complexity
      ≤ (uniformAction D).complexity
        + Real.log
            ((Finset.univ.sup fun d =>
              Fintype.card (SGD.FiberProd f g d) : ℕ)) := by
  rw [uniformAction_complexity, uniformAction_complexity]
  set m : ℕ := Finset.univ.sup fun d => Fintype.card (SGD.FiberProd f g d)
    with hm
  have hcard : Fintype.card (SGD.Pullback f g) ≤ Fintype.card D * m := by
    rw [card_pullback_eq_sum]
    calc ∑ d, Fintype.card (SGD.FiberProd f g d)
        ≤ ∑ _d : D, m :=
          Finset.sum_le_sum fun d _ => by
            rw [hm]
            exact Finset.le_sup
              (f := fun d' => Fintype.card (SGD.FiberProd f g d'))
              (Finset.mem_univ d)
      _ = Fintype.card D * m := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hPpos : 0 < Fintype.card (SGD.Pullback f g) := Fintype.card_pos
  have hmpos : 0 < m := by
    by_contra hm0
    have : m = 0 := by omega
    rw [this, mul_zero] at hcard
    omega
  have hDpos : 0 < Fintype.card D := Fintype.card_pos
  calc Real.log (Fintype.card (SGD.Pullback f g))
      ≤ Real.log ((Fintype.card D * m : ℕ)) := by
        apply Real.log_le_log (by exact_mod_cast hPpos)
        exact_mod_cast hcard
    _ = Real.log (Fintype.card D) + Real.log m := by
        rw [Nat.cast_mul,
          Real.log_mul (by exact_mod_cast hDpos.ne') (by exact_mod_cast hmpos.ne')]

end Meno
