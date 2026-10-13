import Meno.Closure
import Meno.Binding
import Mathlib.InformationTheory.Hamming

/-! # Decoding: the exact distance law for closed corrected steps

On a graph every cochain is a cocycle, so an error on one edge of a
cycle changes the class (`cycle_edgeNoise_not_closed`). Attaching
faces adds a constraint: a `TwoComplex` has a **syndrome** — the
periods around its faces — and its cocycles are the cochains of zero
syndrome. A **decoder** maps each syndrome to a cochain carrying it;
the **corrected step** adds an error `s` and subtracts the decoder's
answer, leaving the **residual** `s − D(σ s)`, a cocycle.

* **The closure law** (`Decoder.corrected_closed_iff`): the corrected
  step on cocycles is closed on classes iff every residual is exact.
* **THE DISTANCE LAW** (`decodable_iff`): some decoder makes the
  corrected step closed under every error of Hamming weight `≤ t`
  **iff** every non-exact cocycle has weight `> 2t`. Achievability
  is the minimum-weight decoder (`minWeightDecoder`); the converse
  splits a light non-exact cocycle into two errors of equal syndrome
  (`Decoder.exists_residual_not_exact`).
* **The impossibility** (`cycle_not_decodable`): on `C_n` with no
  faces, at resolution `q > 1`, no decoder corrects a single error. -/

namespace Meno

open scoped BigOperators
open Matrix

universe u

variable {G : IncidenceGraph.{u}}

/-- **Stokes against a cast cycle**: gradients pair to zero with the
cast of any integral cycle, over any commutative ring. -/
theorem grad_dotProduct_castCycle {R : Type*} [CommRing R] (f : G.V → R)
    {c : G.E → ℤ} (hc : c ∈ G.cycleLattice) :
    G.grad f ⬝ᵥ (fun e => (c e : R)) = 0 := by
  rw [G.grad_dotProduct_eq]
  refine Finset.sum_eq_zero fun v _ => ?_
  have h := G.boundary_ringHom (Int.castRingHom R) c v
  rw [(G.mem_cycleLattice.mp hc) v, map_zero] at h
  rw [show (fun e => (c e : R)) = fun e => Int.castRingHom R (c e) from rfl,
    ← h, mul_zero]

/-- Hamming weight is subadditive under subtraction. -/
theorem hammingNorm_sub_le {ι : Type*} [Fintype ι] {R : Type*} [AddCommGroup R]
    [DecidableEq R] (a b : ι → R) :
    hammingNorm (a - b) ≤ hammingNorm a + hammingNorm b := by
  rw [← neg_add_eq_sub, ← hammingDist_eq_hammingNorm, add_comm,
    ← hammingDist_zero_right b, ← hammingDist_zero_left]
  exact hammingDist_triangle b 0 a

namespace TwoComplex

variable (X : TwoComplex.{u} G) (R : Type*) [CommRing R]

/-- **The syndrome**: the periods of a cochain around every attached
face. -/
def syndrome : (G.E → R) →ₗ[R] (X.Faces → R) where
  toFun ω i := ω ⬝ᵥ (fun e => (X.face i e : R))
  map_add' ω η := funext fun _ => add_dotProduct ω η _
  map_smul' a ω := funext fun _ => smul_dotProduct a ω _

/-- **The `R`-cocycles**: cochains of zero syndrome. -/
def cocyclesR : Submodule R (G.E → R) := LinearMap.ker (X.syndrome R)

/-- Gradients are cocycles. -/
theorem range_grad_le_cocyclesR :
    LinearMap.range (G.gradLin R) ≤ X.cocyclesR R := by
  rintro _ ⟨f, rfl⟩
  exact LinearMap.mem_ker.mpr
    (funext fun i => grad_dotProduct_castCycle f (X.face_mem i))

/-- The exact cocycles, as a submodule of the cocycles: the quotient
is `H¹` of the complex at coefficients `R`. -/
abbrev exactR : Submodule R (X.cocyclesR R) :=
  (LinearMap.range (G.gradLin R)).comap (X.cocyclesR R).subtype

/-- **A decoder**: a cochain carrying each attained syndrome, silent
on the zero syndrome. -/
structure Decoder where
  /-- The correction for a syndrome. -/
  decode : (X.Faces → R) → (G.E → R)
  /-- The correction carries the syndrome it answers. -/
  syndrome_decode : ∀ c, X.syndrome R (decode (X.syndrome R c)) = X.syndrome R c
  /-- No syndrome, no correction. -/
  decode_zero : decode 0 = 0

namespace Decoder

variable {X R} (D : X.Decoder R)

/-- **The residual** of an error: what remains after correction. -/
def residual (s : G.E → R) : G.E → R := s - D.decode (X.syndrome R s)

theorem residual_mem (s : G.E → R) : D.residual s ∈ X.cocyclesR R := by
  show X.syndrome R (s - D.decode (X.syndrome R s)) = 0
  rw [map_sub, D.syndrome_decode, sub_self]

theorem residual_zero : D.residual 0 = 0 := by
  simp [residual, D.decode_zero]

/-- The residuals of an error set, as cocycles: the error set of the
corrected step. -/
def residualSet (S : Set (G.E → R)) : Set (X.cocyclesR R) :=
  {z | ∃ s ∈ S, (z : G.E → R) = D.residual s}

/-- **THE CLOSURE LAW**: the corrected step on cocycles is closed on
classes iff every residual is exact. -/
theorem corrected_closed_iff (S : Set (G.E → R)) (h0 : (0 : G.E → R) ∈ S) :
    StepClosed (noisyStep (LinearMap.id (R := R)) (D.residualSet S))
      (X.exactR R).mkQ (X.exactR R).mkQ ↔
      ∀ s ∈ S, D.residual s ∈ LinearMap.range (G.gradLin R) := by
  rw [noisyStep_closed_iff _ _ _ _ (show (0 : X.cocyclesR R) ∈ D.residualSet S from
    ⟨0, h0, by rw [D.residual_zero]; rfl⟩)]
  constructor
  · rintro ⟨-, h⟩ s hs
    exact @h ⟨_, D.residual_mem s⟩ ⟨s, hs, rfl⟩
  · intro h
    refine ⟨fun _ h' => h', ?_⟩
    rintro z ⟨s, hs, hz⟩
    show (z : G.E → R) ∈ LinearMap.range (G.gradLin R)
    rw [hz]
    exact h s hs

variable [DecidableEq R]

/-- **The converse bound**: a non-exact cocycle of weight `≤ 2t`
defeats every decoder at weight `t` — split it into two errors of
weight `≤ t` with one syndrome; the decoder answers both alike, so
their residuals differ by the cocycle and cannot both be exact. -/
theorem exists_residual_not_exact (t : ℕ) {c : G.E → R}
    (hc : c ∈ X.cocyclesR R) (hne : c ∉ LinearMap.range (G.gradLin R))
    (hw : hammingNorm c ≤ 2 * t) :
    ∃ s, hammingNorm s ≤ t ∧ D.residual s ∉ LinearMap.range (G.gradLin R) := by
  classical
  set A := Finset.univ.filter fun e => c e ≠ 0 with hA
  have hcA : hammingNorm c = A.card := rfl
  obtain ⟨A₁, hA₁, hcard⟩ :=
    Finset.exists_subset_card_eq (show min t A.card ≤ A.card from min_le_right _ _)
  set s₁ : G.E → R := fun e => if e ∈ A₁ then c e else 0 with hs₁
  set s₂ : G.E → R := s₁ - c with hs₂
  have h₁ : hammingNorm s₁ ≤ t := by
    have : hammingNorm s₁ ≤ A₁.card := by
      refine Finset.card_le_card fun e he => ?_
      by_contra hn
      simp [s₁, hn] at he
    omega
  have h₂ : hammingNorm s₂ ≤ t := by
    have hsub : hammingNorm s₂ ≤ (A \ A₁).card := by
      refine Finset.card_le_card fun e he => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, s₂, s₁,
        Pi.sub_apply] at he
      rw [Finset.mem_sdiff]
      by_cases h : e ∈ A₁
      · simp [h] at he
      · simp only [h, if_false, zero_sub, ne_eq, neg_eq_zero] at he
        exact ⟨by simp [hA, he], h⟩
    have := Finset.card_sdiff_add_card_eq_card hA₁
    omega
  have hσ : X.syndrome R s₂ = X.syndrome R s₁ := by
    rw [hs₂, map_sub, LinearMap.mem_ker.mp hc, sub_zero]
  by_contra hall
  push Not at hall
  apply hne
  have e : c = D.residual s₁ - D.residual s₂ := by
    unfold residual
    rw [hσ, hs₂]
    abel
  rw [e]
  exact sub_mem (hall _ h₁) (hall _ h₂)

end Decoder

variable [DecidableEq R]

open Classical in
/-- **The minimum-weight decoder**: each attained syndrome is answered
by a lightest cochain carrying it. -/
noncomputable def minWeightDecoder : X.Decoder R where
  decode τ := if h : ∃ c, X.syndrome R c = τ then
      (InvImage.wf hammingNorm wellFounded_lt).min {c | X.syndrome R c = τ} h
    else 0
  syndrome_decode c := by
    rw [dif_pos ⟨c, rfl⟩]
    exact WellFounded.min_mem _ {c' | X.syndrome R c' = X.syndrome R c} _
  decode_zero := by
    rw [dif_pos ⟨0, map_zero _⟩]
    have h := WellFounded.not_lt_min (InvImage.wf hammingNorm wellFounded_lt)
      {c | X.syndrome R c = 0} (x := 0) (map_zero _)
    simp only [InvImage, hammingNorm_zero, not_lt, Nat.le_zero,
      hammingNorm_eq_zero] at h
    exact h

/-- The minimum-weight decoder answers no heavier than any error
carrying the same syndrome. -/
theorem minWeightDecoder_le (s : G.E → R) :
    hammingNorm ((X.minWeightDecoder R).decode (X.syndrome R s))
      ≤ hammingNorm s := by
  simp only [minWeightDecoder]
  rw [dif_pos ⟨s, rfl⟩]
  exact not_lt.mp (WellFounded.not_lt_min (InvImage.wf hammingNorm wellFounded_lt)
    {c | X.syndrome R c = X.syndrome R s} (x := s) rfl)

/-- **Achievability**: when every non-exact cocycle weighs more than
`2t`, the minimum-weight decoder leaves an exact residual for every
error of weight `≤ t` — the residual weighs at most `2t`. -/
theorem minWeightDecoder_residual_exact (t : ℕ)
    (hd : ∀ c ∈ X.cocyclesR R, c ∉ LinearMap.range (G.gradLin R) →
      2 * t < hammingNorm c)
    {s : G.E → R} (hs : hammingNorm s ≤ t) :
    (X.minWeightDecoder R).residual s ∈ LinearMap.range (G.gradLin R) := by
  by_contra hne
  have h1 := hd _ ((X.minWeightDecoder R).residual_mem s) hne
  have h2 := hammingNorm_sub_le s ((X.minWeightDecoder R).decode (X.syndrome R s))
  have h3 := X.minWeightDecoder_le R s
  simp only [Decoder.residual] at h1
  omega

/-- **THE DISTANCE LAW**: some decoder makes the corrected step closed
on classes under every error of weight `≤ t` iff every non-exact
cocycle weighs more than `2t`. -/
theorem decodable_iff (t : ℕ) :
    (∃ D : X.Decoder R,
      StepClosed (noisyStep (LinearMap.id (R := R)) (D.residualSet {s | hammingNorm s ≤ t}))
        (X.exactR R).mkQ (X.exactR R).mkQ) ↔
      ∀ c ∈ X.cocyclesR R, c ∉ LinearMap.range (G.gradLin R) →
        2 * t < hammingNorm c := by
  have h0 : (0 : G.E → R) ∈ {s : G.E → R | hammingNorm s ≤ t} := by
    simp [hammingNorm_zero]
  constructor
  · rintro ⟨D, hD⟩ c hc hne
    by_contra hle
    push Not at hle
    obtain ⟨s, hs, hres⟩ := D.exists_residual_not_exact t hc hne hle
    exact hres ((D.corrected_closed_iff _ h0).mp hD s hs)
  · intro hd
    exact ⟨X.minWeightDecoder R, ((X.minWeightDecoder R).corrected_closed_iff _ h0).mpr
      fun s hs => X.minWeightDecoder_residual_exact R t hd hs⟩

end TwoComplex

/-! ## The impossibility: a graph corrects nothing -/

/-- A graph as a 2-complex with no faces. -/
def bareComplex (G : IncidenceGraph.{u}) : TwoComplex G :=
  { Faces := PEmpty
    face := fun i => i.elim
    face_mem := fun i => i.elim }

/-- **THE IMPOSSIBILITY**: on `C_n` with no faces, at resolution
`q > 1`, no decoder corrects a single error — an edge indicator is a
non-exact cocycle of weight one. -/
theorem cycle_not_decodable (n q : ℕ) (hn : 0 < n) [NeZero q] (hq : 1 < q)
    (e : Fin n) :
    ¬ ∃ D : (bareComplex (cycleGraph n hn)).Decoder (ZMod q),
      StepClosed (noisyStep (LinearMap.id (R := ZMod q)) (D.residualSet {s | hammingNorm s ≤ 1}))
        ((bareComplex (cycleGraph n hn)).exactR (ZMod q)).mkQ
        ((bareComplex (cycleGraph n hn)).exactR (ZMod q)).mkQ := by
  have : Fact (1 < q) := ⟨hq⟩
  rw [TwoComplex.decodable_iff]
  intro h
  have hw : hammingNorm (Pi.single e (1 : ZMod q) : Fin n → ZMod q) = 1 := by
    rw [hammingNorm, Finset.card_eq_one]
    exact ⟨e, by ext x; by_cases hx : x = e <;> simp [hx, Pi.single_apply]⟩
  have := h (Pi.single e 1) (LinearMap.mem_ker.mpr (funext fun i => i.elim))
    (cycle_single_not_exact n q hn hq e)
  omega

/-! ## The cylinder: distance three -/

/-- An error of weight `≤ 2` is supported on two coordinates. -/
theorem exists_pair_of_hammingNorm_le_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {R : Type*} [AddMonoid R] [DecidableEq R] (c : ι → R)
    (hc : hammingNorm c ≤ 2) :
    ∃ a b : ι, ∃ x y : R, c = Pi.single a x + Pi.single b y := by
  set s := Finset.univ.filter fun e => c e ≠ 0 with hs
  have hcard : s.card ≤ 2 := hc
  have hz : ∀ e, e ∉ s → c e = 0 := fun e he => by simpa [hs] using he
  rcases (by omega : s.card = 0 ∨ s.card = 1 ∨ s.card = 2) with h | h | h
  · refine ⟨Classical.arbitrary ι, Classical.arbitrary ι, 0, 0, funext fun e => ?_⟩
    simp [hz e (by simp [Finset.card_eq_zero.mp h])]
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
    refine ⟨a, a, c a, 0, funext fun e => ?_⟩
    by_cases hea : e = a
    · simp [hea]
    · simp [hea, hz e (by simp [ha, hea])]
  · obtain ⟨a, b, hab, hab'⟩ := Finset.card_eq_two.mp h
    refine ⟨a, b, c a, c b, funext fun e => ?_⟩
    by_cases hea : e = a
    · simp [hea, hab]
    · by_cases heb : e = b
      · simp [heb, Ne.symm hab]
      · simp [hea, heb, hz e (by simp [hab', hea, heb])]

/-- Edge sources of the cylinder `C₃ × P₃`: ring edges `3j + k` run
`(j,k) → (j,k+1)`, rung edges `9 + 3j + k` run `(j,k) → (j+1,k)`;
vertex `(j,k)` is `3j + k`. -/
def cylSrc : Fin 15 → Fin 9 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 1, 2, 3, 4, 5]

/-- Edge targets of the cylinder. -/
def cylTgt : Fin 15 → Fin 9 := ![1, 2, 0, 4, 5, 3, 7, 8, 6, 3, 4, 5, 6, 7, 8]

/-- The cylinder `C₃ × P₃` as an incidence graph. -/
@[reducible] def cylinderGraph : IncidenceGraph :=
  { V := Fin 9
    E := Fin 15
    src := cylSrc
    tgt := cylTgt }

/-- The square face `(j,k)`, `j < 2`: ring `(j,k)`, rung `(j,k+1)`,
ring `(j+1,k)` reversed, rung `(j,k)` reversed. -/
def cylFace (f : Fin 6) (e : Fin 15) : ℤ :=
  (if e.val = 3 * (f.val / 3) + f.val % 3 then 1 else 0)
    + (if e.val = 9 + 3 * (f.val / 3) + (f.val % 3 + 1) % 3 then 1 else 0)
    - (if e.val = 3 * (f.val / 3 + 1) + f.val % 3 then 1 else 0)
    - (if e.val = 9 + 3 * (f.val / 3) + f.val % 3 then 1 else 0)

/-- The cylinder with its six squares filled. -/
def cylinderComplex : TwoComplex cylinderGraph :=
  { Faces := Fin 6
    face := cylFace
    face_mem := fun i => cylinderGraph.mem_cycleLattice.mpr (by
      revert i
      decide) }

instance : Fintype cylinderComplex.Faces := inferInstanceAs (Fintype (Fin 6))

/-- **No light cocycle on the cylinder**: over `ZMod 2`, an error
supported on two edges with zero syndrome is zero. -/
theorem cylinder_pair_cocycle : ∀ a b : Fin 15, ∀ x y : ZMod 2,
    (∀ i : Fin 6,
      (Pi.single a x + Pi.single b y : Fin 15 → ZMod 2) ⬝ᵥ (fun e => (cylFace i e : ZMod 2)) = 0) →
      (Pi.single a x + Pi.single b y : Fin 15 → ZMod 2) = 0 := by
  decide +kernel

/-- Every nonzero `ZMod 2`-cocycle of the cylinder weighs at least `3`. -/
theorem cylinder_cocycle_weight (c : Fin 15 → ZMod 2)
    (hc : c ∈ cylinderComplex.cocyclesR (ZMod 2)) (hne : c ≠ 0) :
    3 ≤ hammingNorm c := by
  by_contra hlt
  obtain ⟨a, b, x, y, rfl⟩ := exists_pair_of_hammingNorm_le_two c (by omega)
  refine hne (cylinder_pair_cocycle a b x y fun i => ?_)
  exact congrFun (LinearMap.mem_ker.mp hc) i

/-- **The strictness witness**: on the cylinder over `ZMod 2`, the
minimum-weight decoder corrects every single error. -/
theorem cylinder_decodable_one :
    ∃ D : cylinderComplex.Decoder (ZMod 2),
      StepClosed (noisyStep (LinearMap.id (R := ZMod 2))
          (D.residualSet {s | hammingNorm s ≤ 1}))
        (cylinderComplex.exactR (ZMod 2)).mkQ
        (cylinderComplex.exactR (ZMod 2)).mkQ := by
  refine (TwoComplex.decodable_iff _ _ 1).mpr fun c hc hne => ?_
  have : c ≠ 0 := by
    rintro rfl
    exact hne (Submodule.zero_mem _)
  have := cylinder_cocycle_weight c hc this
  omega

/-- The radial cut: one ring edge at angle `0` on each ring. -/
def cylCut : Fin 15 → ZMod 2 := fun e => if e.val % 3 = 0 ∧ e.val < 9 then 1 else 0

/-- The inner ring, an integral cycle. -/
def cylRing : Fin 15 → ℤ := fun e => if e.val < 3 then 1 else 0

/-- The radial cut is a `ZMod 2`-cocycle of the cylinder. -/
theorem cylCut_mem_cocycles : cylCut ∈ cylinderComplex.cocyclesR (ZMod 2) := by
  have hcut : ∀ i : Fin 6, cylCut ⬝ᵥ (fun e => (cylFace i e : ZMod 2)) = 0 := by
    decide
  exact LinearMap.mem_ker.mpr (funext fun i => hcut i)

/-- The radial cut is not exact: it pairs to `1` with the inner ring. -/
theorem cylCut_not_exact :
    cylCut ∉ LinearMap.range (cylinderGraph.gradLin (ZMod 2)) := by
  have hring : cylRing ∈ cylinderGraph.cycleLattice :=
    cylinderGraph.mem_cycleLattice.mpr (by decide)
  rintro ⟨f, hf⟩
  have h0 := grad_dotProduct_castCycle f hring
  rw [← IncidenceGraph.gradLin_apply, hf] at h0
  revert h0
  decide

/-- **The boundary witness**: the radial cut is a non-exact cocycle of
weight `3`, so no decoder on the cylinder corrects every pair of
errors — the distance is exactly three. -/
theorem cylinder_not_decodable_two :
    ¬ ∃ D : cylinderComplex.Decoder (ZMod 2),
      StepClosed (noisyStep (LinearMap.id (R := ZMod 2))
          (D.residualSet {s | hammingNorm s ≤ 2}))
        (cylinderComplex.exactR (ZMod 2)).mkQ
        (cylinderComplex.exactR (ZMod 2)).mkQ := by
  rw [TwoComplex.decodable_iff]
  intro h
  have hw : hammingNorm cylCut = 3 := by decide
  have := h cylCut cylCut_mem_cocycles cylCut_not_exact
  omega

end Meno
