import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic
import Meno.Basic

/-! # The Simplicial Model -/

namespace Simplicial

open SGD

universe u

/-- A directed graph: vertices with labeled edges. -/
structure Graph (V : Type u) where
  edge : V → V → Prop

/-- A 2-complex: graph with faces (triangles) that can be contracted.
    Faces provide the relaxation mechanism - cycles through filled triangles
    can shorten, while unfilled cycles persist as matter. -/
structure Complex (V : Type u) extends Graph V where
  face : V → V → V → Prop
  face_closed : ∀ a b c, face a b c → edge a b ∧ edge b c ∧ edge a c
  face_cycle : ∀ a b c, face a b c → face b c a

/-- A graph is symmetric if every edge has a reverse. -/
def Graph.Symmetric (G : Graph V) : Prop := ∀ i j, G.edge i j → G.edge j i

/-- A graph is irreflexive if no vertex has a self-loop. -/
def Graph.Irreflexive (G : Graph V) : Prop := ∀ i, ¬G.edge i i

variable {V : Type u}

/-- A walk is a sequence of vertices where consecutive pairs are edges. -/
inductive Walk (G : Graph V) : V → V → Type u
  | nil (v : V) : Walk G v v
  | cons {v w x : V} (h : G.edge v w) (p : Walk G w x) : Walk G v x

/-- Length of a walk. -/
def Walk.length : Walk G v w → ℕ
  | .nil _ => 0
  | .cons _ p => p.length + 1

/-- Concatenate two walks. -/
def Walk.append : Walk G u v → Walk G v w → Walk G u w
  | .nil _, q => q
  | .cons h p, q => .cons h (p.append q)

/-- A cycle: a non-trivial loop. -/
structure Cycle (G : Graph V) (v : V) where
  walk : Walk G v v
  nontrivial : walk.length > 0

/-! ## Homotopy in a 2-Complex -/

/-- Homotopy relation in a 2-complex. Includes face reductions. -/
inductive Homotopic₂ (C : Complex V) : Walk C.toGraph u v → Walk C.toGraph u v → Prop
  | refl (p : Walk C.toGraph u v) : Homotopic₂ C p p
  | symm {p q} : Homotopic₂ C p q → Homotopic₂ C q p
  | trans {p q r} : Homotopic₂ C p q → Homotopic₂ C q r → Homotopic₂ C p r
  | backtrack {a b w} (hab : C.edge a b) (hba : C.edge b a) (tail : Walk C.toGraph a w) :
      Homotopic₂ C (Walk.cons hab (Walk.cons hba tail)) tail
  | face {a b c w} (hf : C.face a b c) (tail : Walk C.toGraph c w) :
      Homotopic₂ C
        (Walk.cons (C.face_closed a b c hf).1 (Walk.cons (C.face_closed a b c hf).2.1 tail))
        (Walk.cons (C.face_closed a b c hf).2.2 tail)
  | face_rev {a b c w} (hf : C.face a b c)
      (hcb : C.edge c b) (hba : C.edge b a) (hca : C.edge c a)
      (tail : Walk C.toGraph a w) :
      Homotopic₂ C (Walk.cons hcb (Walk.cons hba tail)) (Walk.cons hca tail)
  | congr_cons {a b w} (h : C.edge a b) {p q : Walk C.toGraph b w} :
      Homotopic₂ C p q → Homotopic₂ C (Walk.cons h p) (Walk.cons h q)

/-- Homotopy is a right congruence for concatenation. -/
theorem Homotopic₂.congr_append_right (C : Complex V) (p : Walk C.toGraph u v)
    {q q' : Walk C.toGraph v w} (hq : Homotopic₂ C q q') :
    Homotopic₂ C (p.append q) (p.append q') := by
  induction p with
  | nil _ => exact hq
  | cons h _ ih => exact Homotopic₂.congr_cons h (ih hq)

/-- Concatenation preserves homotopy: if p ~ p' and q ~ q', then p ++ q ~ p' ++ q'. -/
theorem Homotopic₂.congr_append (C : Complex V) {p p' : Walk C.toGraph u v} {q q' : Walk C.toGraph v w}
    (hp : Homotopic₂ C p p') (hq : Homotopic₂ C q q') :
    Homotopic₂ C (p.append q) (p'.append q') := by
  induction hp with
  | refl _ => exact congr_append_right C _ hq
  | symm _ ih => exact Homotopic₂.symm (ih (Homotopic₂.symm hq))
  | trans _ _ ih1 ih2 => exact Homotopic₂.trans (ih1 hq) (ih2 (Homotopic₂.refl q'))
  | backtrack hab hba tail =>
    simp only [Walk.append]
    exact Homotopic₂.trans (Homotopic₂.backtrack hab hba _) (congr_append_right C tail hq)
  | face hf tail =>
    simp only [Walk.append]
    have : Homotopic₂ C (Walk.cons (C.face_closed _ _ _ hf).2.2 (tail.append q))
                       (Walk.cons (C.face_closed _ _ _ hf).2.2 (tail.append q')) :=
      Homotopic₂.congr_cons _ (congr_append_right C tail hq)
    exact Homotopic₂.trans (Homotopic₂.face hf _) this
  | face_rev hf hcb hba hca tail =>
    simp only [Walk.append]
    exact Homotopic₂.trans (Homotopic₂.face_rev hf hcb hba hca _)
      (Homotopic₂.congr_cons _ (congr_append_right C tail hq))
  | congr_cons h _ ih =>
    simp only [Walk.append]
    exact Homotopic₂.congr_cons h (ih hq)

/-- A cycle is contractible in a 2-complex if homotopic to trivial. -/
def Cycle.isContractible₂ (C : Complex V) (c : Cycle C.toGraph v) : Prop :=
  Homotopic₂ C c.walk (Walk.nil v)

/-! ## Geodesic Length -/

/-- The set of lengths achievable by homotopic walks. -/
def homotopyLengths (C : Complex V) (p : Walk C.toGraph u v) : Set ℕ :=
  { n | ∃ q : Walk C.toGraph u v, Homotopic₂ C p q ∧ q.length = n }

/-- Geodesic length: minimum over homotopy class. This is the true complexity. -/
noncomputable def geodesicLength (C : Complex V) (p : Walk C.toGraph u v) : ℕ :=
  sInf (homotopyLengths C p)

/-- The original length is in the homotopy class. -/
theorem length_mem_homotopyLengths (C : Complex V) (p : Walk C.toGraph u v) :
    p.length ∈ homotopyLengths C p :=
  ⟨p, Homotopic₂.refl p, rfl⟩

/-- Geodesic length is at most the current length. -/
theorem geodesicLength_le_length (C : Complex V) (p : Walk C.toGraph u v) :
    geodesicLength C p ≤ p.length := by
  apply Nat.sInf_le
  exact length_mem_homotopyLengths C p

/-- Homotopy classes have the same length sets. -/
theorem homotopyLengths_eq_of_homotopic (C : Complex V) {p q : Walk C.toGraph u v}
    (h : Homotopic₂ C p q) : homotopyLengths C p = homotopyLengths C q := by
  ext n
  constructor
  · intro ⟨r, hr, hn⟩; exact ⟨r, Homotopic₂.trans (Homotopic₂.symm h) hr, hn⟩
  · intro ⟨r, hr, hn⟩; exact ⟨r, Homotopic₂.trans h hr, hn⟩

/-- Homotopic walks have the same geodesic length. -/
theorem geodesicLength_eq_of_homotopic (C : Complex V) {p q : Walk C.toGraph u v}
    (h : Homotopic₂ C p q) : geodesicLength C p = geodesicLength C q := by
  simp only [geodesicLength, homotopyLengths_eq_of_homotopic C h]

/-- The geodesic length is achieved: there exists a homotopic walk of minimal length.
    This is the key finiteness property that makes geodesicLength well-defined. -/
theorem geodesicLength_achieved (C : Complex V) (p : Walk C.toGraph u v) :
    ∃ q : Walk C.toGraph u v, Homotopic₂ C p q ∧ q.length = geodesicLength C p := by
  have hne : (homotopyLengths C p).Nonempty := ⟨p.length, length_mem_homotopyLengths C p⟩
  have hmem := Nat.sInf_mem hne
  exact hmem

/-- Contractible cycles have geodesic length 0. -/
theorem geodesicLength_zero_of_contractible (C : Complex V) (c : Cycle C.toGraph v)
    (hc : c.isContractible₂ C) : geodesicLength C c.walk = 0 := by
  apply Nat.eq_zero_of_le_zero
  calc geodesicLength C c.walk
      = geodesicLength C (Walk.nil v) := geodesicLength_eq_of_homotopic C hc
    _ ≤ (Walk.nil v).length := geodesicLength_le_length C (Walk.nil v)
    _ = 0 := rfl

/-! ## Cycle Complexity -/

/-- Complexity of a cycle: its geodesic length. -/
noncomputable def cycleComplexity (C : Complex V) (c : Cycle C.toGraph v) : ℕ :=
  geodesicLength C c.walk

/-- Contractible cycles have zero complexity. -/
theorem cycleComplexity_zero_of_contractible (C : Complex V) (c : Cycle C.toGraph v)
    (hc : c.isContractible₂ C) : cycleComplexity C c = 0 :=
  geodesicLength_zero_of_contractible C c hc

/-- Non-contractible cycles have positive complexity (they are matter). -/
theorem cycleComplexity_pos_of_noncontractible (C : Complex V) (c : Cycle C.toGraph v)
    (hc : ¬c.isContractible₂ C) : cycleComplexity C c > 0 := by
  simp only [cycleComplexity]
  have h : geodesicLength C c.walk ≠ 0 := by
    intro hz
    obtain ⟨q, hq, hlen⟩ := geodesicLength_achieved C c.walk
    rw [hz] at hlen
    cases q with
    | nil _ => exact hc hq
    | cons _ _ => simp [Walk.length] at hlen
  exact Nat.pos_of_ne_zero h

/-! ## Mass and Matter -/

/-- Mass of a cycle: its geodesic length in the fixed complex. -/
noncomputable def Mass (C : Complex V) (c : Cycle C.toGraph v) : ℕ :=
  cycleComplexity C c

/-- A cycle is matter if its mass is positive. -/
def IsMatter (C : Complex V) (c : Cycle C.toGraph v) : Prop :=
  Mass C c > 0

/-- Contractible cycles have zero mass (vacuum). -/
theorem contractible_zero_mass (C : Complex V) (c : Cycle C.toGraph v)
    (hc : c.isContractible₂ C) : Mass C c = 0 :=
  cycleComplexity_zero_of_contractible C c hc

/-- Matter cycles are non-contractible. -/
theorem matter_noncontractible (C : Complex V) (c : Cycle C.toGraph v)
    (hm : IsMatter C c) : ¬c.isContractible₂ C := by
  intro hc; rw [IsMatter, contractible_zero_mass C c hc] at hm; exact Nat.lt_irrefl 0 hm

/-! ## Pure 1-Skeleton (No Faces) -/

/-- Homotopy in a pure graph (no faces). Includes backtracking reduction. -/
inductive Homotopic (G : Graph V) : Walk G u v → Walk G u v → Prop
  | refl (p : Walk G u v) : Homotopic G p p
  | symm {p q : Walk G u v} : Homotopic G p q → Homotopic G q p
  | trans {p q r : Walk G u v} : Homotopic G p q → Homotopic G q r → Homotopic G p r
  | backtrack {a b w} (hab : G.edge a b) (hba : G.edge b a) (tail : Walk G a w) :
      Homotopic G (Walk.cons hab (Walk.cons hba tail)) tail
  | congr_cons {a b w} (h : G.edge a b) {p q : Walk G b w} :
      Homotopic G p q → Homotopic G (Walk.cons h p) (Walk.cons h q)

/-- Backtracking changes length by exactly 2. -/
theorem backtrack_length_diff {a b w : V} (hab : G.edge a b) (hba : G.edge b a)
    (tail : Walk G a w) :
    (Walk.cons hab (Walk.cons hba tail)).length = tail.length + 2 := by
  simp [Walk.length]

/-- Homotopy preserves length parity. -/
theorem homotopic_length_parity {p q : Walk G u v} (h : Homotopic G p q) :
    p.length % 2 = q.length % 2 := by
  induction h with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | backtrack hab hba tail => simp [Walk.length]; omega
  | congr_cons _ _ ih => simp [Walk.length]; omega

/-- A cycle is contractible if it's homotopic to the trivial walk. -/
def Cycle.isContractible (c : Cycle G v) : Prop :=
  Homotopic G c.walk (Walk.nil v)

/-- Odd-length cycles are NOT contractible in a pure 1-skeleton.
    Even-length cycles may contract via backtracking (a→b→a ~ a). -/
theorem odd_cycle_not_contractible (c : Cycle G v) (hodd : c.walk.length % 2 = 1) :
    ¬c.isContractible := by
  intro hcontr
  have hparity := homotopic_length_parity hcontr
  simp only [Walk.length] at hparity
  omega

/-! ## Examples -/

/-! ## The Cycle Graph C_n -/

/-- Next vertex in the cycle: i ↦ (i+1) mod n. -/
def cycleNext (n : ℕ) (hn : n ≥ 3) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩

/-- The cycle graph C_n: Fin n vertices with next/prev edges, no faces. -/
def CycleGraph (n : ℕ) (hn : n ≥ 3) : Complex (Fin n) where
  edge := fun i j => j = cycleNext n hn i ∨ i = cycleNext n hn j
  face := fun _ _ _ => False
  face_closed := fun _ _ _ h => h.elim
  face_cycle := fun _ _ _ h => h.elim

/-- The cycle graph has no faces. -/
theorem cycleGraph_no_faces (n : ℕ) (hn : n ≥ 3) : ∀ a b c, ¬(CycleGraph n hn).face a b c :=
  fun _ _ _ h => h

/-! ## Cycle Arithmetic -/

/-- Forward and backward cycle edges are mutually exclusive (n ≥ 3). -/
lemma cycleNext_not_both (n : ℕ) (hn : n ≥ 3) (i j : Fin n)
    (hf : j = cycleNext n hn i) : i ≠ cycleNext n hn j := by
  intro heq
  have h1 : j.val = (i.val + 1) % n := congr_arg Fin.val hf
  have h2 : i.val = (j.val + 1) % n := congr_arg Fin.val heq
  have hi := i.isLt
  rw [h1] at h2
  by_cases h3 : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt h3] at h2
    by_cases h4 : i.val + 2 < n
    · rw [Nat.mod_eq_of_lt h4] at h2; omega
    · rw [show i.val + 2 = n by omega, Nat.mod_self] at h2; omega
  · rw [show i.val + 1 = n by omega, Nat.mod_self] at h2
    rw [Nat.mod_eq_of_lt (show 1 < n by omega)] at h2; omega

/-- Previous vertex in the cycle: i ↦ (i+n-1) mod n. -/
def cyclePrev (n : ℕ) (hn : n ≥ 3) (i : Fin n) : Fin n :=
  ⟨(i.val + n - 1) % n, Nat.mod_lt _ (by omega)⟩

/-- cyclePrev is the left inverse of cycleNext. -/
lemma cyclePrev_cycleNext (n : ℕ) (hn : n ≥ 3) (i : Fin n) :
    cyclePrev n hn (cycleNext n hn i) = i := by
  ext; simp only [cyclePrev, cycleNext, Fin.val_mk]
  have hi := i.isLt
  by_cases h : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt h, show i.val + 1 + n - 1 = n + i.val by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt hi]
  · rw [show i.val + 1 = n by omega, Nat.mod_self, show 0 + n - 1 = n - 1 by omega,
        Nat.mod_eq_of_lt (by omega : n - 1 < n)]
    omega

/-- cycleNext is the left inverse of cyclePrev. -/
lemma cycleNext_cyclePrev (n : ℕ) (hn : n ≥ 3) (i : Fin n) :
    cycleNext n hn (cyclePrev n hn i) = i := by
  ext; simp only [cycleNext, cyclePrev, Fin.val_mk]
  have hi := i.isLt
  by_cases h : i.val = 0
  · rw [h, show 0 + n - 1 = n - 1 by omega, Nat.mod_eq_of_lt (by omega : n - 1 < n),
        show n - 1 + 1 = n by omega, Nat.mod_self]
  · rw [show i.val + n - 1 = n + (i.val - 1) by omega, Nat.add_mod_left,
        Nat.mod_eq_of_lt (by omega : i.val - 1 < n),
        show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt hi]

/-- i = cycleNext(j) iff j = cyclePrev(i). -/
lemma eq_cycleNext_iff_cyclePrev (n : ℕ) (hn : n ≥ 3) (i j : Fin n) :
    i = cycleNext n hn j ↔ j = cyclePrev n hn i := by
  constructor
  · intro h; rw [h, cyclePrev_cycleNext]
  · intro h; rw [h, cycleNext_cyclePrev]

/-- cycleNext is an equivalence (permutation) on Fin n. -/
def cycleNextEquiv (n : ℕ) (hn : n ≥ 3) : Fin n ≃ Fin n where
  toFun := cycleNext n hn
  invFun := cyclePrev n hn
  left_inv := cyclePrev_cycleNext n hn
  right_inv := cycleNext_cyclePrev n hn

/-- Value of iterated cycleNext. -/
lemma cycleNext_iterate_val (n : ℕ) (hn : n ≥ 3) (i : Fin n) : ∀ k : ℕ,
    ((cycleNext n hn)^[k] i).val = (i.val + k) % n
  | 0 => by simp [Nat.mod_eq_of_lt i.isLt]
  | k + 1 => by
    rw [Function.iterate_succ', Function.comp, cycleNext, Fin.val_mk,
        cycleNext_iterate_val n hn i k, show i.val + (k + 1) = i.val + k + 1 from by omega]
    conv_lhs => rw [show (1 : ℕ) = 1 % n from (Nat.mod_eq_of_lt (show 1 < n by omega)).symm]
    exact (Nat.add_mod (i.val + k) 1 n).symm

/-- Going around the full cycle returns to the start. -/
lemma cycleNext_iterate_n (n : ℕ) (hn : n ≥ 3) (i : Fin n) :
    (cycleNext n hn)^[n] i = i := by
  ext; rw [cycleNext_iterate_val]
  simp [Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

/-! ## Walk Infrastructure for CycleGraph -/

/-- Edge direction: +1 for forward, -1 for backward. -/
def edgeDir (n : ℕ) (hn : n ≥ 3) (i j : Fin n)
    (_ : (CycleGraph n hn).edge i j) : ℤ :=
  if j = cycleNext n hn i then 1 else -1

/-- Opposite edges cancel. -/
lemma edgeDir_cancel (n : ℕ) (hn : n ≥ 3) (i j : Fin n)
    (hij : (CycleGraph n hn).edge i j) (hji : (CycleGraph n hn).edge j i) :
    edgeDir n hn i j hij + edgeDir n hn j i hji = 0 := by
  simp only [edgeDir]
  rcases hij with hf | hb
  · simp only [if_pos hf, if_neg (cycleNext_not_both n hn i j hf)]; norm_num
  · simp only [if_neg (cycleNext_not_both n hn j i hb), if_pos hb]; norm_num

/-- Winding count: algebraic sum of edge directions along a walk. -/
def Walk.windingCount {n : ℕ} {hn : n ≥ 3} {s t : Fin n} :
    Walk (CycleGraph n hn).toGraph s t → ℤ
  | .nil _ => 0
  | .cons h p => edgeDir n hn _ _ h + p.windingCount

/-- Transport of endpoint doesn't change length. -/
@[simp] lemma Walk.length_cast {G : Graph V} {a b c : V} (h : b = c)
    (p : Walk G a b) : (h ▸ p).length = p.length := by subst h; rfl

/-- Transport of endpoint doesn't change windingCount. -/
@[simp] lemma Walk.windingCount_cast {n : ℕ} {hn : n ≥ 3} {s t r : Fin n}
    (h : t = r) (p : Walk (CycleGraph n hn).toGraph s t) :
    (h ▸ p).windingCount = p.windingCount := by subst h; rfl

/-- Winding count is a homotopy invariant. -/
theorem windingCount_homotopy_invariant {n : ℕ} {hn : n ≥ 3}
    {s t : Fin n} {p q : Walk (CycleGraph n hn).toGraph s t}
    (h : Homotopic₂ (CycleGraph n hn) p q) : p.windingCount = q.windingCount := by
  induction h with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | backtrack hab hba tail =>
    simp only [Walk.windingCount]
    have := edgeDir_cancel n hn _ _ hab hba
    omega
  | face hf => exact hf.elim
  | face_rev hf => exact hf.elim
  | congr_cons _ _ ih => simp only [Walk.windingCount]; omega

/-- Triangle inequality: |windingCount| ≤ length. -/
theorem windingCount_abs_le_length {n : ℕ} {hn : n ≥ 3}
    {s t : Fin n} (p : Walk (CycleGraph n hn).toGraph s t) :
    p.windingCount.natAbs ≤ p.length := by
  induction p with
  | nil _ => simp [Walk.windingCount]
  | cons h tail ih =>
    simp only [Walk.windingCount, Walk.length]
    have habs : (edgeDir n hn _ _ h).natAbs = 1 := by
      simp only [edgeDir]; split <;> simp
    calc (edgeDir n hn _ _ h + tail.windingCount).natAbs
        ≤ (edgeDir n hn _ _ h).natAbs + tail.windingCount.natAbs := Int.natAbs_add_le _ _
      _ = 1 + tail.windingCount.natAbs := by rw [habs]
      _ ≤ 1 + tail.length := by omega
      _ = tail.length + 1 := by omega

/-! ## Canonical Cycle Walk -/

/-- Forward walk from vertex i through k steps, as a sigma type. -/
def cycleForwardWalkAux (n : ℕ) (hn : n ≥ 3) :
    (k : ℕ) → (i : Fin n) → Σ j : Fin n, Walk (CycleGraph n hn).toGraph i j
  | 0, i => ⟨i, Walk.nil i⟩
  | k + 1, i =>
    let ⟨j, w⟩ := cycleForwardWalkAux n hn k (cycleNext n hn i)
    ⟨j, Walk.cons (Or.inl rfl : (CycleGraph n hn).edge i (cycleNext n hn i)) w⟩

/-- The endpoint of cycleForwardWalkAux is (cycleNext^[k]) i. -/
lemma cycleForwardWalkAux_fst (n : ℕ) (hn : n ≥ 3) (k : ℕ) (i : Fin n) :
    (cycleForwardWalkAux n hn k i).1 = (cycleNext n hn)^[k] i := by
  induction k generalizing i with
  | zero => simp [cycleForwardWalkAux]
  | succ k ih =>
    rw [show (cycleForwardWalkAux n hn (k + 1) i).1 =
        (cycleForwardWalkAux n hn k (cycleNext n hn i)).1 from rfl,
      ih, ← Function.iterate_succ_apply]

/-- Length of cycleForwardWalkAux is k. -/
lemma cycleForwardWalkAux_length (n : ℕ) (hn : n ≥ 3) (k : ℕ) (i : Fin n) :
    (cycleForwardWalkAux n hn k i).2.length = k := by
  induction k generalizing i with
  | zero => simp [cycleForwardWalkAux, Walk.length]
  | succ k ih => simp only [cycleForwardWalkAux, Walk.length]; rw [ih]

/-- WindingCount of cycleForwardWalkAux is k. -/
lemma cycleForwardWalkAux_windingCount (n : ℕ) (hn : n ≥ 3) (k : ℕ) (i : Fin n) :
    (cycleForwardWalkAux n hn k i).2.windingCount = (k : ℤ) := by
  induction k generalizing i with
  | zero => simp [cycleForwardWalkAux, Walk.windingCount]
  | succ k ih =>
    simp only [cycleForwardWalkAux, Walk.windingCount, edgeDir]
    rw [ih]; push_cast; ring

/-- Transport of walk endpoint (precise: only changes endpoint, not start). -/
def Walk.castEnd {G : Graph V} {a b c : V} (h : b = c) (p : Walk G a b) : Walk G a c :=
  h ▸ p

@[simp] lemma Walk.castEnd_length {G : Graph V} {a b c : V} (h : b = c) (p : Walk G a b) :
    (p.castEnd h).length = p.length := by subst h; rfl

@[simp] lemma Walk.castEnd_windingCount {n : ℕ} {hn : n ≥ 3} {s t r : Fin n}
    (h : t = r) (p : Walk (CycleGraph n hn).toGraph s t) :
    (p.castEnd h).windingCount = p.windingCount := by subst h; rfl

/-- The canonical cycle walk: 0 → 1 → 2 → ... → (n-1) → 0. -/
def cycleWalk (n : ℕ) (hn : n ≥ 3) :
    Walk (CycleGraph n hn).toGraph (⟨0, by omega⟩ : Fin n) ⟨0, by omega⟩ :=
  (cycleForwardWalkAux n hn n ⟨0, by omega⟩).2.castEnd
    ((cycleForwardWalkAux_fst n hn n _).trans (cycleNext_iterate_n n hn _))

theorem cycleWalk_length (n : ℕ) (hn : n ≥ 3) : (cycleWalk n hn).length = n := by
  simp [cycleWalk, cycleForwardWalkAux_length]

theorem cycleWalk_windingCount (n : ℕ) (hn : n ≥ 3) :
    (cycleWalk n hn).windingCount = (n : ℤ) := by
  simp [cycleWalk, cycleForwardWalkAux_windingCount]

/-- The canonical cycle. -/
def cycleCycle (n : ℕ) (hn : n ≥ 3) : Cycle (CycleGraph n hn).toGraph (⟨0, by omega⟩ : Fin n) where
  walk := cycleWalk n hn
  nontrivial := by rw [cycleWalk_length]; omega

/-! ## Main Topological Results -/

/-- The cycle graph is not contractible: the canonical cycle cannot be homotoped to nil. -/
theorem cycleGraph_not_contractible (n : ℕ) (hn : n ≥ 3) :
    ¬(cycleCycle n hn).isContractible₂ (CycleGraph n hn) := by
  intro hcontr
  have hwc := windingCount_homotopy_invariant hcontr
  simp only [cycleCycle, cycleWalk_windingCount, Walk.windingCount] at hwc
  omega

/-- Geodesic length of the canonical cycle on C_n is exactly n. -/
theorem cycleGraph_geodesic_eq_n (n : ℕ) (hn : n ≥ 3) :
    geodesicLength (CycleGraph n hn) (cycleWalk n hn) = n := by
  apply le_antisymm
  · calc geodesicLength (CycleGraph n hn) (cycleWalk n hn)
        ≤ (cycleWalk n hn).length := geodesicLength_le_length _ _
      _ = n := cycleWalk_length n hn
  · apply le_csInf ⟨_, length_mem_homotopyLengths _ _⟩
    intro m ⟨q, hq, hlen⟩
    have hwc : q.windingCount = (n : ℤ) :=
      (windingCount_homotopy_invariant hq).symm.trans (cycleWalk_windingCount n hn)
    rw [← hlen]
    calc n = (n : ℤ).natAbs := by simp
      _ = q.windingCount.natAbs := by rw [hwc]
      _ ≤ q.length := windingCount_abs_le_length q

/-! ## Path Cost -/

/-- Walks between distinct vertices have positive length. -/
theorem walk_cost_pos {G : Graph V} {v w : V} (p : Walk G v w) (hne : v ≠ w) :
    p.length > 0 := by
  cases p with
  | nil _ => exact absurd rfl hne
  | cons _ _ => simp [Walk.length]

/-- A filled disk: triangle with a face. The boundary cycle CAN contract. -/
def Disk : Complex (Fin 3) where
  edge := fun i j => i ≠ j  -- complete graph on 3 vertices
  face := fun a b c => a ≠ b ∧ b ≠ c ∧ a ≠ c  -- unoriented: any triple of distinct vertices
  face_closed := fun _ _ _ h => h
  face_cycle := fun _ _ _ ⟨hab, hbc, hac⟩ => ⟨hbc, hac.symm, hab.symm⟩

-- Edge proofs for disk
private theorem disk_01 : Disk.edge 0 1 := by simp [Disk]
private theorem disk_12 : Disk.edge 1 2 := by simp [Disk]
private theorem disk_20 : Disk.edge 2 0 := by simp [Disk]
private theorem disk_02 : Disk.edge 0 2 := by simp [Disk]

/-- The boundary of the disk: 0 → 1 → 2 → 0 -/
def diskBoundary : Walk Disk.toGraph 0 0 :=
  Walk.cons disk_01 (Walk.cons disk_12 (Walk.cons disk_20 (Walk.nil 0)))

/-- The boundary cycle. -/
def diskCycle : Cycle Disk.toGraph 0 where
  walk := diskBoundary
  nontrivial := by decide

/-- In the 2-complex with face, a triangle boundary step can shorten.
    This demonstrates relaxation - the mechanism for potential energy. -/
theorem disk_can_shorten :
    Homotopic₂ Disk
      (Walk.cons disk_01 (Walk.cons disk_12 (Walk.nil 2)))
      (Walk.cons disk_02 (Walk.nil 2)) := by
  exact Homotopic₂.face (by simp [Disk] : Disk.face 0 1 2) (Walk.nil 2)

/-- The disk boundary IS contractible: 0→1→2→0 ~ nil via face + backtrack.
    This is the central theorem: faces allow cycles to contract to nothing. -/
theorem disk_contractible : diskCycle.isContractible₂ Disk := by
  unfold Cycle.isContractible₂ diskCycle diskBoundary
  exact Homotopic₂.trans (Homotopic₂.face (by simp [Disk]) _) (Homotopic₂.backtrack disk_02 disk_20 _)

/-! ## Gluing: Interaction as Union -/

/-- Union of two complexes over the same vertex set.
    Edges and faces from either complex are available. -/
def Complex.union (C₁ C₂ : Complex V) : Complex V where
  edge := fun v w => C₁.edge v w ∨ C₂.edge v w
  face := fun a b c => C₁.face a b c ∨ C₂.face a b c
  face_closed := by
    intro a b c hf
    cases hf with
    | inl h => exact ⟨Or.inl (C₁.face_closed a b c h).1,
                      Or.inl (C₁.face_closed a b c h).2.1,
                      Or.inl (C₁.face_closed a b c h).2.2⟩
    | inr h => exact ⟨Or.inr (C₂.face_closed a b c h).1,
                      Or.inr (C₂.face_closed a b c h).2.1,
                      Or.inr (C₂.face_closed a b c h).2.2⟩
  face_cycle := fun _ _ _ hf => hf.elim (Or.inl ∘ C₁.face_cycle _ _ _) (Or.inr ∘ C₂.face_cycle _ _ _)

/-- A walk in C₁ can be lifted to the union. -/
def Walk.toUnion₁ (C₁ C₂ : Complex V) : Walk C₁.toGraph u v → Walk (C₁.union C₂).toGraph u v
  | .nil w => .nil w
  | .cons h p => .cons (Or.inl h) (p.toUnion₁ C₁ C₂)

/-- A walk in C₂ can be lifted to the union. -/
def Walk.toUnion₂ (C₁ C₂ : Complex V) : Walk C₂.toGraph u v → Walk (C₁.union C₂).toGraph u v
  | .nil w => .nil w
  | .cons h p => .cons (Or.inr h) (p.toUnion₂ C₁ C₂)

/-- Lifting preserves length. -/
theorem Walk.toUnion₁_length (C₁ C₂ : Complex V) (p : Walk C₁.toGraph u v) :
    (p.toUnion₁ C₁ C₂).length = p.length := by
  induction p with
  | nil _ => rfl
  | cons _ _ ih => simp [Walk.toUnion₁, Walk.length, ih]

/-- A cycle in C₁ lifts to a cycle in the union C₁ ∪ C₂. -/
def Cycle.toUnion₁ (C₁ C₂ : Complex V) (c : Cycle C₁.toGraph v) :
    Cycle (C₁.union C₂).toGraph v where
  walk := c.walk.toUnion₁ C₁ C₂
  nontrivial := by simpa [Walk.toUnion₁_length] using c.nontrivial

/-- Homotopy in C₁ lifts to homotopy in the union. -/
theorem Homotopic₂.toUnion₁ (C₁ C₂ : Complex V) {p q : Walk C₁.toGraph u v}
    (h : Homotopic₂ C₁ p q) : Homotopic₂ (C₁.union C₂) (p.toUnion₁ C₁ C₂) (q.toUnion₁ C₁ C₂) := by
  induction h with
  | refl p => exact Homotopic₂.refl _
  | symm _ ih => exact Homotopic₂.symm ih
  | trans _ _ ih1 ih2 => exact Homotopic₂.trans ih1 ih2
  | backtrack hab hba tail =>
    simp only [Walk.toUnion₁]
    exact Homotopic₂.backtrack (Or.inl hab) (Or.inl hba) _
  | face hf tail =>
    simp only [Walk.toUnion₁]
    have hf' : (C₁.union C₂).face _ _ _ := Or.inl hf
    exact Homotopic₂.face hf' (tail.toUnion₁ C₁ C₂)
  | face_rev hf hcb hba hca tail =>
    simp only [Walk.toUnion₁]
    exact Homotopic₂.face_rev (Or.inl hf) (Or.inl hcb) (Or.inl hba) (Or.inl hca) _
  | congr_cons h _ ih =>
    simp only [Walk.toUnion₁]
    exact Homotopic₂.congr_cons (Or.inl h) ih

/-- Lifting a homotopy class to union includes all lifted lengths. -/
theorem homotopyLengths_lift_subset (C₁ C₂ : Complex V) (p : Walk C₁.toGraph u v) :
    homotopyLengths C₁ p ⊆ homotopyLengths (C₁.union C₂) (p.toUnion₁ C₁ C₂) := by
  intro n ⟨q, hq, hlen⟩
  exact ⟨q.toUnion₁ C₁ C₂, Homotopic₂.toUnion₁ C₁ C₂ hq, by rw [Walk.toUnion₁_length, hlen]⟩

/-- The union has at least as many reduction paths as C₁ alone.
    Therefore geodesic length in union ≤ geodesic length in C₁. -/
theorem geodesicLength_union_le₁ (C₁ C₂ : Complex V) (p : Walk C₁.toGraph u v) :
    geodesicLength (C₁.union C₂) (p.toUnion₁ C₁ C₂) ≤ geodesicLength C₁ p := by
  simp only [geodesicLength]
  -- Union's homotopy set contains C₁'s homotopy set (via lifting)
  -- So sInf of the larger set ≤ sInf of smaller set? No, opposite!
  -- Actually: if S₁ ⊆ S₂, then sInf S₂ ≤ sInf S₁ (more elements, can be smaller)
  -- But we have the opposite: C₁'s set lifts INTO union's set
  -- Union may have MORE homotopic walks (via C₂'s faces), so LARGER set, so SMALLER sInf
  apply csInf_le_csInf
  · -- Union's homotopy lengths is bounded below by 0
    exact ⟨0, fun _ _ => Nat.zero_le _⟩
  · -- C₁'s homotopy lengths is nonempty
    exact ⟨p.length, length_mem_homotopyLengths C₁ p⟩
  · -- C₁'s lengths ⊆ union's lengths
    exact homotopyLengths_lift_subset C₁ C₂ p

/-! ## Binding Energy -/

/-- Two complexes share a face if they both contain the same triangle. -/
def Complex.sharesFace (C₁ C₂ : Complex V) : Prop :=
  ∃ a b c, C₁.face a b c ∧ C₂.face a b c

/-- Binding energy between two complexes for a specific cycle.
    Positive when the union allows more reduction than either alone. -/
noncomputable def cycleBindingEnergy (C₁ C₂ : Complex V) (c : Cycle C₁.toGraph v) : ℕ :=
  cycleComplexity C₁ c - cycleComplexity (C₁.union C₂) (c.toUnion₁ C₁ C₂)

/-- Union cannot increase cycle complexity: extra faces only add reduction paths. -/
theorem cycleComplexity_union_le (C₁ C₂ : Complex V) (c : Cycle C₁.toGraph v) :
    cycleComplexity (C₁.union C₂) (c.toUnion₁ C₁ C₂) ≤ cycleComplexity C₁ c := by
  simpa [cycleComplexity, Cycle.toUnion₁] using geodesicLength_union_le₁ C₁ C₂ c.walk

/-- Binding energy decomposes cycle complexity into residual + released parts. -/
theorem cycleBindingEnergy_add_union (C₁ C₂ : Complex V) (c : Cycle C₁.toGraph v) :
    cycleBindingEnergy C₁ C₂ c + cycleComplexity (C₁.union C₂) (c.toUnion₁ C₁ C₂) =
      cycleComplexity C₁ c := by
  unfold cycleBindingEnergy
  exact Nat.sub_add_cancel (cycleComplexity_union_le C₁ C₂ c)

/-! ## Shared Faces Enable Binding -/

/-- A cycle becomes contractible in the union if C₂ provides the missing face. -/
def Cycle.contractibleInUnion (C₁ C₂ : Complex V) (c : Cycle C₁.toGraph v) : Prop :=
  (c.toUnion₁ C₁ C₂).isContractible₂ (C₁.union C₂)

/-- When a cycle contracts in the union, all its mass becomes binding energy. -/
theorem binding_releases_mass (C₁ C₂ : Complex V) (c : Cycle C₁.toGraph v)
    (hc : c.contractibleInUnion C₁ C₂) :
    cycleBindingEnergy C₁ C₂ c = cycleComplexity C₁ c := by
  simp only [cycleBindingEnergy]
  have h := cycleComplexity_zero_of_contractible (C₁.union C₂) _ hc
  simp only [h, Nat.sub_zero]

/-! ## The Mass Defect: Hollow Triangle Example -/

/-- The hollow triangle: same edges as Disk, but NO face.
    This represents "potential matter" - a cycle waiting to be filled. -/
def HollowTriangle : Complex (Fin 3) where
  edge := fun i j => i ≠ j
  face := fun _ _ _ => False
  face_closed := fun _ _ _ h => h.elim
  face_cycle := fun _ _ _ h => h.elim

/-- The hollow triangle has the same graph structure as the disk. -/
theorem hollow_eq_disk_graph : HollowTriangle.toGraph = Disk.toGraph := rfl

-- Edge proofs for hollow (same as disk)
private theorem hollow_01 : HollowTriangle.edge 0 1 := by simp [HollowTriangle]
private theorem hollow_12 : HollowTriangle.edge 1 2 := by simp [HollowTriangle]
private theorem hollow_20 : HollowTriangle.edge 2 0 := by simp [HollowTriangle]
private theorem hollow_02 : HollowTriangle.edge 0 2 := by simp [HollowTriangle]

/-- The boundary walk in the hollow triangle. -/
def hollowBoundary : Walk HollowTriangle.toGraph 0 0 :=
  Walk.cons hollow_01 (Walk.cons hollow_12 (Walk.cons hollow_20 (Walk.nil 0)))

/-- The boundary cycle in the hollow triangle. -/
def hollowCycle : Cycle HollowTriangle.toGraph 0 where
  walk := hollowBoundary
  nontrivial := by decide

/-- In a complex with no faces, Homotopic₂ reduces to backtracking only.
    This preserves length parity, so odd cycles cannot contract. -/
theorem homotopic₂_no_faces_parity (C : Complex V) (hno : ∀ a b c, ¬C.face a b c)
    {p q : Walk C.toGraph u v} (h : Homotopic₂ C p q) :
    p.length % 2 = q.length % 2 := by
  induction h with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | backtrack _ _ _ => simp [Walk.length]; omega
  | face hf _ => exact (hno _ _ _ hf).elim
  | face_rev hf _ _ _ _ => exact (hno _ _ _ hf).elim
  | congr_cons _ _ ih => simp [Walk.length]; omega

/-! ## CycleGraph and HollowTriangle -/

/-- The hollow triangle has no faces. -/
theorem hollow_no_faces : ∀ a b c, ¬HollowTriangle.face a b c := by
  intro _ _ _ h; exact h

/-- The hollow boundary cannot contract: odd length, no faces to help. -/
theorem hollow_not_contractible₂ : ¬hollowCycle.isContractible₂ HollowTriangle := by
  intro hcontr
  have hparity := homotopic₂_no_faces_parity HollowTriangle hollow_no_faces hcontr
  simp only [hollowCycle, hollowBoundary, Walk.length] at hparity
  omega

/-- The hollow cycle has positive complexity (it is matter). -/
theorem hollow_positive_complexity : cycleComplexity HollowTriangle hollowCycle > 0 :=
  cycleComplexity_pos_of_noncontractible HollowTriangle hollowCycle hollow_not_contractible₂

/-- The union has Disk's face available. -/
theorem union_has_disk_face : (HollowTriangle.union Disk).face 0 1 2 :=
  Or.inr (by simp [Disk] : Disk.face 0 1 2)

/-- **The Central Theorem**: The hollow cycle CONTRACTS in the union with Disk.
    Disk's face provides the missing 2-cell, allowing the cycle to relax. -/
theorem hollow_contractible_in_union : hollowCycle.contractibleInUnion HollowTriangle Disk := by
  unfold Cycle.contractibleInUnion Cycle.isContractible₂
  simp only [Cycle.toUnion₁, hollowCycle, hollowBoundary]
  exact Homotopic₂.trans (Homotopic₂.face union_has_disk_face _)
    (Homotopic₂.backtrack (Or.inl hollow_02) (Or.inl hollow_20) _)

/-! ## General Triangle Filling -/

/-- A triangle walk: three edges forming a→b→c→a. -/
def triangleWalk (C : Complex V) {a b c : V}
    (hab : C.edge a b) (hbc : C.edge b c) (hca : C.edge c a) : Walk C.toGraph a a :=
  Walk.cons hab (Walk.cons hbc (Walk.cons hca (Walk.nil a)))

/-- A triangle cycle. -/
def triangleCycle (C : Complex V) {a b c : V}
    (hab : C.edge a b) (hbc : C.edge b c) (hca : C.edge c a) : Cycle C.toGraph a where
  walk := triangleWalk C hab hbc hca
  nontrivial := by simp [triangleWalk, Walk.length]

/-- **General Triangle Contraction**: A triangle cycle contracts when the face exists
    and edges are bidirectional (allowing backtracking). -/
theorem triangle_contracts (C : Complex V) {a b c : V}
    (hab : C.edge a b) (hbc : C.edge b c) (hca : C.edge c a)
    (hac : C.edge a c)  -- reverse edge for backtracking
    (hface : C.face a b c) :
    (triangleCycle C hab hbc hca).isContractible₂ C := by
  unfold Cycle.isContractible₂ triangleCycle triangleWalk
  -- a→b→c→a ~[face] a→c→a ~[backtrack] nil
  exact Homotopic₂.trans (Homotopic₂.face hface _) (Homotopic₂.backtrack hac hca _)

/-- Corollary: If C₁ lacks a face that C₂ provides, binding occurs for that triangle.
    Adding the missing face in C₂ is sufficient for contraction in the union. -/
theorem triangle_binding (C₁ C₂ : Complex V) {a b c : V}
    (hab : C₁.edge a b) (hbc : C₁.edge b c) (hca : C₁.edge c a) (hac : C₁.edge a c)
    (hyes : C₂.face a b c) :
    (triangleCycle C₁ hab hbc hca).contractibleInUnion C₁ C₂ := by
  unfold Cycle.contractibleInUnion Cycle.isContractible₂ triangleCycle triangleWalk
  simp only [Cycle.toUnion₁, Walk.toUnion₁]
  apply Homotopic₂.trans
  · exact Homotopic₂.face (Or.inr hyes) (Walk.cons (Or.inl hca) (Walk.nil a))
  · exact Homotopic₂.backtrack (Or.inl hac) (Or.inl hca) (Walk.nil a)

/-! ## Simplicial Gravity -/

/-- **Simplicial Gravity**: The analog of `gravity_uniform`.
    When a cycle gains contractibility from the union, binding energy is positive. -/
theorem simplicial_gravity (C₁ C₂ : Complex V) (c : Cycle C₁.toGraph v)
    (hmatter : ¬c.isContractible₂ C₁)
    (hcontracts : c.contractibleInUnion C₁ C₂) :
    cycleBindingEnergy C₁ C₂ c > 0 := by
  rw [binding_releases_mass C₁ C₂ c hcontracts]
  exact cycleComplexity_pos_of_noncontractible C₁ c hmatter

/-- The hollow triangle is an instance of simplicial gravity. -/
theorem hollow_is_simplicial_gravity :
    cycleBindingEnergy HollowTriangle Disk hollowCycle > 0 :=
  simplicial_gravity HollowTriangle Disk hollowCycle
    hollow_not_contractible₂ hollow_contractible_in_union

/-! ## Discrete Hodge Theory -/

section Hodge

open Finset BigOperators

/-- 0-cochains: functions from vertices to ℝ. -/
def C0 (V : Type*) := V → ℝ

/-- 1-cochains: skew-symmetric edge functions. -/
structure C1 (V : Type*) where
  val : V → V → ℝ
  skew : ∀ i j, val i j = -val j i

/-- The zero 1-cochain. -/
def C1.zero (V : Type*) : C1 V where
  val := fun _ _ => 0
  skew := by intros; ring

/-- Scalar multiplication on 1-cochains. -/
def C1.smul (c : ℝ) (σ : C1 V) : C1 V where
  val := fun i j => c * σ.val i j
  skew := by intro i j; rw [σ.skew]; ring

/-- Addition of 1-cochains. -/
def C1.add (σ τ : C1 V) : C1 V where
  val := fun i j => σ.val i j + τ.val i j
  skew := by intro i j; rw [σ.skew, τ.skew]; ring

/-- Subtraction of 1-cochains. -/
def C1.sub (σ τ : C1 V) : C1 V where
  val := fun i j => σ.val i j - τ.val i j
  skew := by intro i j; rw [σ.skew, τ.skew]; ring

/-- Gradient (coboundary d₀): discrete derivative φ ↦ (i,j) ↦ φ(j) - φ(i). -/
def d0 {V : Type*} (φ : C0 V) : C1 V where
  val := fun i j => φ j - φ i
  skew := by intro i j; ring

/-- Inner product on 1-cochains: ½ Σᵢⱼ σᵢⱼ · τᵢⱼ. -/
noncomputable def innerC1 {V : Type*} [Fintype V] (σ τ : C1 V) : ℝ :=
  (1/2) * ∑ i : V, ∑ j : V, σ.val i j * τ.val i j

/-- Energy (squared norm) of a 1-cochain. -/
noncomputable def energy {V : Type*} [Fintype V] (σ : C1 V) : ℝ := innerC1 σ σ

theorem innerC1_smul_left {V : Type*} [Fintype V] (c : ℝ) (σ τ : C1 V) :
    innerC1 (C1.smul c σ) τ = c * innerC1 σ τ := by
  simp only [innerC1, C1.smul]
  rw [← mul_assoc, mul_comm c, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  congr 1; ext i
  rw [Finset.mul_sum]
  congr 1; ext j
  ring

theorem innerC1_smul_right {V : Type*} [Fintype V] (c : ℝ) (σ τ : C1 V) :
    innerC1 σ (C1.smul c τ) = c * innerC1 σ τ := by
  simp only [innerC1, C1.smul]
  rw [← mul_assoc, mul_comm c, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  congr 1; ext i
  rw [Finset.mul_sum]
  congr 1; ext j
  ring

theorem energy_smul {V : Type*} [Fintype V] (c : ℝ) (σ : C1 V) :
    energy (C1.smul c σ) = c ^ 2 * energy σ := by
  simp only [energy, innerC1_smul_left, innerC1_smul_right]; ring

theorem innerC1_comm {V : Type*} [Fintype V] (σ τ : C1 V) :
    innerC1 σ τ = innerC1 τ σ := by
  simp only [innerC1]; congr 1
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

/-- ‖σ − τ‖² = ‖σ‖² − 2⟨σ,τ⟩ + ‖τ‖². The inner-product polarization identity. -/
theorem energy_sub {V : Type*} [Fintype V] (σ τ : C1 V) :
    energy (C1.sub σ τ) = energy σ - 2 * innerC1 σ τ + energy τ := by
  simp only [energy, innerC1, C1.sub]
  have pw : ∀ (i j : V), (σ.val i j - τ.val i j) * (σ.val i j - τ.val i j) =
      σ.val i j * σ.val i j + τ.val i j * τ.val i j +
      (-2) * (σ.val i j * τ.val i j) := by
    intros; ring
  simp_rw [pw, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- A 1-cochain is exact if it's a gradient. -/
def IsExact {V : Type*} (σ : C1 V) : Prop := ∃ φ : C0 V, d0 φ = σ

/-- A 1-cochain is harmonic if orthogonal to all exact forms. -/
def IsHarmonic {V : Type*} [Fintype V] (σ : C1 V) : Prop :=
  ∀ φ : C0 V, innerC1 (d0 φ) σ = 0

/-- The canonical harmonic 1-form on the n-cycle.
    Assigns ±1/n to forward/backward cycle edges. -/
noncomputable def cycleHarmonicForm (n : ℕ) (hn : n ≥ 3) : C1 (Fin n) where
  val := fun i j =>
    if j = cycleNext n hn i then (1 : ℝ) / n
    else if i = cycleNext n hn j then -(1 : ℝ) / n
    else 0
  skew := by
    intro i j
    by_cases hf : j = cycleNext n hn i
    · have hb : ¬(i = cycleNext n hn j) := cycleNext_not_both n hn i j hf
      simp only [if_pos hf, if_neg hb]
      ring
    · by_cases hb : i = cycleNext n hn j
      · simp only [if_neg hf, if_pos hb]
        ring
      · simp only [if_neg hf, if_neg hb]
        ring

/-- For each vertex i, the inner sum ∑ⱼ σᵢⱼ² has exactly two nonzero terms
    (forward and backward edge), each contributing (1/n)². -/
private lemma energy_inner_sum (n : ℕ) (hn : n ≥ 3) (i : Fin n) :
    ∑ j : Fin n, (cycleHarmonicForm n hn).val i j * (cycleHarmonicForm n hn).val i j =
    2 / (n : ℝ) ^ 2 := by
  simp only [cycleHarmonicForm]
  have : ∀ j : Fin n,
      (if j = cycleNext n hn i then (1 : ℝ) / n
        else if i = cycleNext n hn j then -1 / n else 0) *
      (if j = cycleNext n hn i then (1 : ℝ) / n
        else if i = cycleNext n hn j then -1 / n else 0) =
      (if j = cycleNext n hn i then 1 / (n : ℝ) ^ 2 else 0) +
      (if j = cyclePrev n hn i then 1 / (n : ℝ) ^ 2 else 0) := by
    intro j
    simp only [show (i = cycleNext n hn j) ↔ (j = cyclePrev n hn i) from
        eq_cycleNext_iff_cyclePrev n hn i j]
    by_cases h1 : j = cycleNext n hn i <;> by_cases h2 : j = cyclePrev n hn i
    · exfalso
      have := cycleNext_not_both n hn i (cycleNext n hn i) rfl
      rw [← h1, h2, cycleNext_cyclePrev] at this; exact this rfl
    · simp only [if_pos h1, if_neg h2]; ring
    · simp only [if_neg h1, if_pos h2]; ring
    · simp only [if_neg h1, if_neg h2, mul_zero, zero_add]
  simp_rw [this, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ _ (fun _ => 1 / (n : ℝ) ^ 2),
    Finset.mem_univ, ite_true]
  ring

/-- Energy of the harmonic form on C_n equals 1/n.
    Computation: n forward edges, each contributing (1/n)² twice (once per orientation),
    times the ½ factor: ½ · n · 2 · (1/n)² = 1/n. -/
theorem cycleHarmonicForm_energy (n : ℕ) (hn : n ≥ 3) :
    energy (cycleHarmonicForm n hn) = 1 / n := by
  simp only [energy, innerC1]
  simp_rw [energy_inner_sum n hn]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- Winding number of a 1-cochain around the n-cycle:
    the sum of σ along forward edges. -/
noncomputable def winding (n : ℕ) (hn : n ≥ 3) (σ : C1 (Fin n)) : ℝ :=
  ∑ i : Fin n, σ.val i (cycleNext n hn i)

theorem winding_smul (n : ℕ) (hn : n ≥ 3) (c : ℝ) (σ : C1 (Fin n)) :
    winding n hn (C1.smul c σ) = c * winding n hn σ := by
  simp only [winding, C1.smul, ← Finset.mul_sum]

theorem winding_add (n : ℕ) (hn : n ≥ 3) (σ τ : C1 (Fin n)) :
    winding n hn (C1.add σ τ) = winding n hn σ + winding n hn τ := by
  simp only [winding, C1.add, ← Finset.sum_add_distrib]

theorem winding_sub (n : ℕ) (hn : n ≥ 3) (σ τ : C1 (Fin n)) :
    winding n hn (C1.sub σ τ) = winding n hn σ - winding n hn τ := by
  simp only [winding, C1.sub, ← Finset.sum_sub_distrib]

/-- Exact forms have winding number 0 (telescoping sum). -/
theorem winding_exact (n : ℕ) (hn : n ≥ 3) (φ : C0 (Fin n)) :
    winding n hn (d0 φ) = 0 := by
  simp only [winding, d0]
  rw [Finset.sum_sub_distrib]
  have : ∑ x : Fin n, φ (cycleNext n hn x) = ∑ x, φ x :=
    Equiv.sum_comp (cycleNextEquiv n hn) φ
  linarith

/-- The harmonic form has winding number 1. -/
theorem cycleHarmonicForm_winding (n : ℕ) (hn : n ≥ 3) :
    winding n hn (cycleHarmonicForm n hn) = 1 := by
  simp only [winding, cycleHarmonicForm]
  simp only [if_true, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-! ### The Reproducing Kernel and Hodge Decomposition -/

/-- The inner sum ∑ⱼ h(i,j)·σ(i,j) extracts the forward and backward edge values. -/
private lemma cross_inner_sum (n : ℕ) (hn : n ≥ 3) (σ : C1 (Fin n)) (i : Fin n) :
    ∑ j : Fin n, (cycleHarmonicForm n hn).val i j * σ.val i j =
    (σ.val i (cycleNext n hn i) - σ.val i (cyclePrev n hn i)) / ↑n := by
  simp only [cycleHarmonicForm]
  have : ∀ j : Fin n,
      (if j = cycleNext n hn i then (1 : ℝ) / ↑n
        else if i = cycleNext n hn j then -(1 : ℝ) / ↑n else 0) * σ.val i j =
      (if j = cycleNext n hn i then σ.val i j * (1 / ↑n) else 0) +
      (if j = cyclePrev n hn i then σ.val i j * (-(1 : ℝ) / ↑n) else 0) := by
    intro j
    simp only [show (i = cycleNext n hn j) ↔ (j = cyclePrev n hn i) from
        eq_cycleNext_iff_cyclePrev n hn i j]
    by_cases h1 : j = cycleNext n hn i <;> by_cases h2 : j = cyclePrev n hn i
    · exfalso; have := cycleNext_not_both n hn i (cycleNext n hn i) rfl
      rw [← h1, h2, cycleNext_cyclePrev] at this; exact this rfl
    · simp only [if_pos h1, if_neg h2]; ring
    · simp only [if_neg h1, if_pos h2]; ring
    · simp only [if_neg h1, if_neg h2, zero_mul, zero_add]
  simp_rw [this, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ _ (fun j => σ.val i j * (1 / ↑n)),
    Finset.sum_ite_eq' Finset.univ _ (fun j => σ.val i j * (-(1 : ℝ) / ↑n)),
    Finset.mem_univ, ite_true]
  ring

/-- **Reproducing kernel**: the inner product of h with any σ extracts
    its winding number, scaled by ‖h‖². This is the structural center of
    the Hodge theory — harmonicity is a corollary, not a separate fact. -/
theorem innerC1_cycleHarmonicForm (n : ℕ) (hn : n ≥ 3) (σ : C1 (Fin n)) :
    innerC1 (cycleHarmonicForm n hn) σ =
    winding n hn σ * energy (cycleHarmonicForm n hn) := by
  rw [cycleHarmonicForm_energy]
  simp only [innerC1, winding]
  simp_rw [cross_inner_sum n hn σ]
  rw [← Finset.sum_div]
  suffices ∑ i, (σ.val i (cycleNext n hn i) - σ.val i (cyclePrev n hn i)) =
      2 * ∑ i, σ.val i (cycleNext n hn i) by
    rw [this]; ring
  rw [Finset.sum_sub_distrib]
  -- The backward sum equals minus the forward sum: σ(i,prev(i)) = −σ(prev(i),i) by skew
  suffices ∑ i : Fin n, σ.val i (cyclePrev n hn i) =
      -(∑ i, σ.val i (cycleNext n hn i)) by linarith
  have key : ∀ i : Fin n, σ.val i (cyclePrev n hn i) =
      -(σ.val (cyclePrev n hn i) (cycleNext n hn (cyclePrev n hn i))) := by
    intro i; rw [cycleNext_cyclePrev]; exact σ.skew i (cyclePrev n hn i)
  simp_rw [key, Finset.sum_neg_distrib]
  congr 1
  exact Equiv.sum_comp (cycleNextEquiv n hn).symm
    (fun j => σ.val j (cycleNext n hn j))

/-- Harmonicity of the canonical form: orthogonal to all exact forms.
    Corollary of the reproducing kernel: exact forms have winding 0 (telescoping),
    so ⟨h, d₀φ⟩ = 0 · energy(h) = 0. -/
theorem cycleHarmonicForm_isHarmonic (n : ℕ) (hn : n ≥ 3) :
    IsHarmonic (cycleHarmonicForm n hn) := by
  intro φ
  rw [innerC1_comm, innerC1_cycleHarmonicForm, winding_exact, zero_mul]

/-- The winding-k harmonic form: k times the canonical harmonic form.
    This is the instanton (minimum-energy configuration) in topological sector k. -/
noncomputable def cycleHarmonicForm_k (n : ℕ) (hn : n ≥ 3) (k : ℤ) : C1 (Fin n) :=
  C1.smul (k : ℝ) (cycleHarmonicForm n hn)

theorem cycleHarmonicForm_k_winding (n : ℕ) (hn : n ≥ 3) (k : ℤ) :
    winding n hn (cycleHarmonicForm_k n hn k) = k := by
  simp only [cycleHarmonicForm_k, winding_smul, cycleHarmonicForm_winding, mul_one]

theorem cycleHarmonicForm_k_energy (n : ℕ) (hn : n ≥ 3) (k : ℤ) :
    energy (cycleHarmonicForm_k n hn k) = (k : ℝ) ^ 2 / n := by
  simp only [cycleHarmonicForm_k, energy_smul, cycleHarmonicForm_energy n hn]
  ring

/-- Energy is non-negative (sum of squares). -/
theorem energy_nonneg {V : Type*} [Fintype V] (σ : C1 V) : 0 ≤ energy σ := by
  simp only [energy, innerC1]
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  exact mul_self_nonneg (σ.val i j)

/-- **Positive definiteness**: energy is zero iff all components are zero. -/
theorem energy_eq_zero_iff {V : Type*} [Fintype V] (σ : C1 V) :
    energy σ = 0 ↔ ∀ i j : V, σ.val i j = 0 := by
  simp only [energy, innerC1]
  constructor
  · intro h
    have sum_zero : ∑ i : V, ∑ j : V, σ.val i j * σ.val i j = 0 :=
      (mul_eq_zero.mp h).resolve_left (by norm_num : (1 / 2 : ℝ) ≠ 0)
    intro i j
    have h_i := (Finset.sum_eq_zero_iff_of_nonneg (fun i' _ =>
        Finset.sum_nonneg (fun j' _ => mul_self_nonneg (σ.val i' j')))).mp sum_zero
        i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun j' _ =>
        mul_self_nonneg (σ.val i j'))).mp h_i j (Finset.mem_univ j))
  · intro h; simp [h]

/-- **Hodge decomposition (Pythagoras)**: energy decomposes into topology + overhead.

    For any cochain σ on the n-cycle with winding number w:
      energy(σ) = w²/n + energy(σ − w·h)
    The cross term vanishes by the reproducing kernel: ⟨h, σ − w·h⟩ = 0. -/
theorem hodge_decomposition (n : ℕ) (hn : n ≥ 3) (σ : C1 (Fin n)) :
    energy σ = (winding n hn σ) ^ 2 / n +
      energy (C1.sub σ (C1.smul (winding n hn σ) (cycleHarmonicForm n hn))) := by
  set w := winding n hn σ
  set h := cycleHarmonicForm n hn
  suffices energy (C1.sub σ (C1.smul w h)) = energy σ - w ^ 2 / ↑n by linarith
  rw [energy_sub, innerC1_comm, innerC1_smul_left, innerC1_cycleHarmonicForm,
      energy_smul, cycleHarmonicForm_energy, show winding n hn σ = w from rfl]
  ring

/-- The Hodge residual has winding number zero: all topology is in the harmonic part. -/
theorem hodge_residual_winding_zero (n : ℕ) (hn : n ≥ 3) (σ : C1 (Fin n)) :
    winding n hn (C1.sub σ (C1.smul (winding n hn σ) (cycleHarmonicForm n hn))) = 0 := by
  rw [winding_sub, winding_smul, cycleHarmonicForm_winding, mul_one, sub_self]

/-- **Hodge orthogonality**: the harmonic form is orthogonal to the residual.
    This is the structural content that produces the energy decomposition. -/
theorem hodge_orthogonality (n : ℕ) (hn : n ≥ 3) (σ : C1 (Fin n)) :
    innerC1 (cycleHarmonicForm n hn)
      (C1.sub σ (C1.smul (winding n hn σ) (cycleHarmonicForm n hn))) = 0 := by
  rw [innerC1_cycleHarmonicForm, hodge_residual_winding_zero, zero_mul]

/-- Energy bound: any cochain on Cₙ has energy ≥ w²/n.
    Immediate from Hodge decomposition + non-negativity of residual energy. -/
theorem energy_ge_winding_sq (n : ℕ) (hn : n ≥ 3) (σ : C1 (Fin n)) :
    energy σ ≥ (winding n hn σ) ^ 2 / n := by
  linarith [hodge_decomposition n hn σ,
    energy_nonneg (C1.sub σ (C1.smul (winding n hn σ) (cycleHarmonicForm n hn)))]

/-- **Uniqueness of the instanton**: if a cochain achieves minimum energy in its
    winding class, it IS the scaled harmonic form. Each topological sector has
    exactly one ground state. -/
theorem hodge_minimizer_eq (n : ℕ) (hn : n ≥ 3) (σ : C1 (Fin n))
    (hmin : energy σ = (winding n hn σ) ^ 2 / n) :
    σ.val = (C1.smul (winding n hn σ) (cycleHarmonicForm n hn)).val := by
  have hres : energy (C1.sub σ (C1.smul (winding n hn σ) (cycleHarmonicForm n hn))) = 0 := by
    linarith [hodge_decomposition n hn σ,
      energy_nonneg (C1.sub σ (C1.smul (winding n hn σ) (cycleHarmonicForm n hn)))]
  have hzero := (energy_eq_zero_iff _).mp hres
  funext i j
  have := hzero i j
  simp only [C1.sub] at this
  linarith

/-- Harmonic energy of the n-cycle: minimum energy over cochains with winding number 1.
    This is the mass of the n-cycle in the Hodge-theoretic sense. -/
noncomputable def harmonicEnergy (n : ℕ) (hn : n ≥ 3) : ℝ :=
  ⨅ σ : { σ : C1 (Fin n) // winding n hn σ = 1 }, energy σ.val

/-- **The 1/n Mass Spectrum**: harmonicEnergy of C_n equals 1/n.
    Upper bound: cycleHarmonicForm achieves 1/n.
    Lower bound: Hodge decomposition gives energy ≥ 1/n for any winding-1 cochain. -/
theorem cycleGraph_harmonicEnergy (n : ℕ) (hn : n ≥ 3) :
    harmonicEnergy n hn = 1 / n := by
  haveI : Nonempty { σ : C1 (Fin n) // winding n hn σ = 1 } :=
    ⟨⟨cycleHarmonicForm n hn, cycleHarmonicForm_winding n hn⟩⟩
  apply le_antisymm
  · have hbdd : BddBelow (Set.range (fun σ : { σ : C1 (Fin n) // winding n hn σ = 1 } =>
        energy σ.val)) := ⟨0, by rintro _ ⟨⟨σ, -⟩, rfl⟩; exact energy_nonneg σ⟩
    exact ciInf_le_of_le hbdd
      ⟨cycleHarmonicForm n hn, cycleHarmonicForm_winding n hn⟩
      (le_of_eq (cycleHarmonicForm_energy n hn))
  · exact le_ciInf fun ⟨σ, hw⟩ => by
      have := energy_ge_winding_sq n hn σ; rw [hw, one_pow] at this; exact this

/-- Minimum energy over cochains with winding number k on the n-cycle.
    Generalizes `harmonicEnergy` from winding-1 to arbitrary sector k. -/
noncomputable def harmonicEnergy_k (n : ℕ) (hn : n ≥ 3) (k : ℤ) : ℝ :=
  ⨅ σ : { σ : C1 (Fin n) // winding n hn σ = (k : ℝ) }, energy σ.val

/-- **The k²/n instanton spectrum**: minimum energy over winding-k cochains is k²/n.
    Upper bound: `cycleHarmonicForm_k` achieves k²/n.
    Lower bound: Hodge decomposition (`energy_ge_winding_sq`) gives energy ≥ w²/n. -/
theorem cycleGraph_harmonicEnergy_k (n : ℕ) (hn : n ≥ 3) (k : ℤ) :
    harmonicEnergy_k n hn k = (k : ℝ) ^ 2 / n := by
  haveI : Nonempty { σ : C1 (Fin n) // winding n hn σ = (k : ℝ) } :=
    ⟨⟨cycleHarmonicForm_k n hn k, cycleHarmonicForm_k_winding n hn k⟩⟩
  apply le_antisymm
  · have hbdd : BddBelow (Set.range (fun σ : { σ : C1 (Fin n) // winding n hn σ = (k : ℝ) } =>
        energy σ.val)) := ⟨0, by rintro _ ⟨⟨σ, -⟩, rfl⟩; exact energy_nonneg σ⟩
    exact ciInf_le_of_le hbdd
      ⟨cycleHarmonicForm_k n hn k, cycleHarmonicForm_k_winding n hn k⟩
      (le_of_eq (cycleHarmonicForm_k_energy n hn k))
  · exact le_ciInf fun ⟨σ, hw⟩ => by have := energy_ge_winding_sq n hn σ; rw [hw] at this; exact this

end Hodge

/-! ## Path Integral: Partition Function over Topological Sectors -/

section PathIntegral

open Finset BigOperators

private lemma summable_exp_neg_sq_div (n : ℕ) (hn : n ≥ 3) :
    Summable (fun i : ℕ => Real.exp (-(↑i : ℝ) ^ 2 / ↑n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc : -(1 : ℝ) / ↑n < 0 := by rw [neg_div]; exact neg_lt_zero.mpr (div_pos one_pos hn0)
  have hle : ∀ i : ℕ, (↑i : ℝ) ≤ (↑i : ℝ) ^ 2 := by
    intro i; rcases i with _ | i
    · simp
    · nlinarith [sq_nonneg ((↑(i + 1) : ℝ) - 1),
        show (1 : ℝ) ≤ ↑(i + 1) from by exact_mod_cast Nat.succ_pos i]
  refine (Real.summable_exp_nat_mul_of_ge hc (f := fun i => (↑i : ℝ) ^ 2) hle).congr ?_
  intro i; congr 1; field_simp

theorem summable_partitionFn (n : ℕ) (hn : n ≥ 3) :
    Summable (fun k : ℤ => Real.exp (-(k : ℝ) ^ 2 / ↑n)) :=
  .of_nat_of_neg (summable_exp_neg_sq_div n hn)
    ((summable_exp_neg_sq_div n hn).congr fun i => by push_cast; congr 1; ring)

/-- The partition function of the n-cycle: Z(Cₙ) = Σ_{k∈ℤ} exp(-k²/n).
    Sums Boltzmann weights over topological sectors (winding number k),
    each weighted by the instanton action k²/n. A Jacobi theta function ϑ₃(0, e^{-1/n}). -/
noncomputable def partitionFn (n : ℕ) (_ : n ≥ 3) : ℝ :=
  ∑' (k : ℤ), Real.exp (-(k : ℝ) ^ 2 / ↑n)

theorem partitionFn_pos (n : ℕ) (hn : n ≥ 3) : 0 < partitionFn n hn := by
  unfold partitionFn
  calc 0 < Real.exp (-(0 : ℤ) ^ 2 / ↑n) := Real.exp_pos _
    _ ≤ _ := (summable_partitionFn n hn).le_tsum 0 (fun k _ => le_of_lt (Real.exp_pos _))

/-- The vacuum (k=0) sector contributes exp(0) = 1.
    Particles (k ≠ 0) are exponentially suppressed. -/
theorem partitionFn_ge_one (n : ℕ) (hn : n ≥ 3) : partitionFn n hn ≥ 1 := by
  unfold partitionFn
  have h := (summable_partitionFn n hn).le_tsum (0 : ℤ)
    (fun k _ => le_of_lt (Real.exp_pos _))
  simp at h; linarith

/-- Nonzero sectors are exponentially suppressed relative to vacuum:
    each has weight strictly less than 1. -/
theorem sector_weight_lt_one_of_ne_zero (n : ℕ) (hn : n ≥ 3) {k : ℤ} (hk : k ≠ 0) :
    Real.exp (-(k : ℝ) ^ 2 / ↑n) < 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hk0 : (0 : ℝ) < (k : ℝ) ^ 2 := by
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    exact sq_pos_of_ne_zero hk'
  have hneg : -(k : ℝ) ^ 2 / ↑n < 0 := by
    have hpos : (k : ℝ) ^ 2 / ↑n > 0 := div_pos hk0 hn0
    have hneg' : -((k : ℝ) ^ 2 / ↑n) < 0 := neg_neg_of_pos hpos
    simpa [neg_div] using hneg'
  calc Real.exp (-(k : ℝ) ^ 2 / ↑n) < Real.exp 0 := Real.exp_lt_exp.mpr hneg
    _ = 1 := by simp

/-- Each topological sector k contributes the Boltzmann weight
    of the instanton action k²/n. -/
theorem sector_weight (n : ℕ) (hn : n ≥ 3) (k : ℤ) :
    Real.exp (-(k : ℝ) ^ 2 / ↑n) =
    Real.exp (-(energy (cycleHarmonicForm_k n hn k))) := by
  rw [cycleHarmonicForm_k_energy]; congr 1; ring

/-- The Boltzmann weight of sector k equals exp(−minimum energy in sector k).
    This is the proper statistical-mechanical statement: each term in the partition
    function is weighted by the instanton action, which is the infimum over all
    cochains in that topological sector. -/
theorem sector_weight_eq_min_energy (n : ℕ) (hn : n ≥ 3) (k : ℤ) :
    Real.exp (-(k : ℝ) ^ 2 / ↑n) = Real.exp (-(harmonicEnergy_k n hn k)) := by
  rw [cycleGraph_harmonicEnergy_k]; congr 1; ring

end PathIntegral

/-! ## Edge-Restricted Cochains and b₁ -/

section EdgeHodge

open Finset BigOperators

/-- Edge-supported 1-cochains: skew-symmetric functions vanishing on non-edges. -/
structure EC1 (G : Graph V) where
  val : V → V → ℝ
  skew : ∀ i j, val i j = -val j i
  support : ∀ i j, ¬G.edge i j → val i j = 0

/-- The underlying C1 of an edge-supported cochain. -/
def EC1.toC1 {G : Graph V} (σ : EC1 G) : C1 V where
  val := σ.val
  skew := σ.skew

/-- Divergence at a vertex: Σ_w σ(v,w). -/
noncomputable def EC1.div [Fintype V] {G : Graph V} (σ : EC1 G) (v : V) : ℝ :=
  ∑ w : V, σ.val v w

/-- Harmonic = divergence-free at every vertex. -/
def EC1.IsHarmonic [Fintype V] {G : Graph V} (σ : EC1 G) : Prop :=
  ∀ v : V, σ.div v = 0

/-! ### Cycle graph edge structure -/

/-- On C_n, non-adjacent means neither next nor prev. -/
private lemma cycleGraph_not_edge (n : ℕ) (hn : n ≥ 3) (i j : Fin n)
    (h1 : j ≠ cycleNext n hn i) (h2 : j ≠ cyclePrev n hn i) :
    ¬(CycleGraph n hn).edge i j := by
  simp only [CycleGraph]; push_neg
  exact ⟨h1, fun h => h2 ((eq_cycleNext_iff_cyclePrev n hn i j).mp h)⟩

/-- next(i) ≠ prev(i) for n ≥ 3. -/
private lemma cycleNext_ne_cyclePrev (n : ℕ) (hn : n ≥ 3) (i : Fin n) :
    cycleNext n hn i ≠ cyclePrev n hn i := by
  intro h
  have h2 := congr_arg (cycleNext n hn) h
  rw [cycleNext_cyclePrev] at h2
  have h3 := congr_arg Fin.val h2
  simp only [cycleNext, Fin.val_mk] at h3
  have hi := i.isLt
  by_cases h4 : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt h4] at h3
    by_cases h5 : i.val + 2 < n
    · rw [Nat.mod_eq_of_lt h5] at h3; omega
    · rw [show i.val + 1 + 1 = n by omega, Nat.mod_self] at h3; omega
  · rw [show i.val + 1 = n by omega, Nat.mod_self,
        Nat.mod_eq_of_lt (show 1 < n by omega)] at h3; omega

/-- On C_n, divergence of an EC1 at vertex i reduces to two neighbor terms. -/
private theorem cycleEC1_div_eq (n : ℕ) (hn : n ≥ 3)
    (σ : EC1 (CycleGraph n hn).toGraph) (i : Fin n) :
    σ.div i = σ.val i (cycleNext n hn i) + σ.val i (cyclePrev n hn i) := by
  simp only [EC1.div]
  have hne := cycleNext_ne_cyclePrev n hn i
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (cycleNext n hn i))]
  congr 1
  have hmem : cyclePrev n hn i ∈ Finset.univ.erase (cycleNext n hn i) :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ hmem]
  have : ∑ x ∈ (Finset.univ.erase (cycleNext n hn i)).erase (cyclePrev n hn i),
      σ.val i x = 0 := by
    apply Finset.sum_eq_zero
    intro w hw; simp [Finset.mem_erase] at hw
    exact σ.support i w (cycleGraph_not_edge n hn i w hw.2 hw.1)
  linarith

/-- Shift invariance: divergence-free forces constant value on forward edges. -/
private theorem cycleEC1_harmonic_shift (n : ℕ) (hn : n ≥ 3)
    (σ : EC1 (CycleGraph n hn).toGraph) (hσ : σ.IsHarmonic) (i : Fin n) :
    σ.val (cycleNext n hn i) (cycleNext n hn (cycleNext n hn i)) =
    σ.val i (cycleNext n hn i) := by
  have hdiv := cycleEC1_div_eq n hn σ (cycleNext n hn i)
  rw [hσ, cyclePrev_cycleNext] at hdiv
  linarith [σ.skew (cycleNext n hn i) i]

/-- By iterating the shift, forward-edge values are constant across all vertices. -/
private theorem cycleEC1_harmonic_shift_iter (n : ℕ) (hn : n ≥ 3)
    (σ : EC1 (CycleGraph n hn).toGraph) (hσ : σ.IsHarmonic) (k : ℕ) (i : Fin n) :
    σ.val ((cycleNext n hn)^[k] i) (cycleNext n hn ((cycleNext n hn)^[k] i)) =
    σ.val i (cycleNext n hn i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp]
    rw [cycleEC1_harmonic_shift n hn σ hσ]
    exact ih

/-- On C_n, harmonic edge-supported forms are constant on forward edges. -/
theorem cycleEC1_harmonic_constant (n : ℕ) (hn : n ≥ 3)
    (σ : EC1 (CycleGraph n hn).toGraph) (hσ : σ.IsHarmonic) (i : Fin n) :
    σ.val i (cycleNext n hn i) =
    σ.val (⟨0, by omega⟩ : Fin n) (cycleNext n hn ⟨0, by omega⟩) := by
  -- Every vertex i = next^[i.val](0)
  have hi : i = (cycleNext n hn)^[i.val] ⟨0, by omega⟩ := by
    ext; rw [cycleNext_iterate_val]; simp [Nat.mod_eq_of_lt i.isLt]
  rw [hi]
  exact cycleEC1_harmonic_shift_iter n hn σ hσ i.val ⟨0, by omega⟩

/-- Winding of a harmonic EC1 on C_n equals n times the forward-edge constant. -/
theorem cycleEC1_harmonic_winding (n : ℕ) (hn : n ≥ 3)
    (σ : EC1 (CycleGraph n hn).toGraph) (hσ : σ.IsHarmonic) :
    winding n hn σ.toC1 =
    ↑n * σ.val (⟨0, by omega⟩ : Fin n) (cycleNext n hn ⟨0, by omega⟩) := by
  simp only [winding, EC1.toC1]
  rw [show ∑ i, σ.val i (cycleNext n hn i) =
      ∑ _ : Fin n, σ.val ⟨0, by omega⟩ (cycleNext n hn ⟨0, by omega⟩) from
    Finset.sum_congr rfl fun i _ => cycleEC1_harmonic_constant n hn σ hσ i]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- **Harmonic uniqueness on C_n**: every harmonic edge-supported form equals
    its winding number times the canonical harmonic form.
    This is the concrete content of b₁(C_n) = 1. -/
theorem cycleEC1_harmonic_eq_smul (n : ℕ) (hn : n ≥ 3)
    (σ : EC1 (CycleGraph n hn).toGraph) (hσ : σ.IsHarmonic) :
    σ.val = (C1.smul (winding n hn σ.toC1) (cycleHarmonicForm n hn)).val := by
  funext i j
  simp only [C1.smul, cycleHarmonicForm]
  by_cases hf : j = cycleNext n hn i
  · subst hf
    rw [if_pos rfl, cycleEC1_harmonic_constant n hn σ hσ i,
        cycleEC1_harmonic_winding n hn σ hσ]
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  · by_cases hb : i = cycleNext n hn j
    · rw [if_neg hf, if_pos hb]
      -- σ(i,j) = -σ(j,i) and i = next(j), so σ(j,i) = σ(j, next(j)) = c
      have hskew := σ.skew i j
      have hconst := cycleEC1_harmonic_constant n hn σ hσ j
      have hwinding := cycleEC1_harmonic_winding n hn σ hσ
      -- σ(j, next(j)) = σ(j, i) since i = next(j)
      have hji : σ.val j i = σ.val j (cycleNext n hn j) := by rw [hb]
      rw [hskew, hji, hconst, hwinding]
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp
    · rw [if_neg hf, if_neg hb, mul_zero]
      exact σ.support i j (by simp only [CycleGraph]; push_neg; exact ⟨hf, hb⟩)

end EdgeHodge

/-! ## Complex Intersection -/

/-- Intersection of two complexes: edges and faces present in both. -/
def Complex.inter (C₁ C₂ : Complex V) : Complex V where
  edge := fun v w => C₁.edge v w ∧ C₂.edge v w
  face := fun a b c => C₁.face a b c ∧ C₂.face a b c
  face_closed := by
    intro a b c ⟨h₁, h₂⟩
    exact ⟨⟨(C₁.face_closed a b c h₁).1, (C₂.face_closed a b c h₂).1⟩,
           ⟨(C₁.face_closed a b c h₁).2.1, (C₂.face_closed a b c h₂).2.1⟩,
           ⟨(C₁.face_closed a b c h₁).2.2, (C₂.face_closed a b c h₂).2.2⟩⟩
  face_cycle := fun a b c ⟨h₁, h₂⟩ =>
    ⟨C₁.face_cycle a b c h₁, C₂.face_cycle a b c h₂⟩

/-! ## Mayer-Vietoris -/

section MayerVietoris

open Classical Finset

variable [Fintype V] [DecidableEq V]

/-- The set of ordered edge pairs. -/
noncomputable def Complex.edgeFinset (C : Complex V) : Finset (V × V) :=
  Finset.univ.filter (fun p => C.edge p.1 p.2)

/-- Edge set of union = union of edge sets. -/
theorem edgeFinset_union (C₁ C₂ : Complex V) :
    (C₁.union C₂).edgeFinset = C₁.edgeFinset ∪ C₂.edgeFinset := by
  ext p; simp [Complex.edgeFinset, Complex.union, Finset.mem_union, Finset.mem_filter]

/-- Edge set of intersection = intersection of edge sets. -/
theorem edgeFinset_inter (C₁ C₂ : Complex V) :
    (C₁.inter C₂).edgeFinset = C₁.edgeFinset ∩ C₂.edgeFinset := by
  ext p; simp [Complex.edgeFinset, Complex.inter, Finset.mem_inter, Finset.mem_filter]

/-- Inclusion-exclusion for edge counts. -/
theorem edgeCount_inclusion_exclusion (C₁ C₂ : Complex V) :
    (C₁.union C₂).edgeFinset.card + (C₁.inter C₂).edgeFinset.card =
    C₁.edgeFinset.card + C₂.edgeFinset.card := by
  rw [edgeFinset_union, edgeFinset_inter]
  exact Finset.card_union_add_card_inter _ _

/-- First Betti number (×2, using ordered edge pairs to avoid division).
    For connected graphs with symmetric edges, this is 2·(|E| − |V| + 1). -/
noncomputable def bettiOneZ (C : Complex V) : ℤ :=
  (C.edgeFinset.card : ℤ) - 2 * (Fintype.card V : ℤ) + 2

/-- **Mayer-Vietoris for b₁**: the structural economy of merging complexes. -/
theorem bettiOneZ_mayer_vietoris (C₁ C₂ : Complex V) :
    bettiOneZ (C₁.union C₂) + bettiOneZ (C₁.inter C₂) =
    bettiOneZ C₁ + bettiOneZ C₂ := by
  unfold bettiOneZ
  have h := edgeCount_inclusion_exclusion C₁ C₂
  linarith [h]

/-- b₁ with union/intersection instantiates structured gravity. -/
noncomputable instance [Fintype V] : SGD.StructuredComplexity (Complex V) ℤ where
  K := bettiOneZ
  merge := Complex.union
  overlap := Complex.inter
  merge_overlap := bettiOneZ_mayer_vietoris

end MayerVietoris

/-! ## Bridge: Edge Counting meets Hodge Theory -/

section CycleBridge

open Finset

/-- The cycle graph has exactly 2n ordered edges. -/
theorem cycleGraph_edgeFinset_card (n : ℕ) (hn : n ≥ 3) :
    (CycleGraph n hn).edgeFinset.card = 2 * n := by
  have inj_fwd : Function.Injective (fun i : Fin n => (i, cycleNext n hn i)) :=
    fun a b h => (Prod.mk.inj h).1
  have inj_bwd : Function.Injective (fun i : Fin n => (i, cyclePrev n hn i)) :=
    fun a b h => (Prod.mk.inj h).1
  -- Edge set decomposes into forward and backward images
  have h_eq : (CycleGraph n hn).edgeFinset =
      univ.image (fun i : Fin n => (i, cycleNext n hn i)) ∪
      univ.image (fun i : Fin n => (i, cyclePrev n hn i)) := by
    ext ⟨i, j⟩
    simp only [Complex.edgeFinset, CycleGraph, mem_filter, mem_univ, true_and,
               mem_union, mem_image, Prod.mk.injEq]
    constructor
    · rintro (rfl | h)
      · exact Or.inl ⟨i, rfl, rfl⟩
      · exact Or.inr ⟨i, rfl, ((eq_cycleNext_iff_cyclePrev n hn i j).mp h).symm⟩
    · rintro (⟨k, rfl, rfl⟩ | ⟨k, rfl, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ((eq_cycleNext_iff_cyclePrev n hn k (cyclePrev n hn k)).mpr rfl)
  -- Forward and backward images are disjoint
  have h_disj : Disjoint
      (univ.image (fun i : Fin n => (i, cycleNext n hn i)))
      (univ.image (fun i : Fin n => (i, cyclePrev n hn i))) := by
    rw [Finset.disjoint_left]
    intro p hf hb
    simp only [mem_image, mem_univ, true_and] at hf hb
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb'⟩ := hb
    have heq := ha.trans hb'.symm
    have h1 : a = b := congr_arg Prod.fst heq
    have h2 : cycleNext n hn a = cyclePrev n hn b := congr_arg Prod.snd heq
    subst h1
    exact absurd h2 (cycleNext_ne_cyclePrev n hn a)
  rw [h_eq, card_union_of_disjoint h_disj,
      card_image_of_injective _ inj_fwd, card_image_of_injective _ inj_bwd,
      card_univ, Fintype.card_fin]
  omega

/-- **Bridge theorem**: bettiOneZ of the cycle graph equals 2.
    Since `cycleEC1_harmonic_eq_smul` proves the harmonic subspace of C_n is
    1-dimensional (b₁ = 1), this confirms bettiOneZ = 2 · b₁ on cycle graphs,
    linking the edge-counting formula to the Hodge-theoretic Betti number. -/
theorem bettiOneZ_cycleGraph (n : ℕ) (hn : n ≥ 3) :
    bettiOneZ (CycleGraph n hn) = 2 := by
  simp only [bettiOneZ, cycleGraph_edgeFinset_card, Fintype.card_fin]; omega

/-- The cycle graph is symmetric: every edge has a reverse. -/
theorem cycleGraph_symmetric (n : ℕ) (hn : n ≥ 3) :
    (CycleGraph n hn).toGraph.Symmetric := by
  intro i j h; exact h.symm

/-- The cycle graph is irreflexive: no self-loops. -/
theorem cycleGraph_irreflexive (n : ℕ) (hn : n ≥ 3) :
    (CycleGraph n hn).toGraph.Irreflexive := by
  intro i h
  simp only [CycleGraph] at h
  rcases h with heq | heq
  · exact (cycleNext_not_both n hn i i heq) heq
  · exact (cycleNext_not_both n hn i i heq) heq

end CycleBridge

/-! ## Complex Products -/

section Products

variable {V₁ V₂ : Type u}

/-- Product of two complexes: edges in either factor (cylinder edges),
    faces from prism decomposition (face × vertex or vertex × face). -/
def Complex.prod (C₁ : Complex V₁) (C₂ : Complex V₂) : Complex (V₁ × V₂) where
  edge := fun p q => (C₁.edge p.1 q.1 ∧ p.2 = q.2) ∨ (p.1 = q.1 ∧ C₂.edge p.2 q.2)
  face := fun p q r =>
    -- Prism decomposition: face in one factor, vertex fixed in the other
    (C₁.face p.1 q.1 r.1 ∧ p.2 = q.2 ∧ q.2 = r.2) ∨
    (p.1 = q.1 ∧ q.1 = r.1 ∧ C₂.face p.2 q.2 r.2)
  face_closed := by
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ hf
    rcases hf with ⟨hf₁, ha, hb⟩ | ⟨ha, hb, hf₂⟩
    · obtain ⟨e₁, e₂, e₃⟩ := C₁.face_closed a₁ b₁ c₁ hf₁
      exact ⟨Or.inl ⟨e₁, ha⟩, Or.inl ⟨e₂, hb⟩, Or.inl ⟨e₃, ha.trans hb⟩⟩
    · obtain ⟨e₁, e₂, e₃⟩ := C₂.face_closed a₂ b₂ c₂ hf₂
      exact ⟨Or.inr ⟨ha, e₁⟩, Or.inr ⟨hb, e₂⟩, Or.inr ⟨ha.trans hb, e₃⟩⟩
  face_cycle := by
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ hf
    rcases hf with ⟨hf₁, ha, hb⟩ | ⟨ha, hb, hf₂⟩
    · exact Or.inl ⟨C₁.face_cycle a₁ b₁ c₁ hf₁, hb, (ha.trans hb).symm⟩
    · exact Or.inr ⟨hb, (ha.trans hb).symm, C₂.face_cycle a₂ b₂ c₂ hf₂⟩

open Classical Finset in
/-- Edge count of a product complex: edges decompose into factor-1 edges × V₂ and V₁ × factor-2 edges.
    Disjointness follows from irreflexivity of C₁ (an edge in both factors would require a self-loop). -/
theorem prod_edgeFinset_card [Fintype V₁] [Fintype V₂] [DecidableEq V₁] [DecidableEq V₂]
    (C₁ : Complex V₁) (C₂ : Complex V₂)
    (hirr : C₁.toGraph.Irreflexive) :
    (C₁.prod C₂).edgeFinset.card =
      C₁.edgeFinset.card * Fintype.card V₂ + Fintype.card V₁ * C₂.edgeFinset.card := by
  -- Define the two image sets
  let S₁ := univ.filter (fun p : (V₁ × V₂) × (V₁ × V₂) => C₁.edge p.1.1 p.2.1 ∧ p.1.2 = p.2.2)
  let S₂ := univ.filter (fun p : (V₁ × V₂) × (V₁ × V₂) => p.1.1 = p.2.1 ∧ C₂.edge p.1.2 p.2.2)
  -- Edge set is the union
  have h_eq : (C₁.prod C₂).edgeFinset = S₁ ∪ S₂ := by
    ext ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩
    simp [Complex.edgeFinset, Complex.prod, S₁, S₂, mem_filter, mem_union]
  -- The two sets are disjoint by irreflexivity
  have h_disj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]; intro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ h1 h2
    simp [S₁, S₂, mem_filter] at h1 h2
    exact hirr a₁ (h2.1 ▸ h1.1)
  -- S₁ bijects with edgeFinset C₁ × V₂
  have h_card₁ : S₁.card = C₁.edgeFinset.card * Fintype.card V₂ := by
    have : S₁ = (C₁.edgeFinset ×ˢ univ).image
        (fun p : (V₁ × V₁) × V₂ => ((p.1.1, p.2), (p.1.2, p.2))) := by
      ext ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩
      simp [S₁, Complex.edgeFinset, mem_filter, mem_image, mem_product]
    rw [this, card_image_of_injective]
    · rw [card_product, card_univ]
    · intro ⟨⟨a₁, a₂⟩, v₁⟩ ⟨⟨b₁, b₂⟩, v₂⟩ h
      simp at h; ext <;> simp_all
  -- S₂ bijects with V₁ × edgeFinset C₂
  have h_card₂ : S₂.card = Fintype.card V₁ * C₂.edgeFinset.card := by
    have : S₂ = (univ ×ˢ C₂.edgeFinset).image
        (fun p : V₁ × (V₂ × V₂) => ((p.1, p.2.1), (p.1, p.2.2))) := by
      ext ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩
      simp [S₂, Complex.edgeFinset, mem_filter, mem_image, mem_product, and_comm]
    rw [this, card_image_of_injective]
    · rw [card_product, card_univ]
    · intro ⟨v₁, ⟨a₁, a₂⟩⟩ ⟨v₂, ⟨b₁, b₂⟩⟩ h
      simp at h; ext <;> simp_all
  rw [h_eq, card_union_of_disjoint h_disj, h_card₁, h_card₂]

end Products

/-! ## Dynamics: The Homotopy Ratchet -/

section Dynamics

variable {V : Type u}

/-- Homotopy class of walks: the quotient by homotopy equivalence. -/
def HomotopyClass₂ (C : Complex V) (u v : V) :=
  Quot (Homotopic₂ C (u := u) (v := v))

/-- The quotient map from walks to homotopy classes. -/
def Walk.toHomotopyClass₂ (C : Complex V) (p : Walk C.toGraph u v) :
    HomotopyClass₂ C u v :=
  Quot.mk _ p

/-- Any bidirectional edge makes the quotient map non-injective:
    the backtrack v→w→v is homotopic to nil, but they're distinct walks. -/
theorem homotopyClass₂_non_injective (C : Complex V)
    {v w : V} (h_edge : C.edge v w) (h_back : C.edge w v) :
    ∃ p q : Walk C.toGraph v v,
      Walk.toHomotopyClass₂ C p = Walk.toHomotopyClass₂ C q ∧ p ≠ q := by
  refine ⟨Walk.cons h_edge (Walk.cons h_back (Walk.nil v)), Walk.nil v, ?_, ?_⟩
  · exact Quot.sound (Homotopic₂.backtrack h_edge h_back _)
  · intro h
    have := congr_arg Walk.length h
    simp [Walk.length] at this

/-- The quotient map Walk → HomotopyClass is non-injective whenever
    the complex has a bidirectional edge (backtrack ≠ nil but same class). -/
theorem geodesic_computation_is_lossy (C : Complex V)
    {v w : V} (h_edge : C.edge v w) (h_back : C.edge w v) :
    ¬Function.Injective (Walk.toHomotopyClass₂ C (u := v) (v := v)) := by
  intro hinj
  have ⟨_, _, heq, hne⟩ := homotopyClass₂_non_injective C h_edge h_back
  exact hne (hinj heq)

/-- **The simplicial ratchet**: any section of the homotopy quotient map
    costs strictly more than the forward map. This is the formal bridge
    between the abstract arrow of time (TransitionComplexity) and the
    concrete simplicial model — non-injectivity of the quotient implies
    the cost asymmetry. -/
theorem simplicial_ratchet [inst : SGD.TransitionComplexity]
    (C : Complex V) {v w : V} (h_edge : C.edge v w) (h_back : C.edge w v)
    (r : HomotopyClass₂ C v v → Walk C.toGraph v v)
    (hr : ∀ x, Walk.toHomotopyClass₂ C (r x) = x) :
    inst.transitionCost r >
    inst.transitionCost (Walk.toHomotopyClass₂ C (u := v) (v := v)) :=
  inst.ratchet _ r hr (geodesic_computation_is_lossy C h_edge h_back)

end Dynamics

end Simplicial
