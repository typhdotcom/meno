import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic
import Meno.Basic
import Meno.InfoRatchet

/-! # The Simplicial Model

The walk substrate of the corroborating route: graphs, 2-complexes,
walks, homotopy, geodesic length, winding arithmetic on the cycle
graph, and the discrete Hodge theory the groupoid bridge consumes.
(Review #28: the standalone contractibility/geodesic-matter model,
the disk/hollow-triangle binding chapters, and the parity arguments
were consumerless pre-spine developments and are deleted; binding
and matter live on the spine, `Meno/Binding.lean`, `Meno/Matter.lean`.) -/

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

/-- Length is additive under concatenation. -/
@[simp] theorem Walk.length_append {G : Graph V} :
    (p : Walk G u v) → (q : Walk G v w) →
    (p.append q).length = p.length + q.length
  | .nil _, q => by simp [Walk.append, Walk.length]
  | .cons h p, q => by
      simp [Walk.append, Walk.length, Walk.length_append p q]
      omega


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

/-! ## Winding Arithmetic on `ZMod n` -/

/-- One edge step in `CycleGraph` adds `edgeDir` in `ZMod n`. -/
lemma edgeDir_zmod_step {n : ℕ} {hn : n ≥ 3} {i j : Fin n}
    (h : (CycleGraph n hn).edge i j) :
    (j : ZMod n) = (i : ZMod n) + (edgeDir n hn i j h : ℤ) := by
  rcases h with hf | hb
  · subst hf
    simp [edgeDir, cycleNext]
  · have hforw : (i : ZMod n) = (j : ZMod n) + (1 : ℤ) := by
      rw [hb]
      simp [cycleNext]
    have hnot : ¬j = cycleNext n hn i := cycleNext_not_both n hn j i hb
    have hed : edgeDir n hn i j (Or.inr hb) = -1 := by
      simp [edgeDir, hnot]
    calc
      (j : ZMod n) = (i : ZMod n) + (-1 : ℤ) := by
        calc
          (j : ZMod n) = (j : ZMod n) + (1 : ℤ) + (-1 : ℤ) := by ring
          _ = (i : ZMod n) + (-1 : ℤ) := by simp [hforw, add_assoc]
      _ = (i : ZMod n) + (edgeDir n hn i j (Or.inr hb) : ℤ) := by rw [hed]

/-- Endpoint formula: a walk's endpoint equals start plus total winding in `ZMod n`. -/
theorem Walk.endpoint_zmod_eq_start_add_winding {n : ℕ} {hn : n ≥ 3}
    {s t : Fin n} (p : Walk (CycleGraph n hn).toGraph s t) :
    (t : ZMod n) = (s : ZMod n) + (p.windingCount : ℤ) := by
  induction p with
  | nil _ => simp [Walk.windingCount]
  | @cons v w x h tail ih =>
    calc
      (x : ZMod n) = (w : ZMod n) + (tail.windingCount : ℤ) := ih
      _ = ((v : ZMod n) + (edgeDir n hn v w h : ℤ)) + (tail.windingCount : ℤ) := by
            rw [edgeDir_zmod_step (n := n) (hn := hn) h]
      _ = (v : ZMod n) + ((edgeDir n hn v w h : ℤ) + (tail.windingCount : ℤ)) := by
            abel
      _ = (v : ZMod n) + ((Walk.cons h tail).windingCount : ℤ) := by
            simp [Walk.windingCount]

/-- For a loop on `C_n`, winding count is divisible by `n`. -/
theorem Walk.windingCount_dvd_card {n : ℕ} {hn : n ≥ 3} {s : Fin n}
    (p : Walk (CycleGraph n hn).toGraph s s) :
    (n : ℤ) ∣ p.windingCount := by
  have hz : ((p.windingCount : ℤ) : ZMod n) = 0 := by
    have h := Walk.endpoint_zmod_eq_start_add_winding (n := n) (hn := hn) p
    have h' := congrArg (fun z : ZMod n => z - (s : ZMod n)) h
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h'.symm
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd p.windingCount n).1 hz

/-- Integer winding sector for loops on `C_n` (full turns, not edge count). -/
def Walk.loopWinding {n : ℕ} {hn : n ≥ 3} {s : Fin n}
    (p : Walk (CycleGraph n hn).toGraph s s) : ℤ :=
  p.windingCount / (n : ℤ)

/-- Loop edge winding decomposes as `loopWinding * n`. -/
theorem Walk.windingCount_eq_loopWinding_mul_card {n : ℕ} {hn : n ≥ 3} {s : Fin n}
    (p : Walk (CycleGraph n hn).toGraph s s) :
    p.windingCount = p.loopWinding * n := by
  unfold Walk.loopWinding
  simpa [mul_comm] using
    (Int.ediv_mul_cancel (Walk.windingCount_dvd_card (n := n) (hn := hn) p)).symm

/-- Loop winding sector is homotopy invariant on `C_n`. -/
theorem loopWinding_homotopy_invariant {n : ℕ} {hn : n ≥ 3} {s : Fin n}
    {p q : Walk (CycleGraph n hn).toGraph s s}
    (h : Homotopic₂ (CycleGraph n hn) p q) :
    p.loopWinding = q.loopWinding := by
  unfold Walk.loopWinding
  rw [windingCount_homotopy_invariant h]

/-- Winding count is additive under walk concatenation. -/
@[simp] theorem Walk.windingCount_append {n : ℕ} {hn : n ≥ 3}
    {s t r : Fin n}
    (p : Walk (CycleGraph n hn).toGraph s t)
    (q : Walk (CycleGraph n hn).toGraph t r) :
    (p.append q).windingCount = p.windingCount + q.windingCount := by
  induction p with
  | nil _ => simp [Walk.append, Walk.windingCount]
  | cons h tail ih =>
    simp [Walk.append, Walk.windingCount, ih, add_assoc]

/-- The trivial loop has zero winding sector. -/
@[simp] theorem Walk.loopWinding_nil {n : ℕ} {hn : n ≥ 3} {s : Fin n} :
    (Walk.nil s : Walk (CycleGraph n hn).toGraph s s).loopWinding = 0 := by
  simp [Walk.loopWinding, Walk.windingCount]

/-- Loop winding sector is additive under loop concatenation: the sector
map `loopWinding : (loops at s, append) → (ℤ, +)` is a monoid morphism.
Divisibility (`windingCount_dvd_card`) makes integer division exact. -/
theorem Walk.loopWinding_append {n : ℕ} {hn : n ≥ 3} {s : Fin n}
    (p q : Walk (CycleGraph n hn).toGraph s s) :
    (p.append q).loopWinding = p.loopWinding + q.loopWinding := by
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  show (p.append q).windingCount / (n : ℤ) = p.loopWinding + q.loopWinding
  rw [Walk.windingCount_append,
      Walk.windingCount_eq_loopWinding_mul_card p,
      Walk.windingCount_eq_loopWinding_mul_card q,
      ← add_mul, Int.mul_ediv_cancel _ hn0]

/-! ## Canonical Cycle Walk -/

/-- Repeat a loop by concatenation. -/
def Walk.repeatLoop {G : Graph V} {v : V} (p : Walk G v v) : ℕ → Walk G v v
  | 0 => Walk.nil v
  | k + 1 => p.append (Walk.repeatLoop p k)


/-- Winding count of a repeated cycle-graph loop. -/
theorem Walk.repeatLoop_windingCount {n : ℕ} {hn : n ≥ 3} {s : Fin n}
    (p : Walk (CycleGraph n hn).toGraph s s) :
    ∀ k : ℕ, (Walk.repeatLoop p k).windingCount = (k : ℤ) * p.windingCount
  | 0 => by simp [Walk.repeatLoop, Walk.windingCount]
  | k + 1 => by
      simp [Walk.repeatLoop, Walk.windingCount_append, repeatLoop_windingCount p k]
      ring

/-- Base vertex used for canonical cycle loops. -/
abbrev cycleBase (n : ℕ) (hn : n ≥ 3) : Fin n := ⟨0, by omega⟩

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

def Walk.castStart {G : Graph V} {a b c : V} (h : a = b) (p : Walk G a c) : Walk G b c :=
  h ▸ p

@[simp] lemma Walk.castEnd_length {G : Graph V} {a b c : V} (h : b = c) (p : Walk G a b) :
    (p.castEnd h).length = p.length := by subst h; rfl

@[simp] lemma Walk.castStart_length {G : Graph V} {a b c : V} (h : a = b) (p : Walk G a c) :
    (p.castStart h).length = p.length := by subst h; rfl

@[simp] lemma Walk.castEnd_windingCount {n : ℕ} {hn : n ≥ 3} {s t r : Fin n}
    (h : t = r) (p : Walk (CycleGraph n hn).toGraph s t) :
    (p.castEnd h).windingCount = p.windingCount := by subst h; rfl

@[simp] lemma Walk.castStart_windingCount {n : ℕ} {hn : n ≥ 3} {s t r : Fin n}
    (h : s = t) (p : Walk (CycleGraph n hn).toGraph s r) :
    (p.castStart h).windingCount = p.windingCount := by subst h; rfl

/-- No immediate cancellation pair `a→b→a` appears in the walk. -/
inductive Walk.NoBacktrack {G : Graph V} : Walk G u v → Prop
  | nil (a : V) : Walk.NoBacktrack (Walk.nil (G := G) a)
  | cons_nil {a b : V} (h : G.edge a b) :
      Walk.NoBacktrack (Walk.cons h (Walk.nil b))
  | cons_cons {a b c d : V}
      (h₁ : G.edge a b) (h₂ : G.edge b c) (tail : Walk G c d)
      (hneq : c ≠ a)
      (hrest : Walk.NoBacktrack (Walk.cons h₂ tail)) :
      Walk.NoBacktrack (Walk.cons h₁ (Walk.cons h₂ tail))

theorem Walk.NoBacktrack.tail {G : Graph V} {a b c : V}
    {h : G.edge a b} {p : Walk G b c}
    (hnb : Walk.NoBacktrack (Walk.cons h p)) :
    Walk.NoBacktrack p := by
  cases p with
  | nil _ =>
      exact Walk.NoBacktrack.nil _
  | @cons b c d h₂ tail =>
      cases hnb with
      | cons_cons _ _ _ _ hrest => exact hrest

lemma edgeDir_ne_zero {n : ℕ} {hn : n ≥ 3} {i j : Fin n}
    (h : (CycleGraph n hn).edge i j) :
    edgeDir n hn i j h ≠ 0 := by
  unfold edgeDir
  split <;> omega

lemma edgeDir_eq_of_not_backtrack {n : ℕ} {hn : n ≥ 3}
    {a b c : Fin n}
    (h₁ : (CycleGraph n hn).edge a b)
    (h₂ : (CycleGraph n hn).edge b c)
    (hneq : c ≠ a) :
    edgeDir n hn b c h₂ = edgeDir n hn a b h₁ := by
  rcases h₁ with hf₁ | hb₁
  · rcases h₂ with hf₂ | hb₂
    · simp [edgeDir, hf₁, hf₂]
    · exfalso
      have ha : a = cyclePrev n hn b :=
        (eq_cycleNext_iff_cyclePrev n hn b a).1 hf₁
      have hc : c = cyclePrev n hn b :=
        (eq_cycleNext_iff_cyclePrev n hn b c).1 hb₂
      exact hneq (hc.trans ha.symm)
  · rcases h₂ with hf₂ | hb₂
    · exfalso
      exact hneq (hf₂.trans hb₁.symm)
    · have hnot₁ : ¬b = cycleNext n hn a := cycleNext_not_both n hn b a hb₁
      have hnot₂ : ¬c = cycleNext n hn b := cycleNext_not_both n hn c b hb₂
      simp [edgeDir, hnot₁, hnot₂]

/-- Greedy normalization by canceling immediate backtracks at the head. -/
def Walk.normalizeCycle {n : ℕ} {hn : n ≥ 3}
    {s t : Fin n} :
    Walk (CycleGraph n hn).toGraph s t →
      Walk (CycleGraph n hn).toGraph s t
  | .nil _ => .nil _
  | .cons (v := v) (w := w) (x := x) h p =>
      match p.normalizeCycle with
      | .nil _ => .cons h (.nil _)
      | .cons (v := w) (w := z) (x := x) h₂ tail =>
          if hz : z = v then
            tail.castStart hz
          else
            .cons h (.cons h₂ tail)

theorem Walk.normalizeCycle_homotopic {n : ℕ} {hn : n ≥ 3}
    {s t : Fin n}
    (p : Walk (CycleGraph n hn).toGraph s t) :
    Homotopic₂ (CycleGraph n hn) p p.normalizeCycle := by
  induction p with
  | nil _ =>
      exact Homotopic₂.refl _
  | @cons v w x h tail ih =>
      simp [Walk.normalizeCycle]
      cases hnorm : tail.normalizeCycle with
      | nil =>
          simpa [hnorm] using (Homotopic₂.congr_cons h ih)
      | @cons w z x h₂ tail₂ =>
          by_cases hz : z = v
          · have ih' :
              Homotopic₂ (CycleGraph n hn) tail (Walk.cons h₂ tail₂) := by
                simpa [hnorm] using ih
            have hcons :
                Homotopic₂ (CycleGraph n hn)
                  (Walk.cons h tail)
                  (Walk.cons h (Walk.cons h₂ tail₂)) :=
              Homotopic₂.congr_cons h ih'
            subst hz
            exact hcons.trans (by simpa using (Homotopic₂.backtrack h h₂ tail₂))
          · have ih' :
              Homotopic₂ (CycleGraph n hn) tail (Walk.cons h₂ tail₂) := by
                simpa [hnorm] using ih
            simpa [hz] using (Homotopic₂.congr_cons h ih')

theorem Walk.normalizeCycle_windingCount {n : ℕ} {hn : n ≥ 3}
    {s t : Fin n}
    (p : Walk (CycleGraph n hn).toGraph s t) :
    p.normalizeCycle.windingCount = p.windingCount := by
  exact (windingCount_homotopy_invariant (Walk.normalizeCycle_homotopic p)).symm

theorem Walk.normalizeCycle_noBacktrack {n : ℕ} {hn : n ≥ 3}
    {s t : Fin n}
    (p : Walk (CycleGraph n hn).toGraph s t) :
    Walk.NoBacktrack p.normalizeCycle := by
  induction p with
  | nil a =>
      simpa [Walk.normalizeCycle] using Walk.NoBacktrack.nil (a := a)
  | @cons v w x h tail ih =>
      simp [Walk.normalizeCycle]
      cases hnorm : tail.normalizeCycle with
      | nil =>
          simpa [hnorm] using Walk.NoBacktrack.cons_nil h
      | @cons w z x h₂ tail₂ =>
          by_cases hz : z = v
          · have ih' : Walk.NoBacktrack (Walk.cons h₂ tail₂) := by
              simpa [hnorm] using ih
            subst hz
            simpa using (Walk.NoBacktrack.tail ih')
          · have ih' : Walk.NoBacktrack (Walk.cons h₂ tail₂) := by
              simpa [hnorm] using ih
            simpa [hz] using Walk.NoBacktrack.cons_cons h h₂ tail₂ (by simpa using hz) ih'

private def noBacktrack_dir_mul
    {n : ℕ} {hn : n ≥ 3}
    {a b d : Fin n}
    {h : (CycleGraph n hn).edge a b}
    {tail : Walk (CycleGraph n hn).toGraph b d}
    (hnb : Walk.NoBacktrack (Walk.cons h tail)) :
    (Walk.cons h tail).windingCount =
      edgeDir n hn a b h * (Walk.cons h tail).length :=
  match hnb with
  | .cons_nil h => by
      simp [Walk.windingCount, Walk.length]
  | .cons_cons h₁ h₂ tail hneq hrest => by
      have ih :
          (Walk.cons h₂ tail).windingCount =
            edgeDir n hn _ _ h₂ * (Walk.cons h₂ tail).length :=
        noBacktrack_dir_mul (h := h₂) (tail := tail) hrest
      have hdir : edgeDir n hn _ _ h₂ = edgeDir n hn _ _ h₁ :=
        edgeDir_eq_of_not_backtrack h₁ h₂ hneq
      calc
        (Walk.cons h₁ (Walk.cons h₂ tail)).windingCount
            = edgeDir n hn _ _ h₁ + (Walk.cons h₂ tail).windingCount := by
                simp [Walk.windingCount]
        _ = edgeDir n hn _ _ h₁ + edgeDir n hn _ _ h₂ * (Walk.cons h₂ tail).length := by
              rw [ih]
        _ = edgeDir n hn _ _ h₁ + edgeDir n hn _ _ h₁ * (Walk.cons h₂ tail).length := by
              rw [hdir]
        _ = edgeDir n hn _ _ h₁ * ((Walk.cons h₂ tail).length + 1) := by ring
        _ = edgeDir n hn _ _ h₁ * (Walk.cons h₁ (Walk.cons h₂ tail)).length := by
              simp [Walk.length]

theorem Walk.windingCount_eq_edgeDir_mul_length_of_noBacktrack_cons
    {n : ℕ} {hn : n ≥ 3}
    {a b d : Fin n}
    {h : (CycleGraph n hn).edge a b}
    {tail : Walk (CycleGraph n hn).toGraph b d}
    (hnb : Walk.NoBacktrack (Walk.cons h tail)) :
    (Walk.cons h tail).windingCount =
      edgeDir n hn a b h * (Walk.cons h tail).length :=
  noBacktrack_dir_mul hnb

theorem Walk.eq_nil_of_noBacktrack_windingCount_zero
    {n : ℕ} {hn : n ≥ 3} {s : Fin n}
    (p : Walk (CycleGraph n hn).toGraph s s)
    (hnb : Walk.NoBacktrack p)
    (h0 : p.windingCount = 0) :
    p = Walk.nil s := by
  cases p with
  | nil _ => rfl
  | cons h tail =>
      exfalso
      have hw :
          (Walk.cons h tail).windingCount =
            edgeDir n hn _ _ h * (Walk.cons h tail).length :=
        Walk.windingCount_eq_edgeDir_mul_length_of_noBacktrack_cons hnb
      have hm : edgeDir n hn _ _ h * (Walk.cons h tail).length = 0 := by
        rw [← hw]
        simpa using h0
      rcases Int.mul_eq_zero.mp hm with hdir0 | hlen0
      · exact (edgeDir_ne_zero h) hdir0
      · have hlenNat : (Walk.cons h tail).length = 0 := Int.ofNat_eq_zero.mp hlen0
        simp [Walk.length] at hlenNat

theorem cycleLoop_windingCount_zero_contractible
    (n : ℕ) (hn : n ≥ 3) (s : Fin n)
    (p : Walk (CycleGraph n hn).toGraph s s)
    (h0 : p.windingCount = 0) :
    Homotopic₂ (CycleGraph n hn) p (Walk.nil s) := by
  let q := p.normalizeCycle
  have hpq : Homotopic₂ (CycleGraph n hn) p q := Walk.normalizeCycle_homotopic p
  have hq0 : q.windingCount = 0 := by
    simpa [q, Walk.normalizeCycle_windingCount p] using h0
  have hqnb : Walk.NoBacktrack q := by
    simpa [q] using Walk.normalizeCycle_noBacktrack p
  have hqnil : q = Walk.nil s :=
    Walk.eq_nil_of_noBacktrack_windingCount_zero q hqnb hq0
  simpa [q, hqnil] using hpq

/-- The canonical one-turn loop based at `s`:
    `s → cycleNext s → ... → s` after exactly `n` forward steps. -/
def cycleWalkAt (n : ℕ) (hn : n ≥ 3) (s : Fin n) :
    Walk (CycleGraph n hn).toGraph s s :=
  (cycleForwardWalkAux n hn n s).2.castEnd
    ((cycleForwardWalkAux_fst n hn n _).trans (cycleNext_iterate_n n hn _))

/-- The canonical cycle walk at the distinguished basepoint. -/
def cycleWalk (n : ℕ) (hn : n ≥ 3) :
    Walk (CycleGraph n hn).toGraph (cycleBase n hn) (cycleBase n hn) :=
  cycleWalkAt n hn (cycleBase n hn)

theorem cycleWalk_length (n : ℕ) (hn : n ≥ 3) : (cycleWalk n hn).length = n := by
  simp [cycleWalk, cycleWalkAt, cycleForwardWalkAux_length]

theorem cycleWalk_windingCount (n : ℕ) (hn : n ≥ 3) :
    (cycleWalk n hn).windingCount = (n : ℤ) := by
  simp [cycleWalk, cycleWalkAt, cycleForwardWalkAux_windingCount]


theorem cycleWalkAt_windingCount (n : ℕ) (hn : n ≥ 3) (s : Fin n) :
    (cycleWalkAt n hn s).windingCount = (n : ℤ) := by
  simp [cycleWalkAt, cycleForwardWalkAux_windingCount]

/-- The canonical `k`-turn loop at vertex `s`. -/
def cycleTurnLoopNatAt (n : ℕ) (hn : n ≥ 3) (s : Fin n) (k : ℕ) :
    Walk (CycleGraph n hn).toGraph s s :=
  Walk.repeatLoop (cycleWalkAt n hn s) k


theorem cycleTurnLoopNatAt_windingCount (n : ℕ) (hn : n ≥ 3) (s : Fin n) (k : ℕ) :
    (cycleTurnLoopNatAt n hn s k).windingCount = (k * n : ℤ) := by
  simp [cycleTurnLoopNatAt, Walk.repeatLoop_windingCount, cycleWalkAt_windingCount, mul_comm]


theorem cycleTurnLoopNatAt_loopWinding (n : ℕ) (hn : n ≥ 3) (s : Fin n) (k : ℕ) :
    (cycleTurnLoopNatAt n hn s k).loopWinding = (k : ℤ) := by
  unfold Walk.loopWinding
  rw [cycleTurnLoopNatAt_windingCount]
  have hn0 : (n : ℤ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hdiv : ((n : ℤ) * (k : ℤ)) / (n : ℤ) = (k : ℤ) :=
    Int.mul_ediv_cancel_left (k : ℤ) hn0
  simpa [mul_comm, mul_assoc, mul_left_comm] using hdiv


/-! ## Main Topological Results -/


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


/-! ## Discrete Hodge Theory -/

section Hodge

open Finset BigOperators


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


/-- Energy bound: any cochain on Cₙ has energy ≥ w²/n.
    Immediate from Hodge decomposition + non-negativity of residual energy. -/
theorem energy_ge_winding_sq (n : ℕ) (hn : n ≥ 3) (σ : C1 (Fin n)) :
    energy σ ≥ (winding n hn σ) ^ 2 / n := by
  linarith [hodge_decomposition n hn σ,
    energy_nonneg (C1.sub σ (C1.smul (winding n hn σ) (cycleHarmonicForm n hn)))]


/-- Harmonic energy of the n-cycle: minimum energy over cochains with winding number 1.
    This is the mass of the n-cycle in the Hodge-theoretic sense. -/
noncomputable def harmonicEnergy (n : ℕ) (hn : n ≥ 3) : ℝ :=
  ⨅ σ : { σ : C1 (Fin n) // winding n hn σ = 1 }, energy σ.val


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


end PathIntegral

/-! ## Edge-Restricted Cochains and b₁ -/

section EdgeHodge

open Finset BigOperators

/-- Edge-supported 1-cochains: skew-symmetric functions vanishing on non-edges. -/
structure EC1 (G : Graph V) where
  val : V → V → ℝ
  skew : ∀ i j, val i j = -val j i
  support : ∀ i j, ¬G.edge i j → val i j = 0


/-- Divergence at a vertex: Σ_w σ(v,w). -/
noncomputable def EC1.div [Fintype V] {G : Graph V} (σ : EC1 G) (v : V) : ℝ :=
  ∑ w : V, σ.val v w


/-! ### Cycle graph edge structure -/


end EdgeHodge


/-! ## Mayer-Vietoris -/

section MayerVietoris

open Classical Finset

variable [Fintype V] [DecidableEq V]


end MayerVietoris

/-! ## Bridge: Edge Counting meets Hodge Theory -/

section CycleBridge

open Finset


/-- The cycle graph is symmetric: every edge has a reverse. -/
theorem cycleGraph_symmetric (n : ℕ) (hn : n ≥ 3) :
    (CycleGraph n hn).toGraph.Symmetric := by
  intro i j h; exact h.symm


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


end Products

/-! ## Walk Algebra: Reverse, Append Laws, Homotopy Compatibility -/

section WalkAlgebra

variable {V : Type u}

/-- Reverse a walk in a symmetric graph. -/
def Walk.reverse {G : Graph V} (hsym : G.Symmetric) : Walk G u v → Walk G v u
  | .nil _ => .nil _
  | .cons h p => p.reverse hsym |>.append (.cons (hsym _ _ h) (.nil _))

/-- Appending nil is identity. -/
@[simp] theorem Walk.append_nil {G : Graph V} : (p : Walk G u v) → p.append (.nil v) = p
  | .nil _ => rfl
  | .cons h p => by simp [Walk.append, Walk.append_nil p]

/-- Append is associative. -/
theorem Walk.append_assoc {G : Graph V} :
    (p : Walk G u v) → (q : Walk G v w) → (r : Walk G w x) →
    (p.append q).append r = p.append (q.append r)
  | .nil _, _, _ => rfl
  | .cons h p, q, r => by simp [Walk.append, Walk.append_assoc p q r]

/-- Nil is left identity for append (definitional). -/
@[simp] theorem Walk.nil_append {G : Graph V} (q : Walk G u v) :
    (Walk.nil u).append q = q := rfl

/-- Reverse preserves homotopy. -/
theorem Homotopic₂.reverse {C : Complex V} (hsym : C.toGraph.Symmetric)
    {p q : Walk C.toGraph u v} (h : Homotopic₂ C p q) :
    Homotopic₂ C (p.reverse hsym) (q.reverse hsym) := by
  induction h with
  | refl _ => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | backtrack hab hba tail =>
    simp only [Walk.reverse]
    rw [Walk.append_assoc]
    conv_rhs => rw [← Walk.append_nil (Walk.reverse hsym tail)]
    exact Homotopic₂.congr_append C (Homotopic₂.refl _)
      (Homotopic₂.backtrack (hsym _ _ hba) (hsym _ _ hab) _)
  | face hf tail =>
    simp only [Walk.reverse]
    rw [Walk.append_assoc]
    exact Homotopic₂.congr_append C (Homotopic₂.refl _)
      (Homotopic₂.face_rev hf (hsym _ _ (C.face_closed _ _ _ hf).2.1)
        (hsym _ _ (C.face_closed _ _ _ hf).1)
        (hsym _ _ (C.face_closed _ _ _ hf).2.2) _)
  | face_rev hf hcb hba hca tail =>
    simp only [Walk.reverse]
    rw [Walk.append_assoc]
    exact Homotopic₂.congr_append C (Homotopic₂.refl _) (Homotopic₂.face hf _)
  | congr_cons h _ ih =>
    simp only [Walk.reverse]
    exact Homotopic₂.congr_append C ih (Homotopic₂.refl _)

/-- reverse(p) ++ p is homotopic to nil. -/
theorem reverse_append_homotopic {C : Complex V} (hsym : C.toGraph.Symmetric)
    (p : Walk C.toGraph u v) :
    Homotopic₂ C (p.reverse hsym |>.append p) (.nil v) := by
  induction p with
  | nil _ => exact .refl _
  | cons h tail ih =>
    unfold Walk.reverse
    rw [Walk.append_assoc]
    exact (Homotopic₂.congr_append_right C _ (.backtrack (hsym _ _ h) h tail)).trans ih

/-- p ++ reverse(p) is homotopic to nil. -/
theorem append_reverse_homotopic {C : Complex V} (hsym : C.toGraph.Symmetric)
    (p : Walk C.toGraph u v) :
    Homotopic₂ C (p.append (p.reverse hsym)) (.nil u) := by
  induction p with
  | nil _ => exact .refl _
  | cons h tail ih =>
    simp only [Walk.reverse]
    show Homotopic₂ C (.cons h (tail.append ((tail.reverse hsym).append (.cons (hsym _ _ h) (.nil _))))) _
    rw [← Walk.append_assoc]
    exact (Homotopic₂.congr_cons h
      (Homotopic₂.congr_append C ih (Homotopic₂.refl _))).trans
      (Homotopic₂.backtrack h (hsym _ _ h) _)

/-- Reversing a cycle-graph walk negates winding count. -/
theorem Walk.windingCount_reverse {n : ℕ} {hn : n ≥ 3}
    {s t : Fin n}
    (p : Walk (CycleGraph n hn).toGraph s t) :
    (p.reverse (cycleGraph_symmetric n hn)).windingCount = -p.windingCount := by
  induction p with
  | nil _ => simp [Walk.reverse, Walk.windingCount]
  | @cons v w x h tail ih =>
    have hrev : (CycleGraph n hn).edge w v := cycleGraph_symmetric n hn _ _ h
    have hcancel := edgeDir_cancel n hn v w h hrev
    have hrevdir : edgeDir n hn w v hrev = - edgeDir n hn v w h := by omega
    simp [Walk.reverse, Walk.windingCount_append, Walk.windingCount, ih, hrevdir]

/-- Integer-turn loop at vertex `s`:
    nonnegative turns use forward repetition, negative turns use reverse. -/
def cycleTurnLoopIntAt (n : ℕ) (hn : n ≥ 3) (s : Fin n) (k : ℤ) :
    Walk (CycleGraph n hn).toGraph s s :=
  if _hk : 0 ≤ k then
    cycleTurnLoopNatAt n hn s k.toNat
  else
    (cycleTurnLoopNatAt n hn s k.natAbs).reverse (cycleGraph_symmetric n hn)


theorem cycleTurnLoopIntAt_loopWinding (n : ℕ) (hn : n ≥ 3) (s : Fin n) (k : ℤ) :
    (cycleTurnLoopIntAt n hn s k).loopWinding = k := by
  by_cases hk : 0 ≤ k
  · simp [cycleTurnLoopIntAt, hk, cycleTurnLoopNatAt_loopWinding, Int.toNat_of_nonneg hk]
  · have hnatAbs : k = -((k.natAbs : ℤ)) := by
      rcases Int.natAbs_eq k with hkpos | hkneg
      · exfalso
        have hk0 : 0 ≤ k := by
          calc
            (0 : ℤ) ≤ (k.natAbs : ℤ) := by exact_mod_cast Nat.zero_le k.natAbs
            _ = k := hkpos.symm
        exact hk hk0
      · simpa using hkneg
    have hwc :
        (cycleTurnLoopIntAt n hn s k).windingCount = -((k.natAbs : ℤ) * n) := by
      simp [cycleTurnLoopIntAt, hk, Walk.windingCount_reverse, cycleTurnLoopNatAt_windingCount]
    have hwc_mul :
        (cycleTurnLoopIntAt n hn s k).loopWinding * n = -((k.natAbs : ℤ) * n) := by
      calc
        (cycleTurnLoopIntAt n hn s k).loopWinding * n =
            (cycleTurnLoopIntAt n hn s k).windingCount := by
              symm
              exact Walk.windingCount_eq_loopWinding_mul_card (cycleTurnLoopIntAt n hn s k)
        _ = -((k.natAbs : ℤ) * n) := hwc
    have hwc_mul' :
        (cycleTurnLoopIntAt n hn s k).loopWinding * n = (-(k.natAbs : ℤ)) * n := by
      rw [Int.neg_mul_eq_neg_mul] at hwc_mul
      exact hwc_mul
    have hn0 : (n : ℤ) ≠ 0 := by
      exact_mod_cast (show n ≠ 0 by omega)
    have hloop : (cycleTurnLoopIntAt n hn s k).loopWinding = -((k.natAbs : ℤ)) :=
      (Int.mul_eq_mul_right_iff hn0).1 hwc_mul'
    exact hloop.trans hnatAbs.symm


/-- Surjectivity of integer winding sectors at any cycle vertex. -/
theorem cycleLoopWinding_surjective_at (n : ℕ) (hn : n ≥ 3) (s : Fin n) :
    ∀ k : ℤ, ∃ p : Walk (CycleGraph n hn).toGraph s s,
      p.loopWinding = k := by
  intro k
  exact ⟨cycleTurnLoopIntAt n hn s k, cycleTurnLoopIntAt_loopWinding n hn s k⟩


theorem cycleLoopWinding_complete (n : ℕ) (hn : n ≥ 3) (s : Fin n) :
    ∀ p q : Walk (CycleGraph n hn).toGraph s s,
      p.loopWinding = q.loopWinding → Homotopic₂ (CycleGraph n hn) p q := by
  intro p q hsector
  have hpw : p.windingCount = p.loopWinding * n :=
    Walk.windingCount_eq_loopWinding_mul_card p
  have hqw : q.windingCount = q.loopWinding * n :=
    Walk.windingCount_eq_loopWinding_mul_card q
  have hwEq : p.windingCount = q.windingCount := by
    rw [hpw, hqw, hsector]
  let qrev := q.reverse (cycleGraph_symmetric n hn)
  let r : Walk (CycleGraph n hn).toGraph s s := p.append qrev
  have hr0 : r.windingCount = 0 := by
    unfold r qrev
    simp [Walk.windingCount_append, Walk.windingCount_reverse, hwEq]
  have hrnil : Homotopic₂ (CycleGraph n hn) r (Walk.nil s) :=
    cycleLoop_windingCount_zero_contractible n hn s r hr0
  have hA :
      Homotopic₂ (CycleGraph n hn) (r.append q) p := by
    unfold r qrev
    have hrevq : Homotopic₂ (CycleGraph n hn)
        ((q.reverse (cycleGraph_symmetric n hn)).append q)
        (Walk.nil s) :=
      reverse_append_homotopic (cycleGraph_symmetric n hn) q
    have h := Homotopic₂.congr_append_right (CycleGraph n hn) p hrevq
    simpa [Walk.append_assoc, Walk.append_nil] using h
  have hB :
      Homotopic₂ (CycleGraph n hn) (r.append q) q := by
    have h := Homotopic₂.congr_append (CycleGraph n hn) hrnil (Homotopic₂.refl q)
    simpa [Walk.nil_append] using h
  exact (Homotopic₂.symm hA).trans hB

end WalkAlgebra

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

/-- Canonical winding-sector map on cycle loop classes. -/
noncomputable def cycleLoopWindingClass (n : ℕ) (hn : n ≥ 3) (s : Fin n) :
    HomotopyClass₂ (CycleGraph n hn) s s → ℤ :=
  Quot.lift (fun p : Walk (CycleGraph n hn).toGraph s s => p.loopWinding)
    (fun _ _ h => loopWinding_homotopy_invariant (n := n) (hn := hn) h)

@[simp] theorem cycleLoopWindingClass_mk (n : ℕ) (hn : n ≥ 3) (s : Fin n)
    (p : Walk (CycleGraph n hn).toGraph s s) :
    cycleLoopWindingClass n hn s (Quot.mk _ p) = p.loopWinding := rfl

/-- Hodge-derived energy of a cycle loop class:
    the infimum cochain energy in its winding sector. -/
noncomputable def cycleLoopClassHodgeEnergy (n : ℕ) (hn : n ≥ 3) (s : Fin n) :
    HomotopyClass₂ (CycleGraph n hn) s s → ℝ :=
  fun h => harmonicEnergy_k n hn (cycleLoopWindingClass n hn s h)

/-- On `C_n`, Hodge-derived loop-class energy is exactly quadratic in winding. -/
theorem cycleLoopClassHodgeEnergy_eq_winding_sq (n : ℕ) (hn : n ≥ 3) (s : Fin n)
    (h : HomotopyClass₂ (CycleGraph n hn) s s) :
    cycleLoopClassHodgeEnergy n hn s h =
      (cycleLoopWindingClass n hn s h : ℝ) ^ 2 / n := by
  simp [cycleLoopClassHodgeEnergy, cycleGraph_harmonicEnergy_k]

/-- Loop classes on `C_n` at `s` are classified by integer winding.
    Surjectivity is provided canonically by `cycleTurnLoopIntAt`. -/
noncomputable def cycleLoopClassEquivInt
    (n : ℕ) (hn : n ≥ 3) (s : Fin n) :
    HomotopyClass₂ (CycleGraph n hn) s s ≃ ℤ where
  toFun := cycleLoopWindingClass n hn s
  invFun k := Quot.mk _ (Classical.choose (cycleLoopWinding_surjective_at n hn s k))
  left_inv := by
    intro x
    refine Quot.inductionOn x ?_
    intro p
    apply Quot.sound
    refine cycleLoopWinding_complete n hn s
      (Classical.choose (cycleLoopWinding_surjective_at n hn s p.loopWinding)) p ?_
    simpa [cycleLoopWindingClass] using
      (Classical.choose_spec (cycleLoopWinding_surjective_at n hn s p.loopWinding))
  right_inv := by
    intro k
    simpa [cycleLoopWindingClass] using
      (Classical.choose_spec (cycleLoopWinding_surjective_at n hn s k))


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

/-- **The simplicial ratchet**: any section of the homotopy quotient
    map misses walks — reversing the quotient loses reachability. The
    abstract cost-class form (Phase 10's transition-cost
    vocabulary) is deleted (C9); this is the cardinality-free ratchet
    of `Meno/InfoRatchet.lean`, which is the form that survives the
    quotient's infinite fibers. Where fibers are finite the coding
    theorem (`log_card_sections`) quantifies the loss. -/
theorem simplicial_ratchet
    (C : Complex V) {v w : V} (h_edge : C.edge v w) (h_back : C.edge w v)
    (r : HomotopyClass₂ C v v → Walk C.toGraph v v)
    (hr : ∀ x, Walk.toHomotopyClass₂ C (r x) = x) :
    ¬ Function.Surjective r :=
  Meno.section_not_surjective_of_not_injective
    (geodesic_computation_is_lossy C h_edge h_back) r hr

end Dynamics

end Simplicial
