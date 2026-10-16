import Meno.Symmetry

/-! # Symmetric choice: when a representative can respect the symmetry

Any surjection has sections; the question with content is whether one
commutes with a symmetry. Let a group `Γ` act on fine states `S` and on
observations `Y`, and let `p : S → Y` be equivariant.

* **The law** (`exists_equivariant_section_iff`): an equivariant section
  exists iff every observation `y` has a lift fixed by its stabilizer.
  Any group, any types. The backward direction chooses one lift per
  orbit, so this is the law that symmetric models of ZF break.
* **The price** (`symmetricChoicePrice_le_shannonEntropy`,
  `exists_symmetricChoice_entropy_eq`): a stabilizer-invariant
  distribution on the fiber always exists, and its least entropy is
  `log` of the smallest stabilizer orbit in the fiber
  (`symmetricChoicePrice`). Symmetric mixed choice is always possible;
  symmetric pure choice is the case where it costs nothing.
* **The boundary** (`symmetricChoicePrice_eq_zero_iff`,
  `exists_equivariant_section_iff_price`): the price vanishes iff a
  fixed lift exists, so an equivariant section exists iff every price
  vanishes.
* **The ceiling** (`symmetricChoicePrice_le_recoveryCost`): the price
  never exceeds the recovery cost `log |p⁻¹{y}|` of the coding theorem.
* **The strictness witness** (`cycle_symmetricChoicePrice_pos`): on
  `C_n` at resolution `q` with `1 < gcd n q`, under the rotation's
  `ℤ`-action, the winding-one class has positive price — G4 read as a
  price. -/

namespace Meno

open MulAction

universe u v

section General

variable (Γ : Type v) {S Y : Type u} [Group Γ] [MulAction Γ S] [MulAction Γ Y]

/-- **A symmetric lift** of `y`: a point of the fiber over `y` fixed by
the stabilizer of `y`. -/
def SymmetricLift (p : S → Y) (y : Y) (x : S) : Prop :=
  p x = y ∧ ∀ g ∈ stabilizer Γ y, g • x = x

/-- **THE EQUIVARIANT-SECTION LAW**: an equivariant section of an
equivariant map exists iff every observation has a symmetric lift. -/
theorem exists_equivariant_section_iff (p : S → Y)
    (hp : ∀ (g : Γ) x, p (g • x) = g • p x) :
    (∃ s : Y → S, (∀ y, p (s y) = y) ∧ ∀ (g : Γ) y, s (g • y) = g • s y) ↔
      ∀ y, ∃ x, SymmetricLift Γ p y x := by
  constructor
  · rintro ⟨s, hs, hequi⟩ y
    refine ⟨s y, hs y, fun g hg => ?_⟩
    rw [← hequi, mem_stabilizer_iff.mp hg]
  · intro h
    choose lift hlift using h
    let rep : Y → Y := fun y => (Quotient.mk (orbitRel Γ Y) y).out
    have hrep : ∀ y, ∃ g : Γ, g • rep y = y := fun y => by
      obtain ⟨g, hg⟩ := (orbitRel_apply).mp (Quotient.mk_out (s := orbitRel Γ Y) y)
      simp only at hg
      exact ⟨g⁻¹, by simp only [rep]; rw [← hg, inv_smul_smul]⟩
    have hrep_smul : ∀ (h : Γ) y, rep (h • y) = rep y := fun h y => by
      simp only [rep]
      congr 1
      exact Quotient.sound ((orbitRel_apply).mpr (mem_orbit y h))
    choose g hg using hrep
    refine ⟨fun y => g y • lift (rep y), fun y => ?_, fun h y => ?_⟩
    · rw [hp, (hlift (rep y)).1, hg]
    · simp only
      rw [hrep_smul, smul_smul]
      have e1 : g (h • y) • rep y = h • y := by rw [← hrep_smul h y]; exact hg _
      have e2 : (h * g y) • rep y = h • y := by rw [mul_smul, hg]
      have hk : (h * g y)⁻¹ * g (h • y) ∈ stabilizer Γ (rep y) := by
        rw [mem_stabilizer_iff, mul_smul, e1, ← e2, inv_smul_smul]
      have := (hlift (rep y)).2 _ hk
      rw [mul_smul, inv_smul_eq_iff] at this
      exact this

variable [Fintype S]

open Classical in
/-- **The stabilizer orbit** of `x` under the stabilizer of `y`. -/
noncomputable def stabOrbit (y : Y) (x : S) : Finset S :=
  Finset.univ.filter fun z => ∃ g ∈ stabilizer Γ y, g • x = z

theorem mem_stabOrbit {y : Y} {x z : S} :
    z ∈ stabOrbit Γ y x ↔ ∃ g ∈ stabilizer Γ y, g • x = z := by
  classical
  simp [stabOrbit]

theorem self_mem_stabOrbit (y : Y) (x : S) : x ∈ stabOrbit Γ y x :=
  (mem_stabOrbit Γ).mpr ⟨1, one_mem _, one_smul _ _⟩

theorem smul_mem_stabOrbit_iff {y : Y} {x z : S} {g : Γ}
    (hg : g ∈ stabilizer Γ y) :
    g • z ∈ stabOrbit Γ y x ↔ z ∈ stabOrbit Γ y x := by
  simp only [mem_stabOrbit]
  constructor
  · rintro ⟨h, hh, hz⟩
    exact ⟨g⁻¹ * h, mul_mem (inv_mem hg) hh, by rw [mul_smul, hz, inv_smul_smul]⟩
  · rintro ⟨h, hh, hz⟩
    exact ⟨g * h, mul_mem hg hh, by rw [mul_smul, hz]⟩

theorem card_stabOrbit_pos (y : Y) (x : S) : 0 < (stabOrbit Γ y x).card :=
  Finset.card_pos.mpr ⟨x, self_mem_stabOrbit Γ y x⟩

theorem card_stabOrbit_eq_one_iff {y : Y} {x : S} :
    (stabOrbit Γ y x).card = 1 ↔ ∀ g ∈ stabilizer Γ y, g • x = x := by
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨a, ha⟩ g hg
    have h1 : g • x ∈ stabOrbit Γ y x := (mem_stabOrbit Γ).mpr ⟨g, hg, rfl⟩
    have h2 := self_mem_stabOrbit Γ y x
    rw [ha, Finset.mem_singleton] at h1 h2
    rw [h1, h2]
  · intro hfix
    refine ⟨x, Finset.ext fun z => ?_⟩
    rw [mem_stabOrbit, Finset.mem_singleton]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hfix g hg
    · rintro rfl
      exact ⟨1, one_mem _, one_smul _ _⟩

/-- **The orbit floor**: the size of the smallest stabilizer orbit in the
fiber over `y` (`0` on an empty fiber). -/
noncomputable def orbitFloor (p : S → Y) (y : Y) : ℕ :=
  sInf {k | ∃ x, p x = y ∧ (stabOrbit Γ y x).card = k}

/-- **The price of symmetric choice** at `y`: `log` of the orbit floor. -/
noncomputable def symmetricChoicePrice (p : S → Y) (y : Y) : ℝ :=
  Real.log (orbitFloor Γ p y)

variable {Γ}

theorem orbitFloor_spec {p : S → Y} {y : Y} (hy : ∃ x, p x = y) :
    ∃ x, p x = y ∧ (stabOrbit Γ y x).card = orbitFloor Γ p y := by
  obtain ⟨x, hx⟩ := hy
  exact Nat.sInf_mem (s := {k | ∃ x, p x = y ∧ (stabOrbit Γ y x).card = k})
    ⟨_, x, hx, rfl⟩

theorem orbitFloor_le {p : S → Y} {y : Y} {x : S} (hx : p x = y) :
    orbitFloor Γ p y ≤ (stabOrbit Γ y x).card :=
  Nat.sInf_le ⟨x, hx, rfl⟩

theorem orbitFloor_pos {p : S → Y} {y : Y} (hy : ∃ x, p x = y) :
    0 < orbitFloor Γ p y := by
  obtain ⟨x, _, hx⟩ := orbitFloor_spec (Γ := Γ) hy
  rw [← hx]
  exact card_stabOrbit_pos Γ y x

theorem orbitFloor_eq_one_iff {p : S → Y} {y : Y} (hy : ∃ x, p x = y) :
    orbitFloor Γ p y = 1 ↔ ∃ x, SymmetricLift Γ p y x := by
  constructor
  · intro h1
    obtain ⟨x, hx, hc⟩ := orbitFloor_spec (Γ := Γ) hy
    exact ⟨x, hx, (card_stabOrbit_eq_one_iff Γ).mp (hc.trans h1)⟩
  · rintro ⟨x, hx, hfix⟩
    have hle := orbitFloor_le (Γ := Γ) hx
    rw [(card_stabOrbit_eq_one_iff Γ).mpr hfix] at hle
    have := orbitFloor_pos (Γ := Γ) hy
    omega

theorem symmetricChoicePrice_nonneg (p : S → Y) (y : Y) :
    0 ≤ symmetricChoicePrice Γ p y :=
  Real.log_natCast_nonneg _

/-- **The boundary**: the price vanishes iff a symmetric lift exists. -/
theorem symmetricChoicePrice_eq_zero_iff {p : S → Y} {y : Y}
    (hy : ∃ x, p x = y) :
    symmetricChoicePrice Γ p y = 0 ↔ ∃ x, SymmetricLift Γ p y x := by
  rw [← orbitFloor_eq_one_iff hy, symmetricChoicePrice, Real.log_eq_zero]
  have hpos := orbitFloor_pos (Γ := Γ) hy
  constructor
  · rintro (h | h | h)
    · exact absurd h (by exact_mod_cast hpos.ne')
    · exact_mod_cast h
    · have : (0 : ℝ) ≤ orbitFloor Γ p y := Nat.cast_nonneg _
      linarith
  · intro h
    right; left
    exact_mod_cast h

/-- **The law, priced**: an equivariant section of an equivariant
surjection exists iff the price of symmetric choice vanishes everywhere. -/
theorem exists_equivariant_section_iff_price (p : S → Y)
    (hp : ∀ (g : Γ) x, p (g • x) = g • p x) (hsurj : Function.Surjective p) :
    (∃ s : Y → S, (∀ y, p (s y) = y) ∧ ∀ (g : Γ) y, s (g • y) = g • s y) ↔
      ∀ y, symmetricChoicePrice Γ p y = 0 := by
  rw [exists_equivariant_section_iff Γ p hp]
  exact forall_congr' fun y => (symmetricChoicePrice_eq_zero_iff (hsurj y)).symm

variable (Γ) in
/-- **A symmetric choice** at `y`: a distribution on the fiber over `y`
invariant under the stabilizer of `y`. -/
structure SymmetricChoice (p : S → Y) (y : Y) (μ : S → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ μ x
  sum_one : ∑ x, μ x = 1
  supp : ∀ x, μ x ≠ 0 → p x = y
  inv : ∀ g ∈ stabilizer Γ y, ∀ x, μ (g • x) = μ x

/-- An invariant distribution weighs each point at most the reciprocal of
its stabilizer orbit. -/
theorem SymmetricChoice.card_mul_le_one {p : S → Y} {y : Y} {μ : S → ℝ}
    (hμ : SymmetricChoice Γ p y μ) (x : S) :
    ((stabOrbit Γ y x).card : ℝ) * μ x ≤ 1 := by
  have hconst : ∀ z ∈ stabOrbit Γ y x, μ z = μ x := fun z hz => by
    obtain ⟨g, hg, rfl⟩ := (mem_stabOrbit Γ).mp hz
    exact hμ.inv g hg x
  calc ((stabOrbit Γ y x).card : ℝ) * μ x
      = ∑ z ∈ stabOrbit Γ y x, μ z := by
        rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ z, μ z :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun z _ _ => hμ.nonneg z
    _ = 1 := hμ.sum_one

/-- **The entropy floor**: every symmetric choice has entropy at least
the price. -/
theorem symmetricChoicePrice_le_shannonEntropy {p : S → Y} {y : Y}
    {μ : S → ℝ} (hμ : SymmetricChoice Γ p y μ) :
    symmetricChoicePrice Γ p y ≤ shannonEntropy μ := by
  have hy : ∃ x, p x = y := by
    by_contra hne
    simp only [not_exists] at hne
    have : ∑ x, μ x = 0 :=
      Finset.sum_eq_zero fun x _ => by_contra fun h => hne x (hμ.supp x h)
    rw [hμ.sum_one] at this
    exact one_ne_zero this
  set m := orbitFloor Γ p y
  have hm : (0 : ℝ) < m := by exact_mod_cast orbitFloor_pos (Γ := Γ) hy
  have hterm : ∀ x, μ x * Real.log m ≤ -(μ x * Real.log (μ x)) := fun x => by
    rcases (hμ.nonneg x).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hfloor : (m : ℝ) ≤ (stabOrbit Γ y x).card := by
        exact_mod_cast orbitFloor_le (Γ := Γ) (hμ.supp x hpos.ne')
      have hmx : (m : ℝ) * μ x ≤ 1 :=
        (mul_le_mul_of_nonneg_right hfloor hpos.le).trans (hμ.card_mul_le_one x)
      have hle : (m : ℝ) ≤ (μ x)⁻¹ := by
        rw [le_inv_comm₀ hm hpos]
        rw [inv_eq_one_div, le_div_iff₀ hm]
        linarith
      have := Real.log_le_log hm hle
      rw [Real.log_inv] at this
      nlinarith
  unfold symmetricChoicePrice shannonEntropy
  calc Real.log m = ∑ x, μ x * Real.log m := by
        rw [← Finset.sum_mul, hμ.sum_one, one_mul]
    _ ≤ ∑ x, -(μ x * Real.log (μ x)) := Finset.sum_le_sum fun x _ => hterm x
    _ = -∑ x, μ x * Real.log (μ x) := by rw [Finset.sum_neg_distrib]

/-- **The price is attained**: on a nonempty fiber of an equivariant map,
the uniform distribution on a smallest stabilizer orbit is a symmetric
choice of entropy exactly the price. -/
theorem exists_symmetricChoice_entropy_eq {p : S → Y}
    (hp : ∀ (g : Γ) x, p (g • x) = g • p x) {y : Y} (hy : ∃ x, p x = y) :
    ∃ μ, SymmetricChoice Γ p y μ ∧ shannonEntropy μ = symmetricChoicePrice Γ p y := by
  classical
  obtain ⟨x, hx, hc⟩ := orbitFloor_spec (Γ := Γ) hy
  set O := stabOrbit Γ y x
  have hO : (0 : ℝ) < O.card := by exact_mod_cast card_stabOrbit_pos Γ y x
  let μ : S → ℝ := fun z => if z ∈ O then (O.card : ℝ)⁻¹ else 0
  refine ⟨μ, ⟨fun z => ?_, ?_, fun z hz => ?_, fun g hg z => ?_⟩, ?_⟩
  · simp only [μ]; split_ifs <;> positivity
  · simp only [μ]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
      mul_inv_cancel₀ hO.ne']
  · simp only [μ] at hz
    split_ifs at hz with hmem
    · obtain ⟨g, hg, rfl⟩ := (mem_stabOrbit Γ).mp hmem
      rw [hp, hx, mem_stabilizer_iff.mp hg]
    · exact absurd rfl hz
  · simp only [μ, O, smul_mem_stabOrbit_iff Γ hg]
  · unfold shannonEntropy symmetricChoicePrice
    have : ∀ z, μ z * Real.log (μ z)
        = if z ∈ O then (O.card : ℝ)⁻¹ * Real.log (O.card : ℝ)⁻¹ else 0 := fun z => by
      simp only [μ]; split_ifs <;> simp
    simp only [this]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hO.ne', one_mul, Real.log_inv, neg_neg, ← hc]

/-- **The ceiling**: the price never exceeds the recovery cost of the
fiber — a symmetric choice never needs more than the whole fiber. -/
theorem symmetricChoicePrice_le_recoveryCost {p : S → Y} {y : Y}
    (hp : ∀ (g : Γ) x, p (g • x) = g • p x) (hy : ∃ x, p x = y) :
    symmetricChoicePrice Γ p y ≤ recoveryCost p y := by
  obtain ⟨x, hx, hc⟩ := orbitFloor_spec (Γ := Γ) hy
  have hsub : (↑(stabOrbit Γ y x) : Set S) ⊆ p ⁻¹' {y} := fun z hz => by
    obtain ⟨g, hg, rfl⟩ := (mem_stabOrbit Γ).mp hz
    show p (g • x) = y
    rw [hp, hx, mem_stabilizer_iff.mp hg]
  have hcard : (stabOrbit Γ y x).card ≤ Nat.card (p ⁻¹' {y}) := by
    rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  unfold symmetricChoicePrice recoveryCost
  apply Real.log_le_log (by exact_mod_cast orbitFloor_pos (Γ := Γ) hy)
  rw [← hc]
  exact_mod_cast hcard

end General

/-! ## The cycle: G4 as a price -/

section Cycle

variable (n q : ℕ) (hn : 0 < n) [NeZero q]

/-- The rotation's pullback on resolution-`q` cochains of `C_n`, as a
permutation. -/
def cycleRotPerm : Equiv.Perm (Fin n → ZMod q) :=
  ((cycleRot n hn).edgeEquiv.symm).arrowCongr (Equiv.refl _)

omit [NeZero q] in
theorem cycleRotPerm_apply (ω : Fin n → ZMod q) :
    cycleRotPerm n q hn ω = (cycleRot n hn).cochainMap (ZMod q) ω := rfl

/-- `ℤ` acts on cochains by powers of the rotation. -/
@[reducible] def cycleRotAction : MulAction (Multiplicative ℤ) (Fin n → ZMod q) :=
  MulAction.compHom _ (zpowersHom (Equiv.Perm (Fin n → ZMod q)) (cycleRotPerm n q hn))

/-- `ℤ` acts trivially on classes: the rotation fixes every class
(`cycleRot_h1ReductionMap`). -/
@[reducible] def cycleClassAction :
    MulAction (Multiplicative ℤ) (IncidenceGraph.H1Reduction (cycleGraph n hn) q) :=
  MulAction.compHom _
    (1 : Multiplicative ℤ →* Equiv.Perm (IncidenceGraph.H1Reduction (cycleGraph n hn) q))

/-- **The strictness witness**: at `1 < gcd n q`, under the rotation's
`ℤ`-action, the winding-one class of `C_n` has positive price of
symmetric choice. -/
theorem cycle_symmetricChoicePrice_pos (h : 1 < Nat.gcd n q) :
    letI := cycleRotAction n q hn
    letI := cycleClassAction n q hn
    0 < symmetricChoicePrice (Multiplicative ℤ)
      ((cycleGraph n hn).carrierCompression q)
      ((cycleGraph n hn).carrierCompression q (Pi.single ⟨0, hn⟩ 1)) := by
  let := cycleRotAction n q hn
  let := cycleClassAction n q hn
  have : NeZero n := ⟨hn.ne'⟩
  refine (symmetricChoicePrice_nonneg _ _).lt_of_ne fun h0 => ?_
  obtain ⟨x, hx, hfix⟩ := (symmetricChoicePrice_eq_zero_iff ⟨_, rfl⟩).mp h0.symm
  have hrot := hfix (Multiplicative.ofAdd 1) (by
    simp [mem_stabilizer_iff, MulAction.compHom_smul_def])
  refine cycle_no_invariant_representative n q hn h ⟨x, ?_, ?_⟩
  · rw [← cycleRotPerm_apply]
    simpa [MulAction.compHom_smul_def, zpowersHom_apply, Equiv.Perm.smul_def]
      using hrot
  · exact ((cycleGraph n hn).h1ResQuotEquivZMod q).symm.injective hx

end Cycle

end Meno
