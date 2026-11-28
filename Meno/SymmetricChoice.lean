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
* **The ledger** (`symmetricChoicePrice_le_entropy_add_asymmetry`): any
  distribution on the fiber pays the price in entropy plus asymmetry, the
  entropy that averaging over stabilizer orbits adds (`asymmetry_nonneg`).
  A point mass pays its whole orbit in asymmetry (`asymmetry_dirac`).
  Classically there are two currencies, mixing and choosing; the quantum
  ledger adds superposition, paid in non-locality.
* **The ceiling** (`symmetricChoicePrice_le_recoveryCost`): the price
  never exceeds the recovery cost `log |p⁻¹{y}|` of the coding theorem.
* **The strictness witness** (`cycle_symmetricChoicePrice_pos`): on
  `C_n` at resolution `q` with `1 < gcd n q`, under the rotation's
  `ℤ`-action, the winding-one class has positive price — G4 read as a
  price.
* **The cycle's price, exactly** (`cycle_symmetricChoicePrice_eq`): it is
  `log (n / coprimePart n q)`, where `coprimePart n q` is the largest
  divisor of `n` coprime to `q`. A winding-one cochain of minimal period
  `P` winds `n / P` times a block sum, so `n / P` must be a unit mod `q`;
  `c⁻¹` on every `(n / c)`-th edge attains the bound. At `(4, 2)` the
  price is `log 4` (`cycle_four_two_symmetricChoicePrice`). -/

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

/-! ### The classical ledger: mix or choose

Averaging a distribution over stabilizer orbits makes it symmetric. What
the averaging adds to its entropy is its asymmetry, so entropy plus
asymmetry is the entropy of a symmetric choice, which is at least the
price. Classically a representative is paid for in two currencies only:
mixing (entropy) or choosing (asymmetry). -/

variable (Γ)

theorem mem_stabOrbit_comm {y : Y} {x z : S} :
    z ∈ stabOrbit Γ y x ↔ x ∈ stabOrbit Γ y z := by
  simp only [mem_stabOrbit]
  constructor <;> rintro ⟨g, hg, rfl⟩ <;>
    exact ⟨g⁻¹, inv_mem hg, inv_smul_smul g _⟩

theorem stabOrbit_eq_of_mem {y : Y} {x z : S} (h : z ∈ stabOrbit Γ y x) :
    stabOrbit Γ y z = stabOrbit Γ y x := by
  obtain ⟨g, hg, rfl⟩ := (mem_stabOrbit Γ).mp h
  ext w
  simp only [mem_stabOrbit]
  constructor
  · rintro ⟨h', hh', rfl⟩
    exact ⟨h' * g, mul_mem hh' hg, mul_smul _ _ _⟩
  · rintro ⟨h', hh', rfl⟩
    exact ⟨h' * g⁻¹, mul_mem hh' (inv_mem hg), by rw [mul_smul, inv_smul_smul]⟩

/-- **The symmetrization** of `μ`: its average over each stabilizer orbit. -/
noncomputable def symmetrize (y : Y) (μ : S → ℝ) (x : S) : ℝ :=
  (∑ z ∈ stabOrbit Γ y x, μ z) / (stabOrbit Γ y x).card

theorem symmetrize_eq_of_mem {y : Y} {μ : S → ℝ} {x z : S} (h : z ∈ stabOrbit Γ y x) :
    symmetrize Γ y μ z = symmetrize Γ y μ x := by
  rw [symmetrize, symmetrize, stabOrbit_eq_of_mem Γ h]

/-- Against an orbit-constant weight, a distribution and its symmetrization
agree. -/
theorem sum_symmetrize_mul {y : Y} (μ f : S → ℝ)
    (hf : ∀ x z, z ∈ stabOrbit Γ y x → f z = f x) :
    ∑ x, symmetrize Γ y μ x * f x = ∑ x, μ x * f x := by
  classical
  calc ∑ x, symmetrize Γ y μ x * f x
      = ∑ x, ∑ z, if z ∈ stabOrbit Γ y x then μ z * f x / (stabOrbit Γ y x).card else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_ite_mem, Finset.univ_inter, symmetrize, div_mul_eq_mul_div,
          Finset.sum_mul, Finset.sum_div]
    _ = ∑ z, ∑ x, if z ∈ stabOrbit Γ y x then μ z * f x / (stabOrbit Γ y x).card else 0 :=
        Finset.sum_comm
    _ = ∑ z, μ z * f z := by
        refine Finset.sum_congr rfl fun z _ => ?_
        have hpos : (0 : ℝ) < (stabOrbit Γ y z).card := by
          exact_mod_cast card_stabOrbit_pos Γ y z
        calc (∑ x, if z ∈ stabOrbit Γ y x then μ z * f x / (stabOrbit Γ y x).card else 0)
            = ∑ x, if x ∈ stabOrbit Γ y z then μ z * f z / (stabOrbit Γ y z).card else 0 := by
              refine Finset.sum_congr rfl fun x _ => ?_
              by_cases hx : x ∈ stabOrbit Γ y z
              · have hz : z ∈ stabOrbit Γ y x := (mem_stabOrbit_comm Γ).mpr hx
                rw [ite_eq_left hz, ite_eq_left hx, hf x z hz, stabOrbit_eq_of_mem Γ hx]
              · rw [ite_eq_right (fun hz => hx ((mem_stabOrbit_comm Γ).mp hz)), ite_eq_right hx]
          _ = μ z * f z := by
              rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
                mul_div_cancel₀ _ hpos.ne']

theorem sum_symmetrize {y : Y} (μ : S → ℝ) : ∑ x, symmetrize Γ y μ x = ∑ x, μ x := by
  simpa using sum_symmetrize_mul Γ μ (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)

theorem symmetrize_nonneg {y : Y} {μ : S → ℝ} (hμ : ∀ x, 0 ≤ μ x) (x : S) :
    0 ≤ symmetrize Γ y μ x :=
  div_nonneg (Finset.sum_nonneg fun z _ => hμ z) (Nat.cast_nonneg _)

/-- **Symmetrizing is a symmetric choice**: a distribution on the fiber,
averaged over stabilizer orbits, is stabilizer-invariant and stays on the
fiber. -/
theorem symmetrize_symmetricChoice {p : S → Y} (hp : ∀ (g : Γ) x, p (g • x) = g • p x)
    {y : Y} {μ : S → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hsupp : ∀ x, μ x ≠ 0 → p x = y) :
    SymmetricChoice Γ p y (symmetrize Γ y μ) where
  nonneg := symmetrize_nonneg Γ hμ0
  sum_one := by rw [sum_symmetrize, hμ1]
  supp x hx := by
    have : ∃ z ∈ stabOrbit Γ y x, μ z ≠ 0 := by
      by_contra hne
      simp only [not_exists, not_and, not_not] at hne
      exact hx (by rw [symmetrize, Finset.sum_eq_zero hne, zero_div])
    obtain ⟨z, hz, hμz⟩ := this
    obtain ⟨g, hg, rfl⟩ := (mem_stabOrbit Γ).mp hz
    have h1 := hsupp _ hμz
    rw [hp] at h1
    calc p x = g⁻¹ • g • p x := (inv_smul_smul g _).symm
      _ = y := by rw [h1]; exact mem_stabilizer_iff.mp (inv_mem hg)
  inv g hg x := symmetrize_eq_of_mem Γ ((mem_stabOrbit Γ).mpr ⟨g, hg, rfl⟩)

/-- **The asymmetry** of `μ`: the entropy its symmetrization adds. -/
noncomputable def asymmetry (y : Y) (μ : S → ℝ) : ℝ :=
  shannonEntropy (symmetrize Γ y μ) - shannonEntropy μ

theorem shannonEntropy_add_asymmetry (y : Y) (μ : S → ℝ) :
    shannonEntropy μ + asymmetry Γ y μ = shannonEntropy (symmetrize Γ y μ) := by
  unfold asymmetry; ring

/-- **The asymmetry is nonnegative**: it is the relative entropy of `μ`
against its symmetrization. -/
theorem asymmetry_nonneg {y : Y} {μ : S → ℝ} (hμ : ∀ x, 0 ≤ μ x) :
    0 ≤ asymmetry Γ y μ := by
  set ν := symmetrize Γ y μ
  have hlog : ∑ x, ν x * Real.log (ν x) = ∑ x, μ x * Real.log (ν x) :=
    sum_symmetrize_mul Γ μ (fun x => Real.log (ν x))
      (fun x z h => by simp only [ν]; rw [symmetrize_eq_of_mem Γ h])
  have hterm : ∀ x, μ x - ν x ≤ μ x * Real.log (μ x) - μ x * Real.log (ν x) := fun x => by
    rcases (hμ x).eq_or_lt with h0 | hpos
    · rw [← h0]; simp only [zero_mul, sub_zero, zero_sub, neg_nonpos]
      exact symmetrize_nonneg Γ hμ x
    · have hν : 0 < ν x := by
        have hle : μ x ≤ ∑ z ∈ stabOrbit Γ y x, μ z :=
          Finset.single_le_sum (fun z _ => hμ z) (self_mem_stabOrbit Γ y x)
        exact div_pos (lt_of_lt_of_le hpos hle) (by exact_mod_cast card_stabOrbit_pos Γ y x)
      have key := Real.one_sub_inv_le_log_of_pos (div_pos hpos hν)
      rw [inv_div, Real.log_div hpos.ne' hν.ne'] at key
      have : μ x * (1 - ν x / μ x) = μ x - ν x := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left key hpos.le]
  unfold asymmetry shannonEntropy
  have hsum : ∑ x, (μ x - ν x) = 0 := by
    rw [Finset.sum_sub_distrib, sum_symmetrize, sub_self]
  have := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hterm x
  rw [hsum, Finset.sum_sub_distrib] at this
  linarith

/-- **THE CLASSICAL LEDGER**: entropy plus asymmetry is at least the price
of symmetric choice. A representative is paid for by mixing or by choosing. -/
theorem symmetricChoicePrice_le_entropy_add_asymmetry {p : S → Y}
    (hp : ∀ (g : Γ) x, p (g • x) = g • p x) {y : Y} {μ : S → ℝ}
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1) (hsupp : ∀ x, μ x ≠ 0 → p x = y) :
    symmetricChoicePrice Γ p y ≤ shannonEntropy μ + asymmetry Γ y μ := by
  rw [shannonEntropy_add_asymmetry]
  exact symmetricChoicePrice_le_shannonEntropy (symmetrize_symmetricChoice Γ hp hμ0 hμ1 hsupp)

theorem shannonEntropy_uniform [DecidableEq S] (O : Finset S) (hO : O.Nonempty) :
    shannonEntropy (fun z => if z ∈ O then (O.card : ℝ)⁻¹ else 0) = Real.log O.card := by
  have hc : (0 : ℝ) < O.card := by exact_mod_cast hO.card_pos
  unfold shannonEntropy
  have : ∀ z, (if z ∈ O then (O.card : ℝ)⁻¹ else 0) * Real.log (if z ∈ O then (O.card : ℝ)⁻¹ else 0)
      = if z ∈ O then (O.card : ℝ)⁻¹ * Real.log (O.card : ℝ)⁻¹ else 0 := fun z => by
    split_ifs <;> simp
  simp only [this]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hc.ne', one_mul, Real.log_inv, neg_neg]

/-- **The choosing corner**: a point mass is pure and pays its whole orbit
in asymmetry, `log |stabOrbit x|`. -/
theorem asymmetry_dirac [DecidableEq S] (y : Y) (x : S) :
    asymmetry Γ y (fun z => if z = x then 1 else 0) = Real.log (stabOrbit Γ y x).card := by
  have hsym : symmetrize Γ y (fun z => if z = x then 1 else 0)
      = fun z => if z ∈ stabOrbit Γ y x then ((stabOrbit Γ y x).card : ℝ)⁻¹ else 0 := by
    funext z
    rw [symmetrize, Finset.sum_ite_eq']
    by_cases hz : z ∈ stabOrbit Γ y x
    · rw [ite_eq_left ((mem_stabOrbit_comm Γ).mp hz), ite_eq_left hz, stabOrbit_eq_of_mem Γ hz, one_div]
    · rw [ite_eq_right (fun h => hz ((mem_stabOrbit_comm Γ).mpr h)), ite_eq_right hz, zero_div]
  have hpure : shannonEntropy (fun z => if z = x then (1 : ℝ) else 0) = 0 := by
    unfold shannonEntropy
    rw [neg_eq_zero]
    exact Finset.sum_eq_zero fun z _ => by dsimp only; split_ifs <;> simp
  rw [asymmetry, hsym, hpure, sub_zero,
    shannonEntropy_uniform _ ⟨x, self_mem_stabOrbit Γ y x⟩]

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

/-! ## The cycle's price, exactly -/

open Fin.NatCast

/-- **The coprime part** of `n` against `q`: its largest divisor coprime to
`q`. -/
def coprimePart (n q : ℕ) : ℕ :=
  ((Nat.divisors n).filter fun d => Nat.Coprime d q).sup id

omit [NeZero q] in
include hn in
theorem coprimePart_spec :
    coprimePart n q ∣ n ∧ Nat.Coprime (coprimePart n q) q ∧
      ∀ d, d ∣ n → Nat.Coprime d q → d ≤ coprimePart n q := by
  have hne : ((Nat.divisors n).filter fun d => Nat.Coprime d q).Nonempty :=
    ⟨1, Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hn.ne', Nat.coprime_one_left q⟩⟩
  obtain ⟨c, hc, hsup⟩ := Finset.exists_mem_eq_sup _ hne id
  rw [Finset.mem_filter, Nat.mem_divisors] at hc
  refine ⟨?_, ?_, fun d hd hcop => ?_⟩
  · rw [coprimePart, hsup]; exact hc.1.1
  · rw [coprimePart, hsup]; exact hc.2
  · exact Finset.le_sup (f := id)
      (Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd, hn.ne'⟩, hcop⟩)

omit [NeZero q] in
theorem cycleRotPerm_iterate_apply [NeZero n] (m : ℕ) (x : Fin n → ZMod q) (e : Fin n) :
    ((cycleRotPerm n q hn)^[m] x) e = x (e + (m : Fin n)) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih]
    show x (e + (m : Fin n) + 1) = x (e + ((m + 1 : ℕ) : Fin n))
    rw [Nat.cast_succ, add_assoc]

omit [NeZero q] in
theorem cycle_smul_apply (g : Multiplicative ℤ) (x : Fin n → ZMod q) :
    letI := cycleRotAction n q hn
    g • x = (cycleRotPerm n q hn ^ Multiplicative.toAdd g) x := rfl

theorem cycle_mem_stabilizer (g : Multiplicative ℤ)
    (y : IncidenceGraph.H1Reduction (cycleGraph n hn) q) :
    letI := cycleClassAction n q hn
    g ∈ stabilizer (Multiplicative ℤ) y := by
  simp [mem_stabilizer_iff, MulAction.compHom_smul_def]

/-- The fiber over the winding-one class is the cochains of winding sum `1`. -/
theorem cycle_fiber_iff (x : Fin n → ZMod q) :
    (cycleGraph n hn).carrierCompression q x
        = (cycleGraph n hn).carrierCompression q (Pi.single ⟨0, hn⟩ 1)
      ↔ ∑ e, x e = 1 := by
  have : NeZero n := ⟨hn.ne'⟩
  have key : ∀ z, (cycleGraph n hn).carrierCompression q z
      = ((cycleGraph n hn).h1ResQuotEquivZMod q).symm (Submodule.Quotient.mk z) :=
    fun _ => rfl
  rw [key, key, ((cycleGraph n hn).h1ResQuotEquivZMod q).symm.injective.eq_iff]
  constructor
  · intro h
    have h0 := congrArg
      (fun κ => (cycleGraph n hn).latticeQuotEquivQ (cycleLatticeBasis n hn) q κ 0) h
    rw [cycle_latticeQuotEquivQ_mk, cycle_latticeQuotEquivQ_mk] at h0
    rw [h0]
    exact Fintype.sum_pi_single' _ 1
  · intro h
    apply ((cycleGraph n hn).latticeQuotEquivQ (cycleLatticeBasis n hn) q).injective
    funext j
    rw [cycle_latticeQuotEquivQ_mk, cycle_latticeQuotEquivQ_mk, h, Fintype.sum_pi_single']

omit [NeZero q] in
theorem sum_range_mul_of_periodic {M : Type*} [AddCommMonoid M] (f : ℕ → M) (P : ℕ)
    (hf : ∀ k, f (k + P) = f k) (a : ℕ) :
    ∑ k ∈ Finset.range (a * P), f k = a • ∑ i ∈ Finset.range P, f i := by
  have hshift : ∀ a i, f (a * P + i) = f i := fun a i => by
    induction a with
    | zero => simp
    | succ a ih => rw [Nat.succ_mul, add_right_comm, hf, ih]
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => hshift a i

omit [NeZero q] in
/-- A cochain of period `P ∣ n` winds `n / P` times its first `P` values. -/
theorem sum_of_periodic [NeZero n] (x : Fin n → ZMod q) (P : ℕ) (hP : P ∣ n)
    (hx : ∀ e : Fin n, x (e + (P : Fin n)) = x e) :
    ∑ e, x e = ((n / P : ℕ) : ZMod q) * ∑ i ∈ Finset.range P, x (i : Fin n) := by
  let f : ℕ → ZMod q := fun k => x (k : Fin n)
  have hf : ∀ k, f (k + P) = f k := fun k => by simp only [f, Nat.cast_add]; exact hx _
  have h1 : ∑ e, x e = ∑ k ∈ Finset.range n, f k := by
    rw [← Fin.sum_univ_eq_sum_range]; simp [f]
  have h2 : Finset.range n = Finset.range (n / P * P) := by rw [Nat.div_mul_cancel hP]
  rw [h1, h2, sum_range_mul_of_periodic f P hf, nsmul_eq_mul]

/-- **The lower bound**: every cochain of winding one has a rotation orbit of
at least `n / coprimePart n q` elements. Its minimal period `P` divides `n`,
so it winds `n / P` times a block sum; winding one makes `n / P` a unit mod
`q`, hence a divisor of `n` coprime to `q`. -/
theorem cycle_le_card_stabOrbit (x : Fin n → ZMod q) (hx : ∑ e, x e = 1)
    (y : IncidenceGraph.H1Reduction (cycleGraph n hn) q) :
    letI := cycleRotAction n q hn
    letI := cycleClassAction n q hn
    n / coprimePart n q ≤ (stabOrbit (Multiplicative ℤ) y x).card := by
  let := cycleRotAction n q hn
  let := cycleClassAction n q hn
  have : NeZero n := ⟨hn.ne'⟩
  set σ := cycleRotPerm n q hn
  have hper : Function.IsPeriodicPt σ n x := by
    show σ^[n] x = x
    funext e
    rw [cycleRotPerm_iterate_apply, Fin.natCast_self, add_zero]
  set P := Function.minimalPeriod σ x
  have hPpos : 0 < P := hper.minimalPeriod_pos hn
  have hPdvd : P ∣ n := hper.minimalPeriod_dvd
  have hPx : ∀ e : Fin n, x (e + (P : Fin n)) = x e := fun e => by
    rw [← cycleRotPerm_iterate_apply n q hn P x e, Function.iterate_minimalPeriod]
  have hsum := sum_of_periodic n q x P hPdvd hPx
  rw [hx] at hsum
  have hcop : Nat.Coprime (n / P) q :=
    (ZMod.isUnit_iff_coprime _ q).mp (IsUnit.of_mul_eq_one _ hsum.symm)
  obtain ⟨_, _, hmax⟩ := coprimePart_spec n q hn
  have hle : n / P ≤ coprimePart n q := hmax _ (Nat.div_dvd_of_dvd hPdvd) hcop
  have hnP : 0 < n / P := Nat.div_pos (Nat.le_of_dvd hn hPdvd) hPpos
  have hge : n / coprimePart n q ≤ P :=
    calc n / coprimePart n q ≤ n / (n / P) := Nat.div_le_div_left hle hnP
      _ = P := Nat.div_div_self hPdvd hn.ne'
  have hsub : (Finset.range P).image (fun i => σ^[i] x) ⊆ stabOrbit (Multiplicative ℤ) y x := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    refine (mem_stabOrbit _).mpr
      ⟨Multiplicative.ofAdd (i : ℤ), cycle_mem_stabilizer n q hn _ y, ?_⟩
    rw [cycle_smul_apply]
    simp [σ, zpow_natCast, Equiv.Perm.coe_pow]
  have hcard : ((Finset.range P).image (fun i => σ^[i] x)).card = P := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj h
    exact Function.iterate_injOn_Iio_minimalPeriod (by simpa using hi) (by simpa using hj) h
  calc n / coprimePart n q ≤ P := hge
    _ = _ := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **The upper bound**: a cochain of winding one with a rotation orbit of
exactly `n / coprimePart n q` elements — `c⁻¹` on every `(n / c)`-th edge,
`c = coprimePart n q`. -/
theorem cycle_exists_small_orbit (y : IncidenceGraph.H1Reduction (cycleGraph n hn) q) :
    letI := cycleRotAction n q hn
    letI := cycleClassAction n q hn
    ∃ x : Fin n → ZMod q, ∑ e, x e = 1 ∧
      (stabOrbit (Multiplicative ℤ) y x).card ≤ n / coprimePart n q := by
  let := cycleRotAction n q hn
  let := cycleClassAction n q hn
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨hcdvd, hccop, hmax⟩ := coprimePart_spec n q hn
  set c := coprimePart n q
  set d := n / c
  have hcpos : 0 < c := Nat.pos_of_ne_zero fun h0 => by
    have := hmax 1 (one_dvd n) (Nat.coprime_one_left q); omega
  have hdpos : 0 < d := Nat.div_pos (Nat.le_of_dvd hn hcdvd) hcpos
  have hddvd : d ∣ n := Nat.div_dvd_of_dvd hcdvd
  have hdle : d ≤ n := Nat.le_of_dvd hn hddvd
  set σ := cycleRotPerm n q hn
  let x0 : Fin n → ZMod q := fun e => if d ∣ e.val then (c : ZMod q)⁻¹ else 0
  have hper : ∀ e : Fin n, x0 (e + (d : Fin n)) = x0 e := fun e => by
    have hdd : d ∣ d % n := (Nat.dvd_mod_iff hddvd).mpr dvd_rfl
    have : d ∣ (e + (d : Fin n)).val ↔ d ∣ e.val := by
      rw [Fin.val_add, Fin.val_natCast, Nat.dvd_mod_iff hddvd]
      exact (Nat.dvd_add_left hdd)
    simp only [x0, this]
  refine ⟨x0, ?_, ?_⟩
  · rw [sum_of_periodic n q x0 d hddvd hper, Nat.div_div_self hcdvd hn.ne']
    rw [Finset.sum_eq_single 0]
    · simp only [x0, Nat.cast_zero, Fin.val_zero, dvd_zero, ite_true]
      exact ZMod.coe_mul_inv_eq_one c hccop
    · intro i hi hi0
      have hi' : i < d := Finset.mem_range.mp hi
      have hval : ((i : Fin n)).val = i := by
        rw [Fin.val_natCast]; exact Nat.mod_eq_of_lt (by omega)
      simp only [x0, hval]
      rw [ite_eq_right]
      intro hdi
      exact hi0 (Nat.eq_zero_of_dvd_of_lt hdi hi')
    · intro h; exact absurd (Finset.mem_range.mpr hdpos) h
  · have hfix : (σ ^ d) x0 = x0 := by
      rw [Equiv.Perm.coe_pow]
      funext e
      rw [cycleRotPerm_iterate_apply, hper]
    have hsub : stabOrbit (Multiplicative ℤ) y x0 ⊆ (Finset.range d).image (fun i => σ^[i] x0) := by
      intro z hz
      obtain ⟨g, _, rfl⟩ := (mem_stabOrbit _).mp hz
      rw [cycle_smul_apply]
      set k := Multiplicative.toAdd g
      have hdz : (d : ℤ) ≠ 0 := by exact_mod_cast hdpos.ne'
      have hk : σ ^ k = σ ^ (k % (d : ℤ)) * (σ ^ d) ^ (k / (d : ℤ)) := by
        rw [← zpow_natCast, ← zpow_mul, ← zpow_add, mul_comm (d : ℤ), Int.emod_add_ediv_mul]
      have hnn : 0 ≤ k % (d : ℤ) := Int.emod_nonneg k hdz
      have hlt : k % (d : ℤ) < d := Int.emod_lt_of_pos k (by exact_mod_cast hdpos)
      refine Finset.mem_image.mpr ⟨(k % (d : ℤ)).toNat, Finset.mem_range.mpr (by omega), ?_⟩
      rw [hk, Equiv.Perm.mul_apply, Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hfix,
        ← Int.toNat_of_nonneg hnn, zpow_natCast, Equiv.Perm.coe_pow, Int.toNat_natCast]
    calc (stabOrbit (Multiplicative ℤ) y x0).card
        ≤ ((Finset.range d).image (fun i => σ^[i] x0)).card := Finset.card_le_card hsub
      _ ≤ (Finset.range d).card := Finset.card_image_le
      _ = d := Finset.card_range d

/-- **THE CYCLE'S PRICE** (the exact law): under the rotation's `ℤ`-action,
the price of symmetric choice of the winding-one class of `C_n` at
resolution `q` is `log (n / coprimePart n q)` — the log of the part of `n`
that shares its primes with `q`. It vanishes exactly at coprimality. -/
theorem cycle_symmetricChoicePrice_eq :
    letI := cycleRotAction n q hn
    letI := cycleClassAction n q hn
    symmetricChoicePrice (Multiplicative ℤ)
        ((cycleGraph n hn).carrierCompression q)
        ((cycleGraph n hn).carrierCompression q (Pi.single ⟨0, hn⟩ 1))
      = Real.log (n / coprimePart n q : ℕ) := by
  let := cycleRotAction n q hn
  let := cycleClassAction n q hn
  set y : IncidenceGraph.H1Reduction (cycleGraph n hn) q :=
    (cycleGraph n hn).carrierCompression q (Pi.single ⟨0, hn⟩ 1)
  unfold symmetricChoicePrice
  congr 2
  apply le_antisymm
  · obtain ⟨x0, hx0, hcard⟩ := cycle_exists_small_orbit n q hn y
    exact (orbitFloor_le ((cycle_fiber_iff n q hn x0).mpr hx0)).trans hcard
  · obtain ⟨x, hx, hc⟩ := orbitFloor_spec (Γ := Multiplicative ℤ)
      (p := (cycleGraph n hn).carrierCompression q) (y := y) ⟨Pi.single ⟨0, hn⟩ 1, rfl⟩
    rw [← hc]
    exact cycle_le_card_stabOrbit n q hn x ((cycle_fiber_iff n q hn x).mp hx) y

omit [NeZero q] in
theorem coprimePart_four_two : coprimePart 4 2 = 1 := by decide

/-- **The witness, priced**: at `(n, q) = (4, 2)` the price is `log 4` —
the whole ring, since `4` shares every prime with `2`. -/
theorem cycle_four_two_symmetricChoicePrice :
    letI := cycleRotAction 4 2 (Nat.succ_pos 3)
    letI := cycleClassAction 4 2 (Nat.succ_pos 3)
    symmetricChoicePrice (Multiplicative ℤ)
        ((cycleGraph 4 (Nat.succ_pos 3)).carrierCompression 2)
        ((cycleGraph 4 (Nat.succ_pos 3)).carrierCompression 2 (Pi.single ⟨0, Nat.succ_pos 3⟩ 1))
      = Real.log 4 := by
  rw [cycle_symmetricChoicePrice_eq, coprimePart_four_two]
  norm_num

end Cycle

end Meno
