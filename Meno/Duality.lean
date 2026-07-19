import Meno.Groupoid
import Meno.Fluctuation
import Meno.PeriodHarmonic
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Fourier Duality on GroupoidObj

Lifts the analytic T-duality (Theta.lean) to a structural operation on GroupoidObj:
for quadratic energy α·k² on ℤ-endomorphisms, the Fourier dual has coupling π²/α.
The dual construction is involutive. -/

namespace Simplicial

open UpperHalfPlane CategoryTheory

/-! ## Generalized quadratic partition function -/

noncomputable def quadraticPartFn (α : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp (-α * (k : ℝ) ^ 2)

theorem quadraticPartFn_eq_partitionFn (n : ℕ) (hn : n ≥ 3) :
    quadraticPartFn (1 / ↑n) = partitionFn n hn := by
  simp only [quadraticPartFn, partitionFn]; congr 1; ext k; congr 1; ring

/-! ## Generalized T-duality, inherited from the spine

The modular S-transformation proof lives in **one** place:
`Meno.QuadraticAction.scalarPartFn_duality`. `quadraticPartFn` is
definitionally the spine's scalar partition function, so the duality
here is a name-transport, not an independent analytic theorem. -/

/-- `quadraticPartFn` *is* the spine's scalar partition function. One
analytic object, two historical names. -/
theorem quadraticPartFn_eq_scalarPartFn (α : ℝ) :
    quadraticPartFn α = Meno.QuadraticAction.scalarPartFn α := rfl

theorem quadraticPartFn_duality (α : ℝ) (hα : 0 < α) :
    (↑(quadraticPartFn (Real.pi ^ 2 / α)) : ℂ) =
    ↑(α / Real.pi : ℝ) ^ ((1 : ℂ) / 2) * ↑(quadraticPartFn α) := by
  rw [quadraticPartFn_eq_scalarPartFn, quadraticPartFn_eq_scalarPartFn]
  exact Meno.QuadraticAction.scalarPartFn_duality α hα

/-! ## Fourier dual of a GroupoidObj -/

noncomputable def GroupoidObj.dual
    (E : GroupoidObj) (wind : End E.base ≃ ℤ) (α : ℝ) (hα : 0 < α)
    (_hK : ∀ g, E.energy g = α * (wind g : ℝ) ^ 2) : GroupoidObj where
  G := E.G
  base := E.base
  energy g := (Real.pi ^ 2 / α) * (wind g : ℝ) ^ 2
  summable := by
    have h := Meno.QuadraticAction.summable_scalarPartFn (Real.pi ^ 2 / α)
      (div_pos (sq_pos_of_pos Real.pi_pos) hα)
    exact (wind.summable_iff.mpr h).congr fun g => by simp only [Function.comp_apply, neg_mul]

/-- Partition function of any `GroupoidObj` with quadratic energy `α·(wind g)²` over a
    `ℤ`-valued winding equivalence equals the canonical `quadraticPartFn α`. This is the
    generic bridge between the abstract groupoid invariant and the analytic series. -/
theorem partFn_eq_quadraticPartFn
    (E : GroupoidObj) (wind : End E.base ≃ ℤ) (α : ℝ)
    (hK : ∀ g, E.energy g = α * (wind g : ℝ) ^ 2) :
    E.partFn = quadraticPartFn α := by
  unfold GroupoidObj.partFn groupoidPartitionFn quadraticPartFn
  conv_lhs =>
    rw [show (fun g => Real.exp (-E.energy g)) =
        (fun k : ℤ => Real.exp (-α * (k : ℝ) ^ 2)) ∘ wind from by
      ext g; simp only [Function.comp_apply]; rw [hK g]; ring_nf]
  exact Equiv.tsum_eq wind (fun k : ℤ => Real.exp (-α * (k : ℝ) ^ 2))

theorem GroupoidObj.dual_partFn
    (E : GroupoidObj) (wind : End E.base ≃ ℤ) (α : ℝ) (hα : 0 < α)
    (hK : ∀ g, E.energy g = α * (wind g : ℝ) ^ 2) :
    (↑((E.dual wind α hα hK).partFn) : ℂ) =
    ↑(α / Real.pi : ℝ) ^ ((1 : ℂ) / 2) * ↑E.partFn := by
  have hK' : ∀ g, (E.dual wind α hα hK).energy g = (Real.pi ^ 2 / α) * (wind g : ℝ) ^ 2 :=
    fun g => rfl
  rw [partFn_eq_quadraticPartFn (E.dual wind α hα hK) wind _ hK']
  rw [partFn_eq_quadraticPartFn E wind α hK]
  exact quadraticPartFn_duality α hα

theorem GroupoidObj.dual_dual_equiv
    (E : GroupoidObj) (wind : End E.base ≃ ℤ) (α : ℝ) (hα : 0 < α)
    (hK : ∀ g, E.energy g = α * (wind g : ℝ) ^ 2) :
    GroupoidObj.Equiv
      ((E.dual wind α hα hK).dual wind (Real.pi ^ 2 / α)
        (div_pos (sq_pos_of_pos Real.pi_pos) hα) (fun _ => rfl))
      E := by
  refine ⟨MulEquiv.refl _, fun _ => ?_⟩
  simp only [MulEquiv.refl_apply, GroupoidObj.dual]
  rw [hK]; congr 1
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hpi0 : Real.pi ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos Real.pi_pos)
  field_simp

/-! ## Canonical quadratic family

For each coupling `α > 0`, `quadraticObj α hα` is the canonical `GroupoidObj` whose
underlying groupoid is `SingleObj (Multiplicative ℤ)` — one object with endomorphism
group ℤ — equipped with energy `α · k²` where `k` is the winding. Its partition
function is exactly `quadraticPartFn α`, and its Fourier dual is equivalent to
`quadraticObj (π²/α)`. This is the ℤ-modal family on which T-duality acts. -/

/-- Canonical winding equivalence on the one-object groupoid `SingleObj (Multiplicative ℤ)`:
    endomorphisms of the unique object correspond to integers. -/
noncomputable def quadraticWind :
    End (CategoryTheory.SingleObj.star (Multiplicative ℤ)) ≃ ℤ :=
  (CategoryTheory.SingleObj.toEnd (Multiplicative ℤ)).symm.toEquiv.trans Multiplicative.toAdd

/-- Canonical quadratic groupoid object at coupling `α`: the one-object groupoid whose
    endomorphism group is ℤ, with energy `α · (winding)²`. -/
noncomputable def quadraticObj (α : ℝ) (hα : 0 < α) : GroupoidObj where
  G := CategoryTheory.SingleObj (Multiplicative ℤ)
  base := CategoryTheory.SingleObj.star (Multiplicative ℤ)
  energy g := α * (quadraticWind g : ℝ) ^ 2
  summable := by
    have h := Meno.QuadraticAction.summable_scalarPartFn α hα
    exact (quadraticWind.summable_iff.mpr h).congr fun g => by
      simp only [Function.comp_apply, neg_mul]

/-- Energy of `quadraticObj α` is `α · (winding)²` — definitionally. -/
theorem quadraticObj_energy (α : ℝ) (hα : 0 < α)
    (g : End (quadraticObj α hα).base) :
    (quadraticObj α hα).energy g = α * (quadraticWind g : ℝ) ^ 2 :=
  rfl

/-- Partition function of `quadraticObj α` is `quadraticPartFn α`. -/
theorem quadraticObj_partFn (α : ℝ) (hα : 0 < α) :
    (quadraticObj α hα).partFn = quadraticPartFn α :=
  partFn_eq_quadraticPartFn (quadraticObj α hα) quadraticWind α (quadraticObj_energy α hα)

/-- Fourier dual of `quadraticObj α` (taken with its canonical winding) is equivalent
    to `quadraticObj (π²/α)` — the duality maps the canonical family to itself with
    coupling inverted under T-duality. -/
theorem quadraticObj_dual_equiv (α : ℝ) (hα : 0 < α) :
    GroupoidObj.Equiv
      ((quadraticObj α hα).dual quadraticWind α hα (quadraticObj_energy α hα))
      (quadraticObj (Real.pi ^ 2 / α) (div_pos (sq_pos_of_pos Real.pi_pos) hα)) :=
  ⟨MulEquiv.refl _, fun _ => rfl⟩

/-! ## Gibbs Measure on GroupoidObj

For a groupoid object `E`, the Gibbs density on automorphisms is
`gibbsMass E g = exp(-E.energy g) / E.partFn`.  It is nonnegative, summable,
and sums to `1` — a probability density on `End E.base`.  The Gibbs expectation
of an observable `f : End E.base → ℝ` is `gibbsExpect E f = ∑' g, f g * gibbsMass E g`;
the Gibbs variance is `⟨f²⟩ − ⟨f⟩²`.  All three depend only on the groupoid-level
data `(E.base, E.energy, E.summable)` plus the strict positivity `E.partFn > 0`. -/

/-- Gibbs probability density on automorphisms: `exp(-E.energy g) / E.partFn`. -/
noncomputable def GroupoidObj.gibbsMass (E : GroupoidObj) (g : End E.base) : ℝ :=
  Real.exp (-E.energy g) / E.partFn

/-- Gibbs expectation of `f : End E.base → ℝ` against the Gibbs density. -/
noncomputable def GroupoidObj.gibbsExpect (E : GroupoidObj) (f : End E.base → ℝ) : ℝ :=
  ∑' g, f g * E.gibbsMass g

/-- Gibbs variance of `f` under the Gibbs density: `⟨f²⟩ − ⟨f⟩²`. -/
noncomputable def GroupoidObj.gibbsVariance (E : GroupoidObj) (f : End E.base → ℝ) : ℝ :=
  E.gibbsExpect (fun g => f g ^ 2) - (E.gibbsExpect f) ^ 2

/-- **Audit identification (C12)**: the groupoid Gibbs machinery *is*
the sector action's, through the loop-kernel bridge — definitionally.
Retained as groupoid-facing wrappers; the analytic source of truth is
`SectorAction`. -/
theorem GroupoidObj.gibbsMass_eq_sector (E : GroupoidObj)
    (h_id : E.energy (𝟙 E.base) = 0) (h_nonneg : ∀ g, 0 ≤ E.energy g)
    (g : End E.base) :
    E.gibbsMass g
      = (E.toLoopKernelObj h_id h_nonneg).toSectorAction.gibbsMass g := rfl

theorem GroupoidObj.gibbsExpect_eq_sector (E : GroupoidObj)
    (h_id : E.energy (𝟙 E.base) = 0) (h_nonneg : ∀ g, 0 ≤ E.energy g)
    (f : End E.base → ℝ) :
    E.gibbsExpect f
      = (E.toLoopKernelObj h_id h_nonneg).toSectorAction.gibbsExpect f := rfl

/-- Partition function positivity packaged at the `GroupoidObj` level. -/
theorem GroupoidObj.partFn_pos (E : GroupoidObj) : 0 < E.partFn :=
  groupoidPartitionFn_pos (x := E.base) (K := E.energy) (hsum := E.summable)

/-- The Gibbs density is nonnegative. -/
theorem GroupoidObj.gibbsMass_nonneg (E : GroupoidObj) (g : End E.base) :
    0 ≤ E.gibbsMass g :=
  div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt E.partFn_pos)

/-- The Gibbs density is summable (division of `E.summable` by a constant). -/
theorem GroupoidObj.summable_gibbsMass (E : GroupoidObj) :
    Summable E.gibbsMass := by
  unfold GroupoidObj.gibbsMass
  exact E.summable.div_const _

/-- The Gibbs density integrates to `1`: it is a probability density on
    `End E.base`. -/
theorem GroupoidObj.tsum_gibbsMass (E : GroupoidObj) :
    ∑' g : End E.base, E.gibbsMass g = 1 := by
  have hZ_ne : E.partFn ≠ 0 := ne_of_gt E.partFn_pos
  show ∑' g, Real.exp (-E.energy g) / E.partFn = 1
  rw [tsum_div_const]
  exact div_self hZ_ne

/-! ## Complexity-Rank Bound

T-duality converts the vacuum bound Z ≥ 1 into a nontrivial lower bound on
the partition function: Z(α) ≥ √(π/α). Taking logs gives a complexity floor
that grows with topological rank. -/

theorem quadraticPartFn_gt_one (α : ℝ) (hα : 0 < α) : quadraticPartFn α > 1 := by
  rw [quadraticPartFn_eq_scalarPartFn]
  exact Meno.QuadraticAction.scalarPartFn_gt_one α hα

theorem quadraticPartFn_duality_real (α : ℝ) (hα : 0 < α) :
    quadraticPartFn (Real.pi ^ 2 / α) =
    (α / Real.pi) ^ ((1 : ℝ) / 2) * quadraticPartFn α := by
  rw [quadraticPartFn_eq_scalarPartFn, quadraticPartFn_eq_scalarPartFn]
  exact Meno.QuadraticAction.scalarPartFn_duality_real α hα

theorem quadraticPartFn_lower_bound (α : ℝ) (hα : 0 < α) :
    quadraticPartFn α ≥ (Real.pi / α) ^ ((1 : ℝ) / 2) := by
  have hαπ : 0 < α / Real.pi := div_pos hα Real.pi_pos
  have hge := le_of_lt (quadraticPartFn_gt_one (Real.pi ^ 2 / α)
    (div_pos (sq_pos_of_pos Real.pi_pos) hα))
  rw [quadraticPartFn_duality_real α hα] at hge
  have hprod : (Real.pi / α) ^ ((1:ℝ)/2) * (α / Real.pi) ^ ((1:ℝ)/2) = 1 := by
    rw [← Real.mul_rpow (le_of_lt (div_pos Real.pi_pos hα)) (le_of_lt hαπ)]
    have : Real.pi / α * (α / Real.pi) = 1 := by field_simp
    rw [this, Real.one_rpow]
  nlinarith [Real.rpow_pos_of_pos (div_pos Real.pi_pos hα) ((1:ℝ)/2),
             mul_comm ((α / Real.pi) ^ ((1:ℝ)/2)) (quadraticPartFn α)]

theorem complexity_rank_bound (α : ℝ) (hα : 0 < α) :
    Real.log (quadraticPartFn α) ≥ (1 / 2) * Real.log (Real.pi / α) := by
  have hπα : 0 < Real.pi / α := div_pos Real.pi_pos hα
  calc Real.log (quadraticPartFn α)
      ≥ Real.log ((Real.pi / α) ^ ((1 : ℝ) / 2)) :=
        Real.log_le_log (Real.rpow_pos_of_pos hπα _) (quadraticPartFn_lower_bound α hα)
    _ = (1 / 2) * Real.log (Real.pi / α) :=
        Real.log_rpow hπα _

theorem GroupoidObj.complexity_ge (E : GroupoidObj) (wind : End E.base ≃ ℤ)
    (α : ℝ) (hα : 0 < α) (hK : ∀ g, E.energy g = α * (wind g : ℝ) ^ 2) :
    E.complexity ≥ (1 / 2) * Real.log (Real.pi / α) := by
  simp only [GroupoidObj.complexity, groupoidComplexity]
  rw [show groupoidPartitionFn E.base E.energy E.summable = quadraticPartFn α from
    partFn_eq_quadraticPartFn E wind α hK]
  exact complexity_rank_bound α hα

theorem cycle_complexity_ge (E : GroupoidObj) (wind : End E.base ≃ ℤ)
    (n : ℕ) (hn : 0 < n) (hK : ∀ g, E.energy g = (wind g : ℝ) ^ 2 / n) :
    E.complexity ≥ (1 / 2) * Real.log (Real.pi * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hα : (0 : ℝ) < 1 / n := div_pos one_pos hn0
  have hK' : ∀ g, E.energy g = (1 / ↑n) * (wind g : ℝ) ^ 2 := fun g => by rw [hK]; ring
  have h := GroupoidObj.complexity_ge E wind (1 / ↑n) hα hK'
  convert h using 2
  have : (0 : ℝ) < n := hn0
  field_simp

/-- Canonical cycle object complexity lower bound with no external `hK`.
(`cycleCanonicalObj` itself now lives upstream in `Groupoid.lean`,
where it feeds the spine through `cycleLoopKernel`.) -/
theorem cycleCanonicalObj_complexity_ge (n : ℕ) (hn : n ≥ 3) :
    (cycleCanonicalObj n hn).complexity ≥ (1 / 2) * Real.log (Real.pi * n) := by
  have hn0 : 0 < n := by omega
  refine cycle_complexity_ge
    (E := cycleCanonicalObj n hn)
    (wind := cycleLoopClassEquivInt_base n hn)
    (n := n) (hn := hn0) ?_
  intro g
  simpa [cycleCanonicalObj, cycleCanonicalWinding, cycleBaseObj] using
    (cycleCanonicalEnergy_eq_winding_sq n hn (cycleBaseObj n hn) g)

theorem rank_complexity_bound (E₁ E₂ : GroupoidObj)
    (wind₁ : End E₁.base ≃ ℤ) (wind₂ : End E₂.base ≃ ℤ)
    (n₁ n₂ : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hK₁ : ∀ g, E₁.energy g = (wind₁ g : ℝ) ^ 2 / n₁)
    (hK₂ : ∀ g, E₂.energy g = (wind₂ g : ℝ) ^ 2 / n₂) :
    (E₁.prod E₂).complexity ≥
    (1 / 2) * Real.log (Real.pi * n₁) + (1 / 2) * Real.log (Real.pi * n₂) := by
  rw [GroupoidObj.prod_complexity]
  exact add_le_add (cycle_complexity_ge E₁ wind₁ n₁ hn₁ hK₁)
                   (cycle_complexity_ge E₂ wind₂ n₂ hn₂ hK₂)

/-! ## Complexity Decomposition

The duality identity decomposes complexity into a topological part
(1/2)·log(π/α), determined by the coupling alone, plus a strictly positive
dual residual log(Z(π²/α)) that vanishes exponentially as α → 0. -/

theorem complexity_decomposition (α : ℝ) (hα : 0 < α) :
    Real.log (quadraticPartFn α) =
    (1 / 2) * Real.log (Real.pi / α) +
    Real.log (quadraticPartFn (Real.pi ^ 2 / α)) := by
  have hαπ : 0 < α / Real.pi := div_pos hα Real.pi_pos
  have hπα : 0 < Real.pi / α := div_pos Real.pi_pos hα
  have hZ : 0 < quadraticPartFn α := lt_trans one_pos (quadraticPartFn_gt_one α hα)
  have hpf : 0 < (α / Real.pi) ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hαπ _
  have hlog : Real.log (quadraticPartFn (Real.pi ^ 2 / α)) =
      (1/2) * Real.log (α / Real.pi) + Real.log (quadraticPartFn α) := by
    rw [quadraticPartFn_duality_real α hα,
        Real.log_mul (ne_of_gt hpf) (ne_of_gt hZ), Real.log_rpow hαπ]
  have hsum : Real.log (Real.pi / α) + Real.log (α / Real.pi) = 0 := by
    rw [← Real.log_mul (ne_of_gt hπα) (ne_of_gt hαπ)]
    have : Real.pi / α * (α / Real.pi) = 1 := by field_simp
    rw [this, Real.log_one]
  linarith

theorem complexity_gap_pos (α : ℝ) (hα : 0 < α) :
    Real.log (quadraticPartFn (Real.pi ^ 2 / α)) > 0 :=
  Real.log_pos (quadraticPartFn_gt_one _ (div_pos (sq_pos_of_pos Real.pi_pos) hα))

/-! ## Self-Dual Fixed Point

At coupling α = π, the dual coupling π²/α = π. The object is its own
Fourier dual — the description and its dual description coincide. -/

theorem GroupoidObj.self_dual (E : GroupoidObj) (wind : End E.base ≃ ℤ)
    (hK : ∀ g, E.energy g = Real.pi * (wind g : ℝ) ^ 2) :
    GroupoidObj.Equiv (E.dual wind Real.pi Real.pi_pos hK) E := by
  refine ⟨MulEquiv.refl _, fun g => ?_⟩
  simp only [MulEquiv.refl_apply, GroupoidObj.dual, hK]
  have : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp

/-- The self-dual coupling is unique: Z(π²/α) = Z(α) if and only if α = π. -/
theorem quadraticPartFn_self_dual_iff (α : ℝ) (hα : 0 < α) :
    quadraticPartFn (Real.pi ^ 2 / α) = quadraticPartFn α ↔ α = Real.pi := by
  constructor
  · intro h
    have hdual := quadraticPartFn_duality_real α hα
    rw [h] at hdual
    have hαπ : 0 < α / Real.pi := div_pos hα Real.pi_pos
    have hZpos : 0 < quadraticPartFn α :=
      lt_trans zero_lt_one (quadraticPartFn_gt_one α hα)
    have hlog := congr_arg Real.log hdual
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hαπ _)) (ne_of_gt hZpos),
        Real.log_rpow hαπ] at hlog
    have : Real.log (α / Real.pi) = 0 := by linarith
    rcases Real.log_eq_zero.mp this with h3 | h3 | h3
    · linarith
    · linarith [(div_eq_iff (ne_of_gt Real.pi_pos)).mp h3]
    · linarith
  · intro h; subst h
    show quadraticPartFn (Real.pi ^ 2 / Real.pi) = quadraticPartFn Real.pi
    congr 1; have : Real.pi ≠ 0 := ne_of_gt Real.pi_pos; field_simp

/-- Sub-critical regime: the dual has smaller partition function iff α < π. -/
theorem dual_partFn_lt_iff (α : ℝ) (hα : 0 < α) :
    quadraticPartFn (Real.pi ^ 2 / α) < quadraticPartFn α ↔ α < Real.pi := by
  have hdual := quadraticPartFn_duality_real α hα
  have hZpos : 0 < quadraticPartFn α :=
    lt_trans zero_lt_one (quadraticPartFn_gt_one α hα)
  have hαπ : 0 < α / Real.pi := div_pos hα Real.pi_pos
  rw [hdual, mul_lt_iff_lt_one_left hZpos]
  constructor
  · intro h
    by_contra hle; push_neg at hle
    have : 1 ≤ α / Real.pi := by rwa [le_div_iff₀ Real.pi_pos, one_mul]
    linarith [Real.one_le_rpow this (by norm_num : (0:ℝ) ≤ 1/2)]
  · intro h
    exact Real.rpow_lt_one (le_of_lt hαπ) (by rwa [div_lt_one Real.pi_pos]) (by norm_num)

/-! ## Duality Flow

The duality flow D(α) = log Z(α) - log Z(π²/α) measures asymmetry between
an object and its Fourier dual. The complexity decomposition gives
D(α) = (1/2)·log(π/α) in closed form. -/

noncomputable def dualityFlow (α : ℝ) : ℝ :=
  Real.log (quadraticPartFn α) - Real.log (quadraticPartFn (Real.pi ^ 2 / α))

theorem duality_flow_eq (α : ℝ) (hα : 0 < α) :
    dualityFlow α = (1 / 2) * Real.log (Real.pi / α) := by
  unfold dualityFlow
  linarith [complexity_decomposition α hα]

theorem duality_flow_antisymmetric (α : ℝ) (hα : 0 < α) :
    dualityFlow (Real.pi ^ 2 / α) =
    -dualityFlow α := by
  rw [duality_flow_eq α hα,
      duality_flow_eq _ (div_pos (sq_pos_of_pos Real.pi_pos) hα)]
  rw [show Real.pi / (Real.pi ^ 2 / α) = α / Real.pi from by field_simp]
  rw [Real.log_div (ne_of_gt hα) (ne_of_gt Real.pi_pos),
      Real.log_div (ne_of_gt Real.pi_pos) (ne_of_gt hα)]
  ring

theorem duality_flow_pos_iff (α : ℝ) (hα : 0 < α) :
    0 < dualityFlow α ↔ α < Real.pi := by
  rw [duality_flow_eq α hα]
  constructor
  · intro h
    have hlog : 0 < Real.log (Real.pi / α) := by nlinarith
    rwa [Real.log_pos_iff (le_of_lt (div_pos Real.pi_pos hα)),
         one_lt_div hα] at hlog
  · intro h
    have := Real.log_pos ((one_lt_div hα).mpr h)
    nlinarith

theorem duality_flow_zero_iff (α : ℝ) (hα : 0 < α) :
    dualityFlow α = 0 ↔ α = Real.pi := by
  rw [duality_flow_eq α hα]
  constructor
  · intro h
    have hlog : Real.log (Real.pi / α) = 0 := by nlinarith
    rcases Real.log_eq_zero.mp hlog with h1 | h1 | h1
    · linarith [div_pos Real.pi_pos hα]
    · linarith [(div_eq_one_iff_eq (ne_of_gt hα)).mp h1]
    · linarith [div_pos Real.pi_pos hα]
  · intro h; subst h
    simp [Real.log_one]

/-! ## Variational Principle

The self-dual point α = π minimizes the total complexity of any dual pair:
Z(π)² ≤ Z(α) · Z(π²/α). Equivalently, among all objects and their Fourier
duals, the self-dual pair has the smallest combined descriptive cost. -/

theorem quadraticPartFn_strictAnti :
    StrictAntiOn quadraticPartFn (Set.Ioi 0) := by
  intro α (hα : 0 < α) β (hβ : 0 < β) (hlt : α < β)
  show quadraticPartFn β < quadraticPartFn α
  simp only [quadraticPartFn]
  exact Summable.tsum_lt_tsum (i := (1 : ℤ))
    (fun k => Real.exp_le_exp_of_le (by nlinarith [sq_nonneg (k : ℝ)]))
    (Real.exp_lt_exp.mpr (by push_cast; nlinarith))
    (Meno.QuadraticAction.summable_scalarPartFn β hβ)
    (Meno.QuadraticAction.summable_scalarPartFn α hα)

theorem dual_pair_product (α : ℝ) (hα : 0 < α) :
    quadraticPartFn α * quadraticPartFn (Real.pi ^ 2 / α) =
    (α / Real.pi) ^ ((1 : ℝ) / 2) * quadraticPartFn α ^ 2 := by
  rw [quadraticPartFn_duality_real α hα]; ring

/-! ### The scalar family as the rank-one chart (review #15)

The scalar quadratic family `β ↦ ∑' k : ℤ, exp(−β·k²)` is the
rank-one instance of the rank-generic inverse-temperature engine
(`Meno/Fluctuation.lean`): the unit quadratic action `k ↦ k²` scales
to it, and the differentiation lemmas below are the general
`Z′ = −M₁`, `M₁′ = −M₂` read through the chart `(Fin 1 → ℤ) ≃ ℤ` —
the analytic engine exists once, at every rank. -/

/-- The rank-one unit quadratic action `k ↦ k²`. -/
noncomputable def unitQuadAction : Meno.QuadraticAction 1 where
  Q := !![1]
  Q_posDef := Meno.posDef_fin_one 1 one_pos

private def zEquiv : (Fin 1 → ℤ) ≃ ℤ := Equiv.funUnique (Fin 1) ℤ

private lemma unitQuadAction_energy (k : Fin 1 → ℤ) :
    unitQuadAction.energy k = ((k 0 : ℝ)) ^ 2 := by
  show ∑ i, ∑ j, (!![(1 : ℝ)]) i j * (k i : ℝ) * (k j : ℝ) = _
  have h : (!![(1 : ℝ)]) 0 0 = 1 := rfl
  rw [Fin.sum_univ_one, Fin.sum_univ_one, h]
  ring

private lemma scaledPartFn_unit (β : ℝ) :
    unitQuadAction.scaledPartFn β = quadraticPartFn β := by
  refine (Equiv.tsum_eq zEquiv.symm
    (fun k : Fin 1 → ℤ =>
      Real.exp (-(β * unitQuadAction.energy k)))).symm.trans ?_
  refine tsum_congr fun n => ?_
  rw [unitQuadAction_energy]
  show Real.exp (-(β * (n : ℝ) ^ 2)) = Real.exp (-β * (n : ℝ) ^ 2)
  rw [show -(β * (n : ℝ) ^ 2) = -β * (n : ℝ) ^ 2 from by ring]

private lemma scaledMoment_unit (β : ℝ) :
    unitQuadAction.scaledMoment β
      = ∑' k : ℤ, (k : ℝ) ^ 2 * Real.exp (-β * (k : ℝ) ^ 2) := by
  refine (Equiv.tsum_eq zEquiv.symm
    (fun k : Fin 1 → ℤ => unitQuadAction.energy k
      * Real.exp (-(β * unitQuadAction.energy k)))).symm.trans ?_
  refine tsum_congr fun n => ?_
  rw [unitQuadAction_energy]
  show (n : ℝ) ^ 2 * Real.exp (-(β * (n : ℝ) ^ 2)) = _
  rw [show -(β * (n : ℝ) ^ 2) = -β * (n : ℝ) ^ 2 from by ring]

private lemma scaledMoment2_unit (β : ℝ) :
    unitQuadAction.scaledMoment2 β
      = ∑' k : ℤ, (k : ℝ) ^ 4 * Real.exp (-β * (k : ℝ) ^ 2) := by
  refine (Equiv.tsum_eq zEquiv.symm
    (fun k : Fin 1 → ℤ => unitQuadAction.energy k ^ 2
      * Real.exp (-(β * unitQuadAction.energy k)))).symm.trans ?_
  refine tsum_congr fun n => ?_
  rw [unitQuadAction_energy]
  show ((n : ℝ) ^ 2) ^ 2 * Real.exp (-(β * (n : ℝ) ^ 2)) = _
  rw [show -(β * (n : ℝ) ^ 2) = -β * (n : ℝ) ^ 2 from by ring,
    show ((n : ℝ) ^ 2) ^ 2 = (n : ℝ) ^ 4 from by ring]

private lemma summable_sq_mul_exp (β : ℝ) (hβ : 0 < β) :
    Summable (fun k : ℤ => (k : ℝ) ^ 2 * Real.exp (-β * (k : ℝ) ^ 2)) := by
  have h := (Equiv.summable_iff zEquiv.symm).mpr
    (unitQuadAction.summable_energy_mul_scaledWeight hβ)
  refine h.congr fun n => ?_
  show unitQuadAction.energy (zEquiv.symm n)
      * Real.exp (-(β * unitQuadAction.energy (zEquiv.symm n))) = _
  rw [unitQuadAction_energy]
  show (n : ℝ) ^ 2 * Real.exp (-(β * (n : ℝ) ^ 2)) = _
  rw [show -(β * (n : ℝ) ^ 2) = -β * (n : ℝ) ^ 2 from by ring]

private lemma summable_pow4_mul_exp (β : ℝ) (hβ : 0 < β) :
    Summable (fun k : ℤ => (k : ℝ) ^ 4 * Real.exp (-β * (k : ℝ) ^ 2)) := by
  have h := (Equiv.summable_iff zEquiv.symm).mpr
    (unitQuadAction.summable_energy_sq_mul_scaledWeight hβ)
  refine h.congr fun n => ?_
  show unitQuadAction.energy (zEquiv.symm n) ^ 2
      * Real.exp (-(β * unitQuadAction.energy (zEquiv.symm n))) = _
  rw [unitQuadAction_energy]
  show ((n : ℝ) ^ 2) ^ 2 * Real.exp (-(β * (n : ℝ) ^ 2)) = _
  rw [show -(β * (n : ℝ) ^ 2) = -β * (n : ℝ) ^ 2 from by ring,
    show ((n : ℝ) ^ 2) ^ 2 = (n : ℝ) ^ 4 from by ring]

private lemma hasDerivAt_quadraticPartFn (β : ℝ) (hβ : 0 < β) :
    HasDerivAt quadraticPartFn
      (∑' k : ℤ, -(k : ℝ) ^ 2 * Real.exp (-β * (k : ℝ) ^ 2)) β := by
  have h := unitQuadAction.hasDerivAt_scaledPartFn hβ
  rw [show unitQuadAction.scaledPartFn = quadraticPartFn from
    funext scaledPartFn_unit] at h
  convert h using 1
  rw [scaledMoment_unit β, ← tsum_neg]
  exact tsum_congr fun k => by ring

/-- Derivative of `M₂(β) := ∑' k, k²·exp(-βk²)` equals `-M₄(β)` — the
general `M₁′ = −M₂` at the unit action. -/
private lemma hasDerivAt_M₂ (β : ℝ) (hβ : 0 < β) :
    HasDerivAt (fun α => ∑' k : ℤ, (k : ℝ) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2))
      (∑' k : ℤ, -(k : ℝ) ^ 4 * Real.exp (-β * (k : ℝ) ^ 2)) β := by
  have h := unitQuadAction.hasDerivAt_scaledMoment hβ
  rw [show unitQuadAction.scaledMoment
      = fun α => ∑' k : ℤ, (k : ℝ) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2) from
    funext scaledMoment_unit] at h
  convert h using 1
  rw [scaledMoment2_unit β, ← tsum_neg]
  exact tsum_congr fun k => by ring

private lemma summable_N_summand (β : ℝ) (hβ : 0 < β) :
    Summable (fun k : ℤ => (1 - 4 * β * (k : ℝ) ^ 2) * Real.exp (-β * (k : ℝ) ^ 2)) := by
  have h1 := Meno.QuadraticAction.summable_scalarPartFn β hβ
  have h2 := (summable_sq_mul_exp β hβ).mul_left (4 * β)
  exact (h1.sub h2).congr fun k => by ring

/-- N(π) = 0: differentiating Z(π²/α) = √(α/π)·Z(α) at α = π gives ⟨k²⟩_π = 1/(4π). -/
private lemma N_self_dual :
    ∑' k : ℤ, (1 - 4 * Real.pi * (k : ℝ) ^ 2) *
      Real.exp (-Real.pi * (k : ℝ) ^ 2) = 0 := by
  set Z'π := ∑' k : ℤ, -(k : ℝ) ^ 2 * Real.exp (-Real.pi * (k : ℝ) ^ 2)
  have hπ_pos := Real.pi_pos
  have hπ_ne := ne_of_gt hπ_pos
  have hZ := hasDerivAt_quadraticPartFn Real.pi hπ_pos
  have h_inv : HasDerivAt (fun α : ℝ => Real.pi ^ 2 / α) (-1) Real.pi := by
    have h := (hasDerivAt_const Real.pi (Real.pi ^ 2)).div
      (hasDerivAt_id Real.pi) hπ_ne
    simp only [id] at h; convert h using 1; field_simp; ring
  have hZ_at : HasDerivAt quadraticPartFn Z'π (Real.pi ^ 2 / Real.pi) := by
    rwa [show Real.pi ^ 2 / Real.pi = Real.pi from by field_simp]
  have hLHS := hZ_at.comp Real.pi h_inv
  have h_div : HasDerivAt (fun α : ℝ => α / Real.pi) (1 / Real.pi) Real.pi := by
    simpa using (hasDerivAt_id Real.pi).div_const Real.pi
  have h_rpow : HasDerivAt (fun α => (α / Real.pi) ^ ((1:ℝ)/2))
      (1 / Real.pi * ((1:ℝ)/2) * (Real.pi / Real.pi) ^ ((1:ℝ)/2 - 1)) Real.pi :=
    h_div.rpow_const (Or.inl (ne_of_gt (div_pos hπ_pos hπ_pos)))
  have hRHS := h_rpow.mul hZ
  have hfun : (fun α => (α / Real.pi) ^ ((1:ℝ)/2) * quadraticPartFn α) =ᶠ[nhds Real.pi]
      (quadraticPartFn ∘ fun α => Real.pi ^ 2 / α) := by
    filter_upwards [eventually_gt_nhds hπ_pos] with α hα
    exact (quadraticPartFn_duality_real α hα).symm
  have heq := (hLHS.congr_of_eventuallyEq hfun).unique hRHS
  simp only [div_self hπ_ne, Real.one_rpow, one_mul, mul_one] at heq
  rw [show ∑' k : ℤ, -(k : ℝ) ^ 2 * Real.exp (-Real.pi * (k : ℝ) ^ 2) = Z'π from rfl] at heq
  field_simp at heq
  suffices hN : ∑' k : ℤ, (1 - 4 * Real.pi * (k : ℝ) ^ 2) *
      Real.exp (-Real.pi * (k : ℝ) ^ 2) = quadraticPartFn Real.pi + 4 * Real.pi * Z'π by
    linarith
  have h1 := Meno.QuadraticAction.summable_scalarPartFn Real.pi hπ_pos
  have h2 : Summable (fun k : ℤ =>
      4 * Real.pi * (-(k : ℝ) ^ 2 * Real.exp (-Real.pi * (k : ℝ) ^ 2))) :=
    ((summable_sq_mul_exp Real.pi hπ_pos).neg.mul_left (4 * Real.pi)).congr fun k => by ring
  trans (∑' k : ℤ, Real.exp (-Real.pi * (k : ℝ) ^ 2) +
      ∑' k : ℤ, 4 * Real.pi * (-(k : ℝ) ^ 2 * Real.exp (-Real.pi * (k : ℝ) ^ 2)))
  · rw [← h1.tsum_add h2]; congr 1; ext k; ring
  · unfold quadraticPartFn; congr 1
    rw [show Z'π = ∑' k : ℤ, -(k : ℝ) ^ 2 * Real.exp (-Real.pi * (k : ℝ) ^ 2) from rfl]
    rw [← tsum_mul_left]

/-- Second-moment identity at the self-dual coupling α = π:
    `Z(π) = 4π · ∑ n² · exp(-π · n²)`.  Equivalently,
    `(∑ n² e^{-π n²}) / Z(π) = 1/(4π)`.  Follows by differentiating the
    T-duality identity `Z(π²/α) = √(α/π)·Z(α)` at the fixed point α = π. -/
theorem quadraticPartFn_moment_self_dual :
    quadraticPartFn Real.pi =
      4 * Real.pi *
        (∑' k : ℤ, (k : ℝ) ^ 2 * Real.exp (-Real.pi * (k : ℝ) ^ 2)) := by
  have hπ := Real.pi_pos
  have h1 : Summable (fun k : ℤ => Real.exp (-Real.pi * (k : ℝ) ^ 2)) :=
    Meno.QuadraticAction.summable_scalarPartFn Real.pi hπ
  have h2 : Summable (fun k : ℤ =>
      4 * Real.pi * ((k : ℝ) ^ 2 * Real.exp (-Real.pi * (k : ℝ) ^ 2))) :=
    (summable_sq_mul_exp Real.pi hπ).mul_left (4 * Real.pi)
  have split :
      (∑' k : ℤ, (1 - 4 * Real.pi * (k : ℝ) ^ 2) *
        Real.exp (-Real.pi * (k : ℝ) ^ 2)) =
      quadraticPartFn Real.pi -
        4 * Real.pi *
          (∑' k : ℤ, (k : ℝ) ^ 2 * Real.exp (-Real.pi * (k : ℝ) ^ 2)) := by
    unfold quadraticPartFn
    rw [show (fun k : ℤ => (1 - 4 * Real.pi * (k : ℝ) ^ 2) *
             Real.exp (-Real.pi * (k : ℝ) ^ 2)) =
        (fun k : ℤ => Real.exp (-Real.pi * (k : ℝ) ^ 2) -
          4 * Real.pi *
            ((k : ℝ) ^ 2 * Real.exp (-Real.pi * (k : ℝ) ^ 2))) from
      funext fun k => by ring]
    rw [h1.tsum_sub h2, tsum_mul_left]
  linarith [split, N_self_dual]

/-! ## Gibbs second moment at the self-dual coupling

The Gibbs expectation `⟨k²⟩_α := (∑ k²·e^{-αk²})/Z(α)` of winding-squared at
coupling α.  At the self-dual coupling α = π this equals exactly `1/(4π)` —
the T-duality relation pins the second moment at its fixed point. -/

/-- Gibbs expectation of `k²` in the quadratic partition function at coupling α:
    `⟨k²⟩_α := (∑ k² · e^{-α k²}) / Z(α)`. -/
noncomputable def quadraticMeanEnergy (α : ℝ) : ℝ :=
  (∑' k : ℤ, (k : ℝ) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2)) / quadraticPartFn α

/-- At the self-dual coupling α = π, the mean of `k²` is `1/(4π)`.

    Direct corollary of `quadraticPartFn_moment_self_dual`:
    `Z(π) = 4π · M` gives `M / Z(π) = 1/(4π)`. -/
theorem quadraticMeanEnergy_self_dual :
    quadraticMeanEnergy Real.pi = 1 / (4 * Real.pi) := by
  unfold quadraticMeanEnergy
  have hπ := Real.pi_pos
  have hZπ_ne : quadraticPartFn Real.pi ≠ 0 :=
    ne_of_gt (lt_trans one_pos (quadraticPartFn_gt_one Real.pi hπ))
  have h4π_ne : (4 * Real.pi) ≠ 0 := by positivity
  rw [div_eq_div_iff hZπ_ne h4π_ne]
  linarith [quadraticPartFn_moment_self_dual]

/-- **Bridge to the Gibbs density.** `quadraticMeanEnergy α` is the Gibbs
    expectation of the squared canonical winding on the canonical quadratic
    `GroupoidObj` at coupling `α`.  So the analytic mean energy *is* the second
    moment of a probability density on `End (quadraticObj α hα).base`. -/
theorem quadraticMeanEnergy_eq_gibbsExpect (α : ℝ) (hα : 0 < α) :
    (quadraticObj α hα).gibbsExpect (fun g => (quadraticWind g : ℝ) ^ 2) =
      quadraticMeanEnergy α := by
  unfold GroupoidObj.gibbsExpect GroupoidObj.gibbsMass quadraticMeanEnergy
  rw [quadraticObj_partFn α hα]
  have h_term : ∀ g : End (quadraticObj α hα).base,
      (quadraticWind g : ℝ) ^ 2 *
        (Real.exp (-(quadraticObj α hα).energy g) / quadraticPartFn α) =
      ((quadraticWind g : ℝ) ^ 2 * Real.exp (-α * (quadraticWind g : ℝ) ^ 2)) /
        quadraticPartFn α := by
    intro g
    show (quadraticWind g : ℝ) ^ 2 *
      (Real.exp (-(α * (quadraticWind g : ℝ) ^ 2)) / quadraticPartFn α) = _
    rw [mul_div_assoc, neg_mul]
  rw [tsum_congr h_term, tsum_div_const]
  congr 1

private lemma hasDerivAt_log_quadraticPartFn (β : ℝ) (hβ : 0 < β) :
    HasDerivAt (fun α => Real.log (quadraticPartFn α))
      (- quadraticMeanEnergy β) β := by
  have hZ := hasDerivAt_quadraticPartFn β hβ
  have hZpos : 0 < quadraticPartFn β :=
    lt_trans one_pos (quadraticPartFn_gt_one β hβ)
  have h := hZ.log (ne_of_gt hZpos)
  convert h using 1
  unfold quadraticMeanEnergy
  rw [show (∑' k : ℤ, -(k : ℝ) ^ 2 * Real.exp (-β * (k : ℝ) ^ 2)) =
    -(∑' k : ℤ, (k : ℝ) ^ 2 * Real.exp (-β * (k : ℝ) ^ 2)) from by
    rw [← tsum_neg]; congr 1; ext k; ring]
  rw [neg_div]

/-- **The Cauchy–Schwarz corroboration** (review #16): `M₂² < Z·M₄`
    for all `α > 0` — an independent, self-contained route to the
    strict positivity of the squared-winding variance, retained as
    named corroboration of the generic strict-fluctuation engine
    (`Meno/Fluctuation.lean`).

    Consider the "affine variance" summand `(Z·k² - M₂)²·exp(-αk²)`.
    Its tsum equals `Z²·M₄ - Z·M₂² = Z·(Z·M₄ - M₂²)`.
    Each term is non-negative, and the `k=0` term is `M₂² > 0`, so the
    tsum is strictly positive, forcing `Z·M₄ > M₂²`. This is the Gibbs
    Cauchy–Schwarz for the observable `k²`: the squared mean is strictly
    less than the mean of the square, because `k²` is not constant. -/
theorem M2_sq_lt_Z_mul_M4 (α : ℝ) (hα : 0 < α) :
    (∑' k : ℤ, (k : ℝ) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2)) ^ 2 <
      quadraticPartFn α *
        ∑' k : ℤ, (k : ℝ) ^ 4 * Real.exp (-α * (k : ℝ) ^ 2) := by
  set M2 := ∑' k : ℤ, (k : ℝ) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2) with hM2_def
  set M4 := ∑' k : ℤ, (k : ℝ) ^ 4 * Real.exp (-α * (k : ℝ) ^ 2) with hM4_def
  set Z := quadraticPartFn α with hZ_def
  have hZ_pos : 0 < Z := lt_trans one_pos (quadraticPartFn_gt_one α hα)
  have hM2_pos : 0 < M2 := by
    refine Summable.tsum_pos (summable_sq_mul_exp α hα) ?_ 1 ?_
    · intro k; exact mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _))
    · show (0 : ℝ) < ((1 : ℤ) : ℝ) ^ 2 * Real.exp (-α * ((1 : ℤ) : ℝ) ^ 2)
      rw [Int.cast_one, one_pow, one_mul]
      exact Real.exp_pos _
  have h_expand : ∀ k : ℤ, (Z * (k : ℝ) ^ 2 - M2) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2) =
      Z ^ 2 * ((k : ℝ) ^ 4 * Real.exp (-α * (k : ℝ) ^ 2)) +
        (-(2 * Z * M2)) * ((k : ℝ) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2)) +
        M2 ^ 2 * Real.exp (-α * (k : ℝ) ^ 2) := by
    intro k; ring
  have s1 : Summable (fun k : ℤ => Z ^ 2 * ((k : ℝ) ^ 4 * Real.exp (-α * (k : ℝ) ^ 2))) :=
    (summable_pow4_mul_exp α hα).mul_left _
  have s2 : Summable (fun k : ℤ =>
      (-(2 * Z * M2)) * ((k : ℝ) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2))) :=
    (summable_sq_mul_exp α hα).mul_left _
  have s3 : Summable (fun k : ℤ => M2 ^ 2 * Real.exp (-α * (k : ℝ) ^ 2)) :=
    (Meno.QuadraticAction.summable_scalarPartFn α hα).mul_left _
  have h_summable : Summable (fun k : ℤ =>
      (Z * (k : ℝ) ^ 2 - M2) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2)) :=
    ((s1.add s2).add s3).congr (fun k => (h_expand k).symm)
  have h_tsum_eq : ∑' k : ℤ, (Z * (k : ℝ) ^ 2 - M2) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2) =
      Z ^ 2 * M4 - Z * M2 ^ 2 := by
    rw [tsum_congr h_expand,
        (s1.add s2).tsum_add s3, s1.tsum_add s2,
        tsum_mul_left, tsum_mul_left, tsum_mul_left]
    show Z ^ 2 * M4 + -(2 * Z * M2) * M2 + M2 ^ 2 * Z = Z ^ 2 * M4 - Z * M2 ^ 2
    ring
  have h_tsum_pos : 0 < ∑' k : ℤ, (Z * (k : ℝ) ^ 2 - M2) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2) := by
    refine Summable.tsum_pos h_summable ?_ 0 ?_
    · intro k; exact mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _))
    · show (0 : ℝ) < (Z * ((0 : ℤ) : ℝ) ^ 2 - M2) ^ 2 * Real.exp (-α * ((0 : ℤ) : ℝ) ^ 2)
      rw [Int.cast_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_sub,
          neg_sq, mul_zero, Real.exp_zero, mul_one]
      exact pow_pos hM2_pos 2
  rw [h_tsum_eq] at h_tsum_pos
  have hfact : Z ^ 2 * M4 - Z * M2 ^ 2 = Z * (Z * M4 - M2 ^ 2) := by ring
  rw [hfact] at h_tsum_pos
  have hposZM : 0 < Z * M4 - M2 ^ 2 := (mul_pos_iff_of_pos_left hZ_pos).mp h_tsum_pos
  linarith

private lemma unit_energy_one_ne :
    unitQuadAction.energy (fun _ => (1 : ℤ)) ≠ 0 := by
  rw [unitQuadAction_energy]
  norm_num

private lemma meanEnergy_unit :
    unitQuadAction.meanEnergy = quadraticMeanEnergy := by
  funext β
  show unitQuadAction.scaledMoment β / unitQuadAction.scaledPartFn β = _
  rw [scaledMoment_unit β, scaledPartFn_unit β]
  rfl

/-- `quadraticMeanEnergy` is strictly decreasing on `(0, ∞)` — the
    generic strict-dissipation theorem (`Meno/Fluctuation.lean`) at
    the rank-one unit action (review #16). The Cauchy–Schwarz route
    stands as named corroboration (`M2_sq_lt_Z_mul_M4`). -/
theorem quadraticMeanEnergy_strictAntiOn :
    StrictAntiOn quadraticMeanEnergy (Set.Ioi 0) := by
  rw [← meanEnergy_unit]
  exact unitQuadAction.meanEnergy_strictAntiOn ⟨fun _ => 1, unit_energy_one_ne⟩

/-- `quadraticMeanEnergy` is injective on `(0, ∞)`: distinct couplings give
    distinct mean values.  Immediate from strict anti-monotonicity. -/
theorem quadraticMeanEnergy_injOn :
    Set.InjOn quadraticMeanEnergy (Set.Ioi 0) :=
  quadraticMeanEnergy_strictAntiOn.injOn

private lemma quadraticObj_gibbsVariance_expr (α : ℝ) (hα : 0 < α) :
    (quadraticObj α hα).gibbsVariance
        (fun g => (quadraticWind g : ℝ) ^ 2) =
      (∑' k : ℤ, (k : ℝ) ^ 4 * Real.exp (-α * (k : ℝ) ^ 2)) / quadraticPartFn α -
        (quadraticMeanEnergy α) ^ 2 := by
  unfold GroupoidObj.gibbsVariance
  rw [quadraticMeanEnergy_eq_gibbsExpect α hα]
  have h_pow4 : (quadraticObj α hα).gibbsExpect
        (fun g => ((quadraticWind g : ℝ) ^ 2) ^ 2) =
      (∑' k : ℤ, (k : ℝ) ^ 4 * Real.exp (-α * (k : ℝ) ^ 2)) / quadraticPartFn α := by
    unfold GroupoidObj.gibbsExpect GroupoidObj.gibbsMass
    rw [quadraticObj_partFn α hα]
    have h_term : ∀ g : End (quadraticObj α hα).base,
        ((quadraticWind g : ℝ) ^ 2) ^ 2 *
          (Real.exp (-(quadraticObj α hα).energy g) / quadraticPartFn α) =
        ((quadraticWind g : ℝ) ^ 4 * Real.exp (-α * (quadraticWind g : ℝ) ^ 2)) /
          quadraticPartFn α := by
      intro g
      show ((quadraticWind g : ℝ) ^ 2) ^ 2 *
        (Real.exp (-(α * (quadraticWind g : ℝ) ^ 2)) / quadraticPartFn α) = _
      rw [mul_div_assoc, neg_mul]
      congr 1
      ring
    rw [tsum_congr h_term, tsum_div_const]
    congr 1
  rw [h_pow4]

private lemma quadraticObj_gibbsVariance_eq_unit (α : ℝ) (hα : 0 < α) :
    (quadraticObj α hα).gibbsVariance (fun g => (quadraticWind g : ℝ) ^ 2)
      = (unitQuadAction.scaledSector α hα).gibbsVariance
          unitQuadAction.energy := by
  rw [quadraticObj_gibbsVariance_expr α hα,
    unitQuadAction.scaledSector_gibbsVariance_energy α hα,
    scaledMoment2_unit α, scaledPartFn_unit α,
    show unitQuadAction.meanEnergy α = quadraticMeanEnergy α from
      congrFun meanEnergy_unit α]

/-- **Fluctuation-dissipation identity** at the `GroupoidObj` level:
    `d⟨k²⟩/dα = -gibbsVariance((wind)²)` on the canonical quadratic family.

    The derivative of the Gibbs mean of squared winding under coupling `α` is
    the negative Gibbs variance of squared winding, a probabilistic identity
    about the Gibbs density on `End (quadraticObj α).base`.  Strict positivity
    of the variance (Cauchy–Schwarz: `(wind)²` is not constant) is the reason
    `quadraticMeanEnergy` is strictly decreasing. -/
theorem hasDerivAt_quadraticMeanEnergy_eq_neg_gibbsVariance
    (α : ℝ) (hα : 0 < α) :
    HasDerivAt quadraticMeanEnergy
      (-((quadraticObj α hα).gibbsVariance
            (fun g => (quadraticWind g : ℝ) ^ 2))) α := by
  rw [← meanEnergy_unit, quadraticObj_gibbsVariance_eq_unit α hα]
  exact unitQuadAction.hasDerivAt_meanEnergy_eq_neg_gibbsVariance α hα

/-- The Gibbs variance of squared winding is strictly positive on
    `(0, ∞)` — the generic strict-fluctuation theorem at the unit
    action (review #16); Cauchy–Schwarz (`M2_sq_lt_Z_mul_M4`) stands
    as named corroboration. -/
theorem quadraticObj_gibbsVariance_pos (α : ℝ) (hα : 0 < α) :
    0 < (quadraticObj α hα).gibbsVariance (fun g => (quadraticWind g : ℝ) ^ 2) := by
  rw [quadraticObj_gibbsVariance_eq_unit α hα]
  exact unitQuadAction.scaledSector_gibbsVariance_energy_pos α hα
    (k₀ := fun _ => 1) unit_energy_one_ne

/-- `log Z(α)` is strictly convex on `(0, ∞)`.

    Dual to strict anti-monotonicity of `⟨k²⟩_α = -d(log Z)/dα`: the derivative
    of `log Z` is `-⟨k²⟩` (pointwise), and strict anti-monotonicity of `⟨k²⟩`
    becomes strict monotonicity of the derivative, which is strict convexity. -/
theorem log_quadraticPartFn_strictConvexOn :
    StrictConvexOn ℝ (Set.Ioi 0) (fun α => Real.log (quadraticPartFn α)) := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ioi 0)
  · intro α hα
    exact (hasDerivAt_log_quadraticPartFn α hα).continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    intro α hα β hβ hlt
    have hdα := hasDerivAt_log_quadraticPartFn α hα
    have hdβ := hasDerivAt_log_quadraticPartFn β hβ
    rw [hdα.deriv, hdβ.deriv]
    exact neg_lt_neg (quadraticMeanEnergy_strictAntiOn hα hβ hlt)

/-- T-duality functional equation for mean energy:
    `(π²/α²)·⟨k²⟩_{π²/α} + ⟨k²⟩_α = 1/(2α)`.

    Obtained by differentiating `log Z(π²/α) = (1/2)·log(α/π) + log Z(α)` in α.
    At α = π the two mean-energy terms coalesce into `2·⟨k²⟩_π = 1/(2π)`,
    recovering `quadraticMeanEnergy_self_dual`. The full FE says T-duality
    constrains the second moment as a function of α, not just at the fixed
    point: `⟨k²⟩_{π²/α}` is a rational function of α and `⟨k²⟩_α`. -/
theorem quadraticMeanEnergy_T_dual (α : ℝ) (hα : 0 < α) :
    (Real.pi ^ 2 / α ^ 2) * quadraticMeanEnergy (Real.pi ^ 2 / α) +
      quadraticMeanEnergy α = 1 / (2 * α) := by
  have hπ := Real.pi_pos
  have hπα : 0 < Real.pi ^ 2 / α := div_pos (sq_pos_of_pos hπ) hα
  have hαπ : 0 < α / Real.pi := div_pos hα hπ
  have h_log_eventually :
      (fun β : ℝ => Real.log (quadraticPartFn (Real.pi ^ 2 / β))) =ᶠ[nhds α]
        (fun β => (1/2 : ℝ) * Real.log (β / Real.pi) +
          Real.log (quadraticPartFn β)) := by
    filter_upwards [eventually_gt_nhds hα] with β hβ
    have hβπ : 0 < β / Real.pi := div_pos hβ hπ
    have hZβ : 0 < quadraticPartFn β :=
      lt_trans one_pos (quadraticPartFn_gt_one β hβ)
    have hrpow : 0 < (β / Real.pi) ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hβπ _
    rw [quadraticPartFn_duality_real β hβ,
        Real.log_mul (ne_of_gt hrpow) (ne_of_gt hZβ),
        Real.log_rpow hβπ]
  have hLogZ_πα := hasDerivAt_log_quadraticPartFn (Real.pi ^ 2 / α) hπα
  have h_inv : HasDerivAt (fun β : ℝ => Real.pi ^ 2 / β)
      (-(Real.pi ^ 2) / α ^ 2) α := by
    have h := (hasDerivAt_const α (Real.pi ^ 2)).div
              (hasDerivAt_id α) (ne_of_gt hα)
    simp only [id] at h
    convert h using 1
    ring
  have hLHS : HasDerivAt (fun β => Real.log (quadraticPartFn (Real.pi ^ 2 / β)))
      ((- quadraticMeanEnergy (Real.pi ^ 2 / α)) * (-(Real.pi ^ 2) / α ^ 2)) α :=
    hLogZ_πα.comp α h_inv
  have h_div : HasDerivAt (fun β : ℝ => β / Real.pi) (1 / Real.pi) α := by
    simpa using (hasDerivAt_id α).div_const Real.pi
  have h_log_div : HasDerivAt (fun β => Real.log (β / Real.pi)) (1 / α) α := by
    have := h_div.log (ne_of_gt hαπ)
    convert this using 1
    field_simp
  have h_halflog : HasDerivAt (fun β : ℝ => (1/2 : ℝ) * Real.log (β / Real.pi))
      (1 / (2 * α)) α := by
    have := h_log_div.const_mul ((1:ℝ)/2)
    convert this using 1
    ring
  have hLogZ_α := hasDerivAt_log_quadraticPartFn α hα
  have hRHS : HasDerivAt (fun β : ℝ => (1/2 : ℝ) * Real.log (β / Real.pi) +
      Real.log (quadraticPartFn β))
      (1 / (2 * α) + (- quadraticMeanEnergy α)) α :=
    h_halflog.add hLogZ_α
  have heq := (hLHS.congr_of_eventuallyEq h_log_eventually.symm).unique hRHS
  have hsimp : (- quadraticMeanEnergy (Real.pi ^ 2 / α)) *
      (-(Real.pi ^ 2) / α ^ 2) =
      (Real.pi ^ 2 / α ^ 2) * quadraticMeanEnergy (Real.pi ^ 2 / α) := by ring
  rw [hsimp] at heq
  linarith

/-- **Structural bridge.** On any `GroupoidObj` carrying quadratic energy
    `α·(wind g)²` for a ℤ-valued winding equivalence, the Gibbs expectation of
    `(wind g)²` equals the canonical `quadraticMeanEnergy α`. -/
theorem GroupoidObj.gibbsExpect_wind_sq_eq
    (E : GroupoidObj) (wind : End E.base ≃ ℤ) (α : ℝ) (_hα : 0 < α)
    (hK : ∀ g, E.energy g = α * (wind g : ℝ) ^ 2) :
    E.gibbsExpect (fun g => (wind g : ℝ) ^ 2) = quadraticMeanEnergy α := by
  unfold GroupoidObj.gibbsExpect GroupoidObj.gibbsMass quadraticMeanEnergy
  rw [partFn_eq_quadraticPartFn E wind α hK]
  have h_term : ∀ g : End E.base,
      (wind g : ℝ) ^ 2 * (Real.exp (-E.energy g) / quadraticPartFn α) =
      ((wind g : ℝ) ^ 2 * Real.exp (-α * (wind g : ℝ) ^ 2)) / quadraticPartFn α := by
    intro g
    rw [hK g, mul_div_assoc, neg_mul]
  rw [tsum_congr h_term, tsum_div_const]
  congr 1
  exact Equiv.tsum_eq wind
    (fun k : ℤ => (k : ℝ) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2))

/-- **Structural T-duality functional equation** for the Gibbs mean energy
    of squared winding on any `GroupoidObj` with quadratic energy `α·(wind g)²`.
    This lifts `quadraticMeanEnergy_T_dual` to arbitrary quadratic groupoid
    objects via their canonical ℤ-valued winding. -/
theorem GroupoidObj.meanEnergy_T_dual
    (E : GroupoidObj) (wind : End E.base ≃ ℤ) (α : ℝ) (hα : 0 < α)
    (hK : ∀ g, E.energy g = α * (wind g : ℝ) ^ 2) :
    (Real.pi ^ 2 / α ^ 2) *
        (E.dual wind α hα hK).gibbsExpect (fun g => (wind g : ℝ) ^ 2) +
      E.gibbsExpect (fun g => (wind g : ℝ) ^ 2) = 1 / (2 * α) := by
  have hπα : 0 < Real.pi ^ 2 / α := div_pos (sq_pos_of_pos Real.pi_pos) hα
  have hK' : ∀ g, (E.dual wind α hα hK).energy g =
      (Real.pi ^ 2 / α) * (wind g : ℝ) ^ 2 := fun _ => rfl
  have hE := E.gibbsExpect_wind_sq_eq wind α hα hK
  have hEdual := (E.dual wind α hα hK).gibbsExpect_wind_sq_eq wind
    (Real.pi ^ 2 / α) hπα hK'
  have hFE := quadraticMeanEnergy_T_dual α hα
  linear_combination hE + (Real.pi^2/α^2) * hEdual + hFE

/-- For A ≥ 4 and t ≥ 0: (A + 4t)·e⁻ᵗ ≤ A. Uses only e^t ≥ 1 + t and A ≥ 4. -/
private lemma aux_exp_ineq (A t : ℝ) (hA : 4 ≤ A) (ht : 0 ≤ t) :
    (A + 4 * t) * Real.exp (-t) ≤ A := by
  rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos t)]
  calc A + 4 * t ≤ A + A * t := by nlinarith
    _ = A * (1 + t) := by ring
    _ ≤ A * Real.exp t :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp t]) (by linarith)

/-- Each summand of N is nondecreasing in β for β ≥ π (4π > 5 argument). -/
private lemma N_summand_mono (k : ℤ) (β : ℝ) (hβ : Real.pi ≤ β) :
    (1 - 4 * Real.pi * (k : ℝ) ^ 2) * Real.exp (-Real.pi * (k : ℝ) ^ 2) ≤
    (1 - 4 * β * (k : ℝ) ^ 2) * Real.exp (-β * (k : ℝ) ^ 2) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
      rcases le_or_gt k (-1) with h | h
      · have : (k : ℝ) ≤ -1 := by exact_mod_cast h
        nlinarith [sq_nonneg ((k : ℝ) + 1)]
      · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
        nlinarith [sq_nonneg ((k : ℝ) - 1)]
    have hA : 4 ≤ 4 * Real.pi * (k : ℝ) ^ 2 - 1 := by nlinarith [Real.pi_gt_three]
    have ht : 0 ≤ (β - Real.pi) * (k : ℝ) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    have haux := aux_exp_ineq (4 * Real.pi * (k : ℝ) ^ 2 - 1)
      ((β - Real.pi) * (k : ℝ) ^ 2) hA ht
    -- Factor exp(-βk²) = exp(-πk²) · exp(-(β-π)k²)
    have hfac : Real.exp (-β * (k : ℝ) ^ 2) =
        Real.exp (-Real.pi * (k : ℝ) ^ 2) * Real.exp (-(β - Real.pi) * (k : ℝ) ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hfac]
    -- Reduce to: (1-4πk²) ≤ (1-4βk²)·exp(-(β-π)k²), then multiply by exp(-πk²) > 0
    suffices hsuff : 1 - 4 * Real.pi * (k : ℝ) ^ 2 ≤
        (1 - 4 * β * (k : ℝ) ^ 2) * Real.exp (-(β - Real.pi) * (k : ℝ) ^ 2) by
      calc (1 - 4 * Real.pi * (k : ℝ) ^ 2) * Real.exp (-Real.pi * (k : ℝ) ^ 2)
          ≤ ((1 - 4 * β * (k : ℝ) ^ 2) * Real.exp (-(β - Real.pi) * (k : ℝ) ^ 2)) *
            Real.exp (-Real.pi * (k : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right hsuff (le_of_lt (Real.exp_pos _))
        _ = (1 - 4 * β * (k : ℝ) ^ 2) *
            (Real.exp (-Real.pi * (k : ℝ) ^ 2) *
             Real.exp (-(β - Real.pi) * (k : ℝ) ^ 2)) := by ring
    -- -(4πk²-1) ≤ -(4πk²-1+4(β-π)k²)·exp, follows from haux by negation
    have hrw1 : 1 - 4 * β * (k : ℝ) ^ 2 =
        -(4 * Real.pi * (k : ℝ) ^ 2 - 1 + 4 * ((β - Real.pi) * (k : ℝ) ^ 2)) := by ring
    have hrw2 : -(β - Real.pi) * (k : ℝ) ^ 2 = -((β - Real.pi) * (k : ℝ) ^ 2) := by ring
    rw [hrw1, hrw2, neg_mul]
    linarith

/-- N(β) ≥ 0 for β ≥ π: term-by-term from N(π) = 0. -/
private lemma N_nonneg (β : ℝ) (hβ : Real.pi ≤ β) :
    0 ≤ ∑' k : ℤ, (1 - 4 * β * (k : ℝ) ^ 2) *
      Real.exp (-β * (k : ℝ) ^ 2) := by
  rw [show (0 : ℝ) = ∑' k : ℤ, (1 - 4 * Real.pi * (k : ℝ) ^ 2) *
    Real.exp (-Real.pi * (k : ℝ) ^ 2) from N_self_dual.symm]
  exact (summable_N_summand Real.pi Real.pi_pos).tsum_le_tsum
    (fun k => N_summand_mono k β hβ)
    (summable_N_summand β (lt_of_lt_of_le Real.pi_pos hβ))

/-- Strict version of `aux_exp_ineq`: when `t > 0`, the inequality is strict. -/
private lemma aux_exp_ineq_strict (A t : ℝ) (hA : 4 ≤ A) (ht : 0 < t) :
    (A + 4 * t) * Real.exp (-t) < A := by
  rw [Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos t)]
  calc A + 4 * t ≤ A + A * t := by nlinarith
    _ = A * (1 + t) := by ring
    _ < A * Real.exp t := by
        apply mul_lt_mul_of_pos_left _ (by linarith)
        have := Real.add_one_lt_exp (ne_of_gt ht)
        linarith

/-- Strict monotone increase of the `N` summand in β at a fixed nonzero k when β > π.
    Proof: reduce to `aux_exp_ineq_strict` via `A = 4πx - 1 ≥ 4`, `u = (β-π)x > 0`,
    where the shift A + 4u = 4βx - 1. -/
private lemma N_summand_strict_mono (k : ℤ) (hk : k ≠ 0) (β : ℝ) (hβ : Real.pi < β) :
    (1 - 4 * Real.pi * (k : ℝ) ^ 2) * Real.exp (-Real.pi * (k : ℝ) ^ 2) <
    (1 - 4 * β * (k : ℝ) ^ 2) * Real.exp (-β * (k : ℝ) ^ 2) := by
  have hx_ge_one : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
    have hk_abs_r : (1 : ℝ) ≤ |(k : ℝ)| := by
      have hint : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
      have : ((1 : ℤ) : ℝ) ≤ ((|k| : ℤ) : ℝ) := Int.cast_le.mpr hint
      simpa [Int.cast_abs] using this
    nlinarith [sq_abs (k : ℝ), abs_nonneg ((k : ℝ))]
  set x : ℝ := (k : ℝ) ^ 2 with hx_def
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx_ge_one
  have hu_pos : 0 < (β - Real.pi) * x := mul_pos (by linarith) hx_pos
  have hA_ge : (4 : ℝ) ≤ 4 * Real.pi * x - 1 := by
    have h4π : (5 : ℝ) ≤ 4 * Real.pi := by
      have : (3 : ℝ) < Real.pi := Real.pi_gt_three
      linarith
    have h5 : (5 : ℝ) ≤ 4 * Real.pi * x := by
      calc (5 : ℝ)
          ≤ 4 * Real.pi * 1 := by linarith
        _ ≤ 4 * Real.pi * x := by
            apply mul_le_mul_of_nonneg_left hx_ge_one
            positivity
    linarith
  have h_aux := aux_exp_ineq_strict
    (4 * Real.pi * x - 1) ((β - Real.pi) * x) hA_ge hu_pos
  have h_shift : 4 * Real.pi * x - 1 + 4 * ((β - Real.pi) * x) = 4 * β * x - 1 := by ring
  rw [h_shift] at h_aux
  -- h_aux : (4 * β * x - 1) * Real.exp (-((β - Real.pi) * x)) < 4 * Real.pi * x - 1
  have h_exp_split : Real.exp (-β * x) =
      Real.exp (-Real.pi * x) * Real.exp (-((β - Real.pi) * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h_exp_split]
  have hE_pos : 0 < Real.exp (-Real.pi * x) := Real.exp_pos _
  have h_neg : (1 - 4 * β * x) * Real.exp (-((β - Real.pi) * x)) =
      -((4 * β * x - 1) * Real.exp (-((β - Real.pi) * x))) := by ring
  have target : (1 - 4 * Real.pi * x) <
      (1 - 4 * β * x) * Real.exp (-((β - Real.pi) * x)) := by
    rw [h_neg]; linarith
  calc (1 - 4 * Real.pi * x) * Real.exp (-Real.pi * x)
      < (1 - 4 * β * x) * Real.exp (-((β - Real.pi) * x)) * Real.exp (-Real.pi * x) :=
        mul_lt_mul_of_pos_right target hE_pos
    _ = (1 - 4 * β * x) *
        (Real.exp (-Real.pi * x) * Real.exp (-((β - Real.pi) * x))) := by ring

/-- Strict positivity of `N(β)` for β > π. -/
private lemma N_pos (β : ℝ) (hβ : Real.pi < β) :
    0 < ∑' k : ℤ, (1 - 4 * β * (k : ℝ) ^ 2) *
      Real.exp (-β * (k : ℝ) ^ 2) := by
  rw [show (0 : ℝ) = ∑' k : ℤ, (1 - 4 * Real.pi * (k : ℝ) ^ 2) *
    Real.exp (-Real.pi * (k : ℝ) ^ 2) from N_self_dual.symm]
  exact Summable.tsum_lt_tsum (i := (1 : ℤ))
    (fun k => N_summand_mono k β (le_of_lt hβ))
    (N_summand_strict_mono 1 (by decide) β hβ)
    (summable_N_summand Real.pi Real.pi_pos)
    (summable_N_summand β (lt_trans Real.pi_pos hβ))

/-- β ↦ (β/π)^{1/2}·Z(β)² is monotone on [π,∞).
Reduces to N(β) ≥ 0 via `monotoneOn_of_deriv_nonneg` + `hasDerivAt_tsum`. -/
private lemma quadraticPartFn_rpow_sq_monotone :
    MonotoneOn (fun β => (β / Real.pi) ^ ((1:ℝ)/2) * quadraticPartFn β ^ 2)
    (Set.Ici Real.pi) := by
  have hf_at : ∀ β : ℝ, 0 < β →
      HasDerivAt (fun α => (α / Real.pi) ^ ((1:ℝ)/2) * quadraticPartFn α ^ 2)
        (1 / Real.pi * ((1:ℝ)/2) * (β / Real.pi) ^ ((1:ℝ)/2 - 1) *
         quadraticPartFn β ^ 2 +
         (β / Real.pi) ^ ((1:ℝ)/2) *
         (↑2 * quadraticPartFn β ^ (2 - 1) *
          (∑' k : ℤ, -(k : ℝ) ^ 2 * Real.exp (-β * (k : ℝ) ^ 2))))
        β := fun β hβ =>
    (((hasDerivAt_id β).div_const Real.pi).rpow_const
      (Or.inl (ne_of_gt (div_pos hβ Real.pi_pos)))).mul
      ((hasDerivAt_quadraticPartFn β hβ).pow 2)
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · exact fun β hβ => (hf_at β (lt_of_lt_of_le Real.pi_pos hβ)).differentiableAt.continuousAt.continuousWithinAt
  · rw [interior_Ici]; exact fun β hβ => (hf_at β (lt_trans Real.pi_pos hβ)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]; intro β hβ
    have hβ_pos : 0 < β := lt_trans Real.pi_pos hβ
    have hβπ : 0 < β / Real.pi := div_pos hβ_pos Real.pi_pos
    rw [(hf_at β hβ_pos).deriv]
    simp only [show (2:ℕ) - 1 = 1 from rfl, pow_one]
    set c := (β / Real.pi) ^ ((1:ℝ)/2) with hc_def
    set ci := (β / Real.pi) ^ ((1:ℝ)/2 - 1) with hci_def
    set Zβ := quadraticPartFn β
    set Z'β := ∑' k : ℤ, -(k : ℝ) ^ 2 * Real.exp (-β * (k : ℝ) ^ 2)
    have hc_pos : 0 < c := Real.rpow_pos_of_pos hβπ _
    have hc_ci : c * ci = 1 := by
      simp only [hc_def, hci_def]
      rw [← Real.rpow_add hβπ, show (1:ℝ)/2 + ((1:ℝ)/2 - 1) = 0 from by ring,
         Real.rpow_zero]
    have hc_sq : c * c = β / Real.pi := by
      simp only [hc_def]
      rw [← Real.rpow_add hβπ, show (1:ℝ)/2 + (1:ℝ)/2 = 1 from by norm_num,
         Real.rpow_one]
    have hZ_pos : 0 < Zβ := lt_trans one_pos (quadraticPartFn_gt_one β hβ_pos)
    have hπ_ne := ne_of_gt Real.pi_pos
    have hNβ : 0 ≤ Zβ + 4 * β * Z'β := by
      have hN := N_nonneg β (le_of_lt hβ)
      rw [show Zβ + 4 * β * Z'β =
          ∑' k : ℤ, (1 - 4 * β * (k : ℝ) ^ 2) * Real.exp (-β * (k : ℝ) ^ 2) from by
        show quadraticPartFn β + 4 * β *
            (∑' k : ℤ, -(k : ℝ) ^ 2 * Real.exp (-β * (k : ℝ) ^ 2)) =
            ∑' k : ℤ, (1 - 4 * β * (k : ℝ) ^ 2) * Real.exp (-β * (k : ℝ) ^ 2)
        unfold quadraticPartFn; rw [← tsum_mul_left]
        rw [← (Meno.QuadraticAction.summable_scalarPartFn β hβ_pos).tsum_add
            (((summable_sq_mul_exp β hβ_pos).neg.mul_left (4 * β)).congr fun k => by ring)]
        congr 1; ext k; ring]
      exact hN
    suffices h : 0 ≤ 2 * Real.pi * c *
        (1 / Real.pi * (1 / 2) * ci * Zβ ^ 2 + c * (2 * Zβ * Z'β)) by
      exact nonneg_of_mul_nonneg_right h
        (mul_pos (mul_pos two_pos Real.pi_pos) hc_pos)
    have hring : 2 * Real.pi * c *
        (1 / Real.pi * (1 / 2) * ci * Zβ ^ 2 + c * (2 * Zβ * Z'β)) =
        c * ci * Zβ ^ 2 + 4 * Real.pi * (c * c) * Zβ * Z'β := by
      field_simp; ring
    rw [hring, hc_ci, hc_sq]
    have hfinal : 1 * Zβ ^ 2 + 4 * Real.pi * (β / Real.pi) * Zβ * Z'β =
        Zβ * (Zβ + 4 * β * Z'β) := by field_simp
    rw [hfinal]
    exact mul_nonneg (le_of_lt hZ_pos) hNβ

set_option maxHeartbeats 800000 in
private lemma quadraticPartFn_self_dual_minimum (α : ℝ) (hα : 0 < α) :
    quadraticPartFn Real.pi ^ 2 ≤
    (α / Real.pi) ^ ((1 : ℝ) / 2) * quadraticPartFn α ^ 2 := by
  suffices h : ∀ β : ℝ, β ≥ Real.pi → quadraticPartFn Real.pi ^ 2 ≤
      (β / Real.pi) ^ ((1 : ℝ) / 2) * quadraticPartFn β ^ 2 by
    by_cases hle : α ≥ Real.pi
    · exact h α hle
    · push_neg at hle
      have hβ := h (Real.pi ^ 2 / α) (by rw [ge_iff_le, le_div_iff₀ hα]; nlinarith [Real.pi_pos])
      rw [quadraticPartFn_duality_real α hα] at hβ
      convert hβ using 1
      have hπ : Real.pi > 0 := Real.pi_pos
      have hαπ : 0 < α / Real.pi := div_pos hα hπ
      have hsimp : Real.pi ^ 2 / α / Real.pi = Real.pi / α := by field_simp
      rw [hsimp, mul_pow]
      have hsq : ((α / Real.pi) ^ ((1:ℝ)/2)) ^ 2 = α / Real.pi := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hαπ)]; norm_num
      rw [hsq]
      suffices hkey : (Real.pi / α) ^ ((1:ℝ)/2) * (α / Real.pi) = (α / Real.pi) ^ ((1:ℝ)/2) by
        nlinarith [sq_nonneg (quadraticPartFn α)]
      have step1 : (Real.pi / α) ^ ((1:ℝ)/2) = ((α / Real.pi) ^ ((1:ℝ)/2))⁻¹ := by
        rw [show (Real.pi / α : ℝ) = (α / Real.pi)⁻¹ from (inv_div α Real.pi).symm]
        exact Real.inv_rpow (le_of_lt hαπ) _
      set x := (α / Real.pi) ^ ((1:ℝ)/2) with hx_def
      have hx : 0 < x := Real.rpow_pos_of_pos hαπ _
      rw [step1, ← hsq, show x⁻¹ * x ^ 2 = x from by
        rw [sq, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hx), one_mul]]
  intro β hβ
  have hπ_mem : Real.pi ∈ Set.Ici Real.pi := Set.left_mem_Ici
  have hβ_mem : β ∈ Set.Ici Real.pi := hβ
  have hmono := quadraticPartFn_rpow_sq_monotone hπ_mem hβ_mem hβ
  simp only [div_self (ne_of_gt Real.pi_pos), Real.one_rpow, one_mul] at hmono
  exact hmono

theorem dual_pair_variational (α : ℝ) (hα : 0 < α) :
    quadraticPartFn Real.pi ^ 2 ≤
    quadraticPartFn α * quadraticPartFn (Real.pi ^ 2 / α) := by
  rw [dual_pair_product α hα]
  exact quadraticPartFn_self_dual_minimum α hα

theorem GroupoidObj.dual_pair_variational
    (E : GroupoidObj) (wind : End E.base ≃ ℤ) (α : ℝ) (hα : 0 < α)
    (hK : ∀ g, E.energy g = α * (wind g : ℝ) ^ 2) :
    quadraticPartFn Real.pi ^ 2 ≤ E.partFn * (E.dual wind α hα hK).partFn := by
  rw [partFn_eq_quadraticPartFn E wind α hK,
      partFn_eq_quadraticPartFn (E.dual wind α hα hK) wind _ (fun _ => rfl)]
  exact Simplicial.dual_pair_variational α hα

/-! ## Self-Dual Mean Energy: Uniqueness

Two bounds sandwiching `⟨k²⟩_α` against `1/(4α)` — the upper bound for
α ≥ π follows from `N_nonneg`, the lower bound for α ≤ π follows by
reflecting the upper bound through the T-duality FE. At α = π the two
collide: `⟨k²⟩_π = 1/(4π)`, uniquely. -/

/-- Upper bound: for α ≥ π, `⟨k²⟩_α ≤ 1/(4α)`. Direct from `N_nonneg`. -/
theorem quadraticMeanEnergy_le_inv (α : ℝ) (hα : Real.pi ≤ α) :
    quadraticMeanEnergy α ≤ 1 / (4 * α) := by
  have hα_pos : 0 < α := lt_of_lt_of_le Real.pi_pos hα
  have hZ_pos : 0 < quadraticPartFn α :=
    lt_trans one_pos (quadraticPartFn_gt_one α hα_pos)
  have h4α_pos : (0 : ℝ) < 4 * α := by linarith
  have h1 := Meno.QuadraticAction.summable_scalarPartFn α hα_pos
  have h2 : Summable (fun k : ℤ =>
      4 * α * ((k : ℝ)^2 * Real.exp (-α * (k : ℝ)^2))) :=
    (summable_sq_mul_exp α hα_pos).mul_left (4 * α)
  have hsplit :
      (∑' k : ℤ, (1 - 4 * α * (k : ℝ)^2) * Real.exp (-α * (k : ℝ)^2)) =
      quadraticPartFn α -
        4 * α * (∑' k : ℤ, (k : ℝ)^2 * Real.exp (-α * (k : ℝ)^2)) := by
    unfold quadraticPartFn
    rw [show (fun k : ℤ => (1 - 4 * α * (k : ℝ)^2) * Real.exp (-α * (k : ℝ)^2)) =
        (fun k : ℤ => Real.exp (-α * (k : ℝ)^2) -
          4 * α * ((k : ℝ)^2 * Real.exp (-α * (k : ℝ)^2))) from
      funext fun k => by ring]
    rw [h1.tsum_sub h2, tsum_mul_left]
  have hN := N_nonneg α hα
  rw [hsplit] at hN
  unfold quadraticMeanEnergy
  rw [div_le_div_iff₀ hZ_pos h4α_pos]
  linarith

/-- Strict upper bound: for α > π, `⟨k²⟩_α < 1/(4α)`. Uses `N_pos` strictly. -/
theorem quadraticMeanEnergy_lt_inv (α : ℝ) (hα : Real.pi < α) :
    quadraticMeanEnergy α < 1 / (4 * α) := by
  have hα_pos : 0 < α := lt_trans Real.pi_pos hα
  have hZ_pos : 0 < quadraticPartFn α :=
    lt_trans one_pos (quadraticPartFn_gt_one α hα_pos)
  have h4α_pos : (0 : ℝ) < 4 * α := by linarith
  have h1 := Meno.QuadraticAction.summable_scalarPartFn α hα_pos
  have h2 : Summable (fun k : ℤ =>
      4 * α * ((k : ℝ)^2 * Real.exp (-α * (k : ℝ)^2))) :=
    (summable_sq_mul_exp α hα_pos).mul_left (4 * α)
  have hsplit :
      (∑' k : ℤ, (1 - 4 * α * (k : ℝ)^2) * Real.exp (-α * (k : ℝ)^2)) =
      quadraticPartFn α -
        4 * α * (∑' k : ℤ, (k : ℝ)^2 * Real.exp (-α * (k : ℝ)^2)) := by
    unfold quadraticPartFn
    rw [show (fun k : ℤ => (1 - 4 * α * (k : ℝ)^2) * Real.exp (-α * (k : ℝ)^2)) =
        (fun k : ℤ => Real.exp (-α * (k : ℝ)^2) -
          4 * α * ((k : ℝ)^2 * Real.exp (-α * (k : ℝ)^2))) from
      funext fun k => by ring]
    rw [h1.tsum_sub h2, tsum_mul_left]
  have hN := N_pos α hα
  rw [hsplit] at hN
  unfold quadraticMeanEnergy
  rw [div_lt_div_iff₀ hZ_pos h4α_pos]
  linarith

/-- Lower bound: for 0 < α ≤ π, `⟨k²⟩_α ≥ 1/(4α)`. Via the T-duality FE and
    the upper bound at π²/α ≥ π. -/
theorem quadraticMeanEnergy_ge_inv (α : ℝ) (hα : 0 < α) (hαπ : α ≤ Real.pi) :
    1 / (4 * α) ≤ quadraticMeanEnergy α := by
  have hπ := Real.pi_pos
  have hπα_ge : Real.pi ≤ Real.pi ^ 2 / α := by
    rw [le_div_iff₀ hα]; nlinarith
  have h_upper_dual := quadraticMeanEnergy_le_inv (Real.pi ^ 2 / α) hπα_ge
  have hFE := quadraticMeanEnergy_T_dual α hα
  have h_coeff_nonneg : (0 : ℝ) ≤ Real.pi ^ 2 / α ^ 2 := by positivity
  have h_mul : (Real.pi ^ 2 / α ^ 2) * quadraticMeanEnergy (Real.pi ^ 2 / α) ≤
      (Real.pi ^ 2 / α ^ 2) * (1 / (4 * (Real.pi ^ 2 / α))) :=
    mul_le_mul_of_nonneg_left h_upper_dual h_coeff_nonneg
  have h_simp : (Real.pi ^ 2 / α ^ 2) * (1 / (4 * (Real.pi ^ 2 / α))) = 1 / (4 * α) := by
    have hα_ne : α ≠ 0 := ne_of_gt hα
    have hπ_ne : Real.pi ≠ 0 := ne_of_gt hπ
    field_simp
  rw [h_simp] at h_mul
  have harith : (1 : ℝ) / (2 * α) - 1 / (4 * α) = 1 / (4 * α) := by
    have hα_ne : α ≠ 0 := ne_of_gt hα
    field_simp
    ring
  linarith

/-- Strict lower bound: for 0 < α < π, `1/(4α) < ⟨k²⟩_α`.
    Via T-duality FE and the strict upper bound at π²/α > π. -/
theorem quadraticMeanEnergy_gt_inv (α : ℝ) (hα : 0 < α) (hαπ : α < Real.pi) :
    1 / (4 * α) < quadraticMeanEnergy α := by
  have hπ := Real.pi_pos
  have hπα_gt : Real.pi < Real.pi ^ 2 / α := by
    rw [lt_div_iff₀ hα]; nlinarith
  have h_upper_dual := quadraticMeanEnergy_lt_inv (Real.pi ^ 2 / α) hπα_gt
  have hFE := quadraticMeanEnergy_T_dual α hα
  have h_coeff_pos : (0 : ℝ) < Real.pi ^ 2 / α ^ 2 := by positivity
  have h_mul : (Real.pi ^ 2 / α ^ 2) * quadraticMeanEnergy (Real.pi ^ 2 / α) <
      (Real.pi ^ 2 / α ^ 2) * (1 / (4 * (Real.pi ^ 2 / α))) :=
    mul_lt_mul_of_pos_left h_upper_dual h_coeff_pos
  have h_simp : (Real.pi ^ 2 / α ^ 2) * (1 / (4 * (Real.pi ^ 2 / α))) = 1 / (4 * α) := by
    have hα_ne : α ≠ 0 := ne_of_gt hα
    have hπ_ne : Real.pi ≠ 0 := ne_of_gt hπ
    field_simp
  rw [h_simp] at h_mul
  have harith : (1 : ℝ) / (2 * α) - 1 / (4 * α) = 1 / (4 * α) := by
    have hα_ne : α ≠ 0 := ne_of_gt hα
    field_simp
    ring
  linarith

/-- Positivity of the mean energy: `⟨k²⟩_α > 0` for all α > 0.
    The numerator is strictly positive via the k = 1 term. -/
theorem quadraticMeanEnergy_pos (α : ℝ) (hα : 0 < α) :
    0 < quadraticMeanEnergy α := by
  have hZ_pos : 0 < quadraticPartFn α :=
    lt_trans one_pos (quadraticPartFn_gt_one α hα)
  have hsum := summable_sq_mul_exp α hα
  have h_nonneg : ∀ k : ℤ, 0 ≤ (k : ℝ) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2) :=
    fun k => mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _))
  have h_one_pos : 0 < ((1 : ℤ) : ℝ) ^ 2 * Real.exp (-α * ((1 : ℤ) : ℝ) ^ 2) := by
    push_cast; positivity
  have h_num_pos : 0 < ∑' k : ℤ, (k : ℝ) ^ 2 * Real.exp (-α * (k : ℝ) ^ 2) := by
    rw [show (0 : ℝ) = ∑' _ : ℤ, (0 : ℝ) from tsum_zero.symm]
    exact Summable.tsum_lt_tsum (i := (1 : ℤ))
      (fun k => h_nonneg k) h_one_pos summable_zero hsum
  unfold quadraticMeanEnergy
  exact div_pos h_num_pos hZ_pos

/-- Symmetric (halving) form of the T-duality FE for mean energy:
    `α·⟨k²⟩_α + (π²/α)·⟨k²⟩_{π²/α} = 1/2`.
    The product `α·⟨k²⟩_α` at the two T-dual couplings averages to `1/4`. -/
theorem quadraticMeanEnergy_T_dual_symmetric (α : ℝ) (hα : 0 < α) :
    α * quadraticMeanEnergy α +
      (Real.pi ^ 2 / α) * quadraticMeanEnergy (Real.pi ^ 2 / α) = 1 / 2 := by
  have hFE := quadraticMeanEnergy_T_dual α hα
  have hα_ne : α ≠ 0 := ne_of_gt hα
  have h_mul_FE : α * ((Real.pi ^ 2 / α ^ 2) * quadraticMeanEnergy (Real.pi ^ 2 / α) +
         quadraticMeanEnergy α) = α * (1 / (2 * α)) := by
    rw [hFE]
  have halg : α * ((Real.pi ^ 2 / α ^ 2) * quadraticMeanEnergy (Real.pi ^ 2 / α) +
              quadraticMeanEnergy α) =
              α * quadraticMeanEnergy α +
              (Real.pi ^ 2 / α) * quadraticMeanEnergy (Real.pi ^ 2 / α) := by
    field_simp
    ring
  have hhalf : α * (1 / (2 * α)) = 1 / 2 := by
    field_simp
  linarith [halg ▸ h_mul_FE, hhalf]

/-- `α·⟨k²⟩_α = 1/4 ↔ α = π`.  The product `α·⟨k²⟩_α` on `(0, ∞)` equals
    `1/4` iff α is the self-dual coupling.  Equivalent to
    `quadraticMeanEnergy_self_dual_iff` via multiplication by α. -/
theorem quadraticMeanEnergy_mul_eq_quarter_iff (α : ℝ) (hα : 0 < α) :
    α * quadraticMeanEnergy α = 1 / 4 ↔ α = Real.pi := by
  have hα_ne : α ≠ 0 := ne_of_gt hα
  have hsimp : α * (1 / (4 * α)) = 1 / 4 := by field_simp
  constructor
  · intro h
    rcases lt_trichotomy α Real.pi with h1 | h1 | h1
    · have hlow := quadraticMeanEnergy_gt_inv α hα h1
      have hmul : α * (1 / (4 * α)) < α * quadraticMeanEnergy α :=
        mul_lt_mul_of_pos_left hlow hα
      linarith
    · exact h1
    · have hup := quadraticMeanEnergy_lt_inv α h1
      have hmul : α * quadraticMeanEnergy α < α * (1 / (4 * α)) :=
        mul_lt_mul_of_pos_left hup hα
      linarith
  · intro h
    have hπ_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    rw [h, quadraticMeanEnergy_self_dual]
    field_simp

/-- The self-dual coupling α = π is the UNIQUE α > 0 with `⟨k²⟩_α = 1/(4π)`.
    Mirrors `quadraticPartFn_self_dual_iff` at the level of mean energy. -/
theorem quadraticMeanEnergy_self_dual_iff (α : ℝ) (hα : 0 < α) :
    quadraticMeanEnergy α = 1 / (4 * Real.pi) ↔ α = Real.pi := by
  refine ⟨fun h => ?_, fun h => h ▸ quadraticMeanEnergy_self_dual⟩
  rcases lt_trichotomy α Real.pi with h1 | h1 | h1
  · have hlow := quadraticMeanEnergy_ge_inv α hα (le_of_lt h1)
    have hlt : 1 / (4 * Real.pi) < 1 / (4 * α) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      linarith
    linarith
  · exact h1
  · have hup := quadraticMeanEnergy_le_inv α (le_of_lt h1)
    have hlt : 1 / (4 * α) < 1 / (4 * Real.pi) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      linarith
    linarith

/-- Corollary: the mean energy is strictly below the self-dual value iff α > π. -/
theorem quadraticMeanEnergy_lt_self_dual_iff (α : ℝ) (hα : 0 < α) :
    quadraticMeanEnergy α < 1 / (4 * Real.pi) ↔ Real.pi < α := by
  constructor
  · intro h
    by_contra h_not
    push_neg at h_not
    have hlow := quadraticMeanEnergy_ge_inv α hα h_not
    have hle : 1 / (4 * Real.pi) ≤ 1 / (4 * α) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  · intro hπα
    have hup := quadraticMeanEnergy_le_inv α (le_of_lt hπα)
    have hlt : 1 / (4 * α) < 1 / (4 * Real.pi) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith

/-- Corollary: the mean energy is strictly above the self-dual value iff α < π. -/
theorem quadraticMeanEnergy_gt_self_dual_iff (α : ℝ) (hα : 0 < α) :
    1 / (4 * Real.pi) < quadraticMeanEnergy α ↔ α < Real.pi := by
  constructor
  · intro h
    by_contra h_not
    push_neg at h_not
    have hup := quadraticMeanEnergy_le_inv α h_not
    have hle : 1 / (4 * α) ≤ 1 / (4 * Real.pi) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  · intro hαπ
    have hlow := quadraticMeanEnergy_ge_inv α hα (le_of_lt hαπ)
    have hlt : 1 / (4 * Real.pi) < 1 / (4 * α) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith

/-- **Canonical self-dual winding moment.** Gibbs mean of `(canonical winding)²`
    on `quadraticObj π Real.pi_pos` equals `1/(4π)`. The winding is *derived* from
    the one-object groupoid `SingleObj (Multiplicative ℤ)` via `quadraticWind`; no
    external data is required. This is the undecorated groupoid-level version:
    the groupoid alone witnesses `End ≃ ℤ`. -/
theorem quadraticObj_meanWindingSq_self_dual :
    (quadraticObj Real.pi Real.pi_pos).gibbsExpect
        (fun g => (quadraticWind g : ℝ) ^ 2) = 1 / (4 * Real.pi) :=
  ((quadraticObj Real.pi Real.pi_pos).gibbsExpect_wind_sq_eq
      quadraticWind Real.pi Real.pi_pos
      (quadraticObj_energy Real.pi Real.pi_pos)).trans
    quadraticMeanEnergy_self_dual

/-- **Canonical self-dual mean energy.** Gibbs mean of the energy on
    `quadraticObj π Real.pi_pos` equals `1/4`.  Derived from
    `quadraticObj_meanWindingSq_self_dual` by factoring π out of the energy.
    Like its companion, this version takes no external winding data: the
    canonical `quadraticWind` is built from the groupoid's own structure. -/
theorem quadraticObj_meanEnergy_self_dual :
    (quadraticObj Real.pi Real.pi_pos).gibbsExpect
        (fun g => (quadraticObj Real.pi Real.pi_pos).energy g) = 1 / 4 := by
  have h := quadraticObj_meanWindingSq_self_dual
  unfold GroupoidObj.gibbsExpect at h ⊢
  have h_sum :
      ∑' g : End (quadraticObj Real.pi Real.pi_pos).base,
        (quadraticObj Real.pi Real.pi_pos).energy g *
          (quadraticObj Real.pi Real.pi_pos).gibbsMass g =
      Real.pi *
        ∑' g : End (quadraticObj Real.pi Real.pi_pos).base,
          (fun g => (quadraticWind g : ℝ) ^ 2) g *
            (quadraticObj Real.pi Real.pi_pos).gibbsMass g := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun g => ?_)
    simp only
    rw [quadraticObj_energy Real.pi Real.pi_pos g]
    ring
  rw [h_sum, h]
  field_simp

/-! ## Completed Partition Function: T-duality invariant

The "completed" Jacobi theta is `f(α) = (α/π)^(1/4) · Z(α)`, T-duality invariant:
`f(π²/α) = f(α)`. Its unique minimum on `(0, ∞)` is at the self-dual point
`α = π`, where `f(π) = Z(π)`. -/

/-- Completed partition function: `f(α) = (α/π)^(1/4) · Z(α)`. -/
noncomputable def completedPartFn (α : ℝ) : ℝ :=
  (α / Real.pi) ^ ((1 : ℝ) / 4) * quadraticPartFn α

theorem completedPartFn_at_self_dual :
    completedPartFn Real.pi = quadraticPartFn Real.pi := by
  unfold completedPartFn
  rw [div_self (ne_of_gt Real.pi_pos), Real.one_rpow, one_mul]

theorem completedPartFn_T_dual (α : ℝ) (hα : 0 < α) :
    completedPartFn (Real.pi ^ 2 / α) = completedPartFn α := by
  unfold completedPartFn
  have hαπ_pos : 0 < α / Real.pi := div_pos hα Real.pi_pos
  have h_ratio : Real.pi ^ 2 / α / Real.pi = (α / Real.pi)⁻¹ := by
    rw [inv_div]; field_simp
  rw [h_ratio, quadraticPartFn_duality_real α hα,
      Real.inv_rpow (le_of_lt hαπ_pos),
      ← Real.rpow_neg (le_of_lt hαπ_pos),
      ← mul_assoc, ← Real.rpow_add hαπ_pos]
  congr 2
  norm_num

/-- Derivative of `log(completedPartFn α) = (1/4) log(α/π) + log Z(α)`:
    `1/(4α) - ⟨k²⟩_α`. Zero exactly at α = π (where ⟨k²⟩ = 1/(4π)). -/
private lemma hasDerivAt_log_completedPartFn (β : ℝ) (hβ : 0 < β) :
    HasDerivAt (fun α : ℝ => (1/4 : ℝ) * Real.log (α / Real.pi) +
                             Real.log (quadraticPartFn α))
      (1 / (4 * β) - quadraticMeanEnergy β) β := by
  have hπ := Real.pi_pos
  have hβπ : 0 < β / Real.pi := div_pos hβ hπ
  have h_div : HasDerivAt (fun α : ℝ => α / Real.pi) (1 / Real.pi) β := by
    simpa using (hasDerivAt_id β).div_const Real.pi
  have h_log_div : HasDerivAt (fun α => Real.log (α / Real.pi)) (1 / β) β := by
    have := h_div.log (ne_of_gt hβπ)
    convert this using 1
    field_simp
  have h_quart : HasDerivAt (fun α : ℝ => (1/4 : ℝ) * Real.log (α / Real.pi))
      (1 / (4 * β)) β := by
    have := h_log_div.const_mul ((1 : ℝ) / 4)
    convert this using 1
    ring
  exact h_quart.add (hasDerivAt_log_quadraticPartFn β hβ)

/-- **Strict minimum of the completed partition function at the self-dual point.**

    For any `α > 0` with `α ≠ π`, `f(α) > f(π) = Z(π)`.

    The self-dual coupling `α = π` is the unique minimum of the T-duality
    invariant `f(α) = (α/π)^(1/4) · Z(α)` on `(0, ∞)`. Proof via the
    sign of `d(log f)/dα = 1/(4α) - ⟨k²⟩_α`: negative for `α < π`,
    positive for `α > π` (by `quadraticMeanEnergy_gt_inv` / `_lt_inv`),
    so `log f` strictly decreases on `(0, π]` and strictly increases on `[π, ∞)`. -/
theorem completedPartFn_strictMin (α : ℝ) (hα : 0 < α) (hαπ : α ≠ Real.pi) :
    quadraticPartFn Real.pi < completedPartFn α := by
  set g : ℝ → ℝ := fun β => (1/4 : ℝ) * Real.log (β / Real.pi) +
                              Real.log (quadraticPartFn β) with hg_def
  have hπ := Real.pi_pos
  have hZπ_pos : 0 < quadraticPartFn Real.pi :=
    lt_trans one_pos (quadraticPartFn_gt_one Real.pi hπ)
  have hZα_pos : 0 < quadraticPartFn α :=
    lt_trans one_pos (quadraticPartFn_gt_one α hα)
  have hαπ_pos : 0 < α / Real.pi := div_pos hα hπ
  have hf_pos : 0 < completedPartFn α :=
    mul_pos (Real.rpow_pos_of_pos hαπ_pos _) hZα_pos
  have hlog_α : Real.log (completedPartFn α) = g α := by
    show Real.log ((α/Real.pi)^((1:ℝ)/4) * quadraticPartFn α) = _
    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hαπ_pos _)) (ne_of_gt hZα_pos),
        Real.log_rpow hαπ_pos]
  have hg_π : g Real.pi = Real.log (quadraticPartFn Real.pi) := by
    show (1/4 : ℝ) * Real.log (Real.pi / Real.pi) +
         Real.log (quadraticPartFn Real.pi) = _
    rw [div_self (ne_of_gt hπ), Real.log_one, mul_zero, zero_add]
  suffices h_strict : g Real.pi < g α by
    rw [hg_π, ← hlog_α] at h_strict
    exact (Real.log_lt_log_iff hZπ_pos hf_pos).mp h_strict
  rcases lt_or_gt_of_ne hαπ with h_lt | h_gt
  · have h_anti : StrictAntiOn g (Set.Ioc 0 Real.pi) := by
      apply strictAntiOn_of_deriv_neg (convex_Ioc _ _)
      · intro β ⟨hβ, _⟩
        exact (hasDerivAt_log_completedPartFn β hβ).continuousAt.continuousWithinAt
      · intro β hβ
        rw [interior_Ioc] at hβ
        obtain ⟨hβ_pos, hβπ⟩ := hβ
        rw [(hasDerivAt_log_completedPartFn β hβ_pos).deriv]
        have h := quadraticMeanEnergy_gt_inv β hβ_pos hβπ
        linarith
    exact h_anti ⟨hα, le_of_lt h_lt⟩ ⟨hπ, le_refl _⟩ h_lt
  · have h_mono : StrictMonoOn g (Set.Ici Real.pi) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici _)
      · intro β hβ
        have hβ_pos : 0 < β := lt_of_lt_of_le hπ hβ
        exact (hasDerivAt_log_completedPartFn β hβ_pos).continuousAt.continuousWithinAt
      · intro β hβ
        rw [interior_Ici] at hβ
        have hβ_pos : 0 < β := lt_trans hπ hβ
        rw [(hasDerivAt_log_completedPartFn β hβ_pos).deriv]
        have h := quadraticMeanEnergy_lt_inv β hβ
        linarith
    exact h_mono (Set.left_mem_Ici) (le_of_lt h_gt) h_gt

/-- **Non-strict form of the self-dual minimum**: `Z(π) ≤ f(α)` for every `α > 0`.
    Covers the boundary case `α = π` (equality) along with the strict version. -/
theorem completedPartFn_ge_self_dual (α : ℝ) (hα : 0 < α) :
    quadraticPartFn Real.pi ≤ completedPartFn α := by
  rcases eq_or_ne α Real.pi with rfl | hne
  · exact completedPartFn_at_self_dual.ge
  · exact (completedPartFn_strictMin α hα hne).le

/-- **Sharp uniqueness**: `f(α) = Z(π)` iff `α = π`.

    Every `α ≠ π` gives `f(α) > Z(π)` (strict by `completedPartFn_strictMin`), and
    `f(π) = Z(π)` by `completedPartFn_at_self_dual`. So the self-dual coupling is the
    unique point on `(0, ∞)` where the T-duality-invariant completed partition
    function matches its self-dual value — equivalently, the unique minimizer of
    `f` on `(0, ∞)`. -/
theorem completedPartFn_eq_self_dual_iff (α : ℝ) (hα : 0 < α) :
    completedPartFn α = quadraticPartFn Real.pi ↔ α = Real.pi := by
  refine ⟨fun h => ?_, fun h => h ▸ completedPartFn_at_self_dual⟩
  by_contra hne
  exact absurd h (ne_of_gt (completedPartFn_strictMin α hα hne))

/-! ## Mass Duality

Geodesic mass (combinatorial, ℕ) and harmonic mass (analytic, ℝ) are reciprocal:
their product is 1. T-duality exchanges these two measures. -/

theorem mass_duality (n : ℕ) (hn : n ≥ 3) :
    (↑(geodesicLength (CycleGraph n hn) (cycleWalk n hn)) : ℝ) * harmonicEnergy n hn = 1 := by
  rw [cycleGraph_geodesic_eq_n, cycleGraph_harmonicEnergy]
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

end Simplicial
