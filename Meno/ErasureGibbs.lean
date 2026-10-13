import Meno.Erasure

/-! # The erasure rate under a noise law

The counting rate law (`sum_erasure_ge`) in the Gibbs chart. A memory
law `P` on cocycles and memory, an independent error law `Q`, and a
reset `Φ`: the input law is `I = (P ⊗ Q)` pushed along
`((x, m), s) ↦ (x + s, m)` (`TwoComplex.noisyIn`), the next law is
`Φ_* I`, and the tick's erasure is the conditional entropy `H(I | Φ)`
— by the chain rule, exactly what `Φ` removes from the entropy.

* **The input bound** (`entropy_input_ge`): `H(I) ≥ H(P) + H(σ_* Q)` —
  noise adds at least the syndrome entropy.
* **The tick law** (`entropy_tick`):
  `H(P) + H(σ_* Q) ≤ H(Φ_* I) + H(I | Φ)`.
* **THE RATE LAW** (`sum_condEntropy_ge`): over `T` ticks,
  `Σ H(Iₜ | Φₜ) ≥ T · H(σ_* Q) + H(P₀) − log |cocycles × M|` — the
  average erasure per tick is at least the syndrome entropy, the first
  term of the error-entropy split (`entropy_split`).
* **Attainment** (`Decoder.condEntropy_reset_le`): a decoder's reset
  erases at most `H(σ_* Q)` per tick.

The library facts beneath are one inequality, `log t ≤ t − 1`: the
cross-entropy bound against any support-dominating subprobability
(`FinDist.entropy_le_crossEntropy`), whence conditional entropy is
nonnegative (`FinDist.condEntropy_nonneg`), entropy is additive on
products (`FinDist.entropy_prod`) and subadditive along a separating
pair of maps (`FinDist.entropy_le_map_add_map`). -/

namespace Meno

open scoped BigOperators
open Classical

universe u

namespace FinDist

variable {X Y D : Type u} [Fintype X] [Fintype Y] [Fintype D]

/-- **The cross-entropy bound**: entropy is at most the cross-entropy
against any subprobability positive on the support. -/
theorem entropy_le_crossEntropy (P : FinDist X) (r : X → ℝ) (hr : ∀ x, 0 ≤ r x)
    (hsum : ∑ x, r x ≤ 1) (hsupp : ∀ x, 0 < P.mass x → 0 < r x) :
    P.entropy ≤ -∑ x, P.mass x * Real.log (r x) := by
  have hterm : ∀ x, P.mass x - r x
      ≤ P.mass x * Real.log (P.mass x) - P.mass x * Real.log (r x) := by
    intro x
    rcases eq_or_lt_of_le (P.nonneg x) with h0 | hp
    · rw [← h0]
      simp [hr x]
    · have hrx := hsupp x hp
      have h := Real.log_le_sub_one_of_pos (div_pos hrx hp)
      rw [Real.log_div hrx.ne' hp.ne'] at h
      have h' := mul_le_mul_of_nonneg_left h hp.le
      have hc : P.mass x * (r x / P.mass x) = r x := by field_simp
      rw [mul_sub, mul_sub, mul_one, hc] at h'
      linarith
  have hs := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hterm x
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, P.sum_one] at hs
  show -∑ x, P.mass x * Real.log (P.mass x) ≤ _
  linarith

/-- **Conditional entropy is nonnegative.** -/
theorem condEntropy_nonneg [DecidableEq D] (f : X → D) (P : FinDist X) : 0 ≤ P.condEntropy f := by
  unfold condEntropy
  rw [neg_nonneg]
  refine Finset.sum_nonpos fun x _ => ?_
  rcases eq_or_lt_of_le (P.nonneg x) with h0 | hp
  · rw [← h0, zero_mul]
  · have hm := mass_le_map f P x
    exact mul_nonpos_of_nonneg_of_nonpos hp.le
      (Real.log_nonpos (div_nonneg hp.le (hp.le.trans hm))
        ((div_le_one (hp.trans_le hm)).mpr hm))

/-- Summing a composite against a law is summing against the
pushforward. -/
theorem sum_mass_comp [DecidableEq D] (f : X → D) (P : FinDist X) (φ : D → ℝ) :
    ∑ x, P.mass x * φ (f x) = ∑ d, (P.map f).mass d * φ d := by
  rw [← Finset.sum_fiberwise Finset.univ f (fun x => P.mass x * φ (f x))]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
    ← Finset.sum_mul]
  rfl

/-- **The product law**. -/
noncomputable def prod (P : FinDist X) (Q : FinDist Y) : FinDist (X × Y) where
  mass p := P.mass p.1 * Q.mass p.2
  nonneg p := mul_nonneg (P.nonneg _) (Q.nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, Q.sum_one, mul_one, P.sum_one]

/-- **Entropy is additive on products.** -/
theorem entropy_prod (P : FinDist X) (Q : FinDist Y) :
    (P.prod Q).entropy = P.entropy + Q.entropy := by
  have hterm : ∀ x y, P.mass x * Q.mass y * Real.log (P.mass x * Q.mass y)
      = Q.mass y * (P.mass x * Real.log (P.mass x))
        + P.mass x * (Q.mass y * Real.log (Q.mass y)) := by
    intro x y
    rcases eq_or_lt_of_le (P.nonneg x) with hp | hp
    · rw [← hp]
      simp
    rcases eq_or_lt_of_le (Q.nonneg y) with hq | hq
    · rw [← hq]
      simp
    rw [Real.log_mul hp.ne' hq.ne']
    ring
  show -∑ p : X × Y, P.mass p.1 * Q.mass p.2 * Real.log (P.mass p.1 * Q.mass p.2)
    = -∑ x, P.mass x * Real.log (P.mass x) + -∑ y, Q.mass y * Real.log (Q.mass y)
  rw [Fintype.sum_prod_type]
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Q.sum_one,
    one_mul, ← Finset.sum_mul, P.sum_one, one_mul]
  ring

/-- The second marginal of a product. -/
theorem map_snd_prod [DecidableEq Y] (P : FinDist X) (Q : FinDist Y) : (P.prod Q).map Prod.snd = Q := by
  apply ext
  funext y
  show ∑ p ∈ Finset.univ.filter (fun p : X × Y => p.2 = y), P.mass p.1 * Q.mass p.2
    = Q.mass y
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq', ← Finset.sum_mul, P.sum_one]

/-- **Subadditivity**: along two maps that together separate points,
entropy is at most the sum of the two pushforward entropies. -/
theorem entropy_le_map_add_map {A B : Type u} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (f : X → A)
    (g : X → B) (hfg : Function.Injective fun x => (f x, g x)) (P : FinDist X) :
    P.entropy ≤ (P.map f).entropy + (P.map g).entropy := by
  have hsum : ∑ x, (P.map f).mass (f x) * (P.map g).mass (g x) ≤ 1 := by
    have h1 : ∑ x, (P.map f).mass (f x) * (P.map g).mass (g x)
        = ∑ p ∈ Finset.univ.image (fun x => (f x, g x)),
            (P.map f).mass p.1 * (P.map g).mass p.2 :=
      (Finset.sum_image (f := fun p : A × B => (P.map f).mass p.1 * (P.map g).mass p.2)
        fun x _ y _ h => hfg h).symm
    rw [h1, ← ((P.map f).prod (P.map g)).sum_one]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun p _ _ => mul_nonneg ((P.map f).nonneg _) ((P.map g).nonneg _)
  have h := P.entropy_le_crossEntropy
    (fun x => (P.map f).mass (f x) * (P.map g).mass (g x))
    (fun x => mul_nonneg ((P.map f).nonneg _) ((P.map g).nonneg _)) hsum
    fun x hp => mul_pos (hp.trans_le (mass_le_map f P x)) (hp.trans_le (mass_le_map g P x))
  have hsplit : ∀ x, P.mass x * Real.log ((P.map f).mass (f x) * (P.map g).mass (g x))
      = P.mass x * Real.log ((P.map f).mass (f x))
        + P.mass x * Real.log ((P.map g).mass (g x)) := by
    intro x
    rcases eq_or_lt_of_le (P.nonneg x) with h0 | hp
    · rw [← h0]
      simp
    · rw [Real.log_mul (hp.trans_le (mass_le_map f P x)).ne'
        (hp.trans_le (mass_le_map g P x)).ne', mul_add]
  simp_rw [hsplit, Finset.sum_add_distrib] at h
  rw [P.sum_mass_comp f (fun a => Real.log ((P.map f).mass a)),
    P.sum_mass_comp g (fun b => Real.log ((P.map g).mass b))] at h
  show _ ≤ -∑ a, (P.map f).mass a * Real.log ((P.map f).mass a)
    + -∑ b, (P.map g).mass b * Real.log ((P.map g).mass b)
  linarith

end FinDist

namespace TwoComplex

variable {G : IncidenceGraph.{u}} (X : TwoComplex.{u} G) (R : Type u) [CommRing R]
  [Fintype R] [Fintype X.Faces]

/-- **The noisy input map**: `((x, m), s) ↦ (x + s, m)`. -/
def noisyIn {M : Type u} (ω : (X.cocyclesR R × M) × (G.E → R)) : (G.E → R) × M :=
  ((ω.1.1 : G.E → R) + ω.2, ω.1.2)

omit [Fintype R] [Fintype X.Faces] in
theorem syndrome_noisyIn {M : Type u} (ω : (X.cocyclesR R × M) × (G.E → R)) :
    X.syndrome R (X.noisyIn R ω).1 = X.syndrome R ω.2 := by
  show X.syndrome R ((ω.1.1 : G.E → R) + ω.2) = _
  rw [map_add, LinearMap.mem_ker.mp ω.1.1.2, zero_add]

/-- The input law's syndrome is the error law's syndrome. -/
theorem map_syndrome_input {M : Type u} [Fintype M] (P : FinDist (X.cocyclesR R × M))
    (Q : FinDist (G.E → R)) :
    ((P.prod Q).map (X.noisyIn R)).map (X.syndrome R ∘ Prod.fst) = Q.map (X.syndrome R) := by
  rw [← FinDist.map_comp]
  have hf : (X.syndrome R ∘ Prod.fst) ∘ X.noisyIn R (M := M)
      = X.syndrome R ∘ Prod.snd := funext fun ω => X.syndrome_noisyIn R ω
  rw [hf, FinDist.map_comp, FinDist.map_snd_prod]

/-- **The input bound**: noise adds at least the syndrome entropy. -/
theorem entropy_input_ge {M : Type u} [Fintype M] (P : FinDist (X.cocyclesR R × M))
    (Q : FinDist (G.E → R)) :
    P.entropy + (Q.map (X.syndrome R)).entropy
      ≤ ((P.prod Q).map (X.noisyIn R)).entropy := by
  set μ := P.prod Q
  set I := μ.map (X.noisyIn R)
  set q := Q.map (X.syndrome R)
  have hIσ := X.map_syndrome_input R P Q
  -- the reference subprobability on `(Z × M) × V`
  set r : (X.cocyclesR R × M) × (G.E → R) → ℝ :=
    fun ω => I.mass (X.noisyIn R ω) * Q.mass ω.2 / q.mass (X.syndrome R ω.2)
  have hr : ∀ ω, 0 ≤ r ω := fun ω =>
    div_nonneg (mul_nonneg (I.nonneg _) (Q.nonneg _)) (q.nonneg _)
  have hinner : ∀ s : G.E → R,
      ∑ a : X.cocyclesR R × M, I.mass (X.noisyIn R (a, s)) ≤ q.mass (X.syndrome R s) := by
    intro s
    have hinj : Set.InjOn (fun a : X.cocyclesR R × M => X.noisyIn R (a, s))
        ↑(Finset.univ : Finset (X.cocyclesR R × M)) := by
      intro a _ a' _ h
      have h1 : (a.1 : G.E → R) + s = a'.1 + s := congrArg Prod.fst h
      have h2 : (X.noisyIn R (a, s)).2 = (X.noisyIn R (a', s)).2 := congrArg Prod.snd h
      exact Prod.ext (Subtype.ext (add_right_cancel h1)) h2
    rw [← Finset.sum_image hinj]
    calc _ ≤ ∑ p ∈ Finset.univ.filter
          (fun p : (G.E → R) × M => (X.syndrome R ∘ Prod.fst) p = X.syndrome R s), I.mass p := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => I.nonneg p
          intro p hp
          obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, X.syndrome_noisyIn R (a, s)⟩
      _ = (I.map (X.syndrome R ∘ Prod.fst)).mass (X.syndrome R s) := rfl
      _ = q.mass (X.syndrome R s) := by rw [hIσ]
  have hsum : ∑ ω, r ω ≤ 1 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm, ← Q.sum_one]
    refine Finset.sum_le_sum fun s _ => ?_
    simp only [r]
    rw [← Finset.sum_div, ← Finset.sum_mul]
    rcases eq_or_lt_of_le (q.nonneg (X.syndrome R s)) with hq | hq
    · rw [← hq, div_zero]
      exact Q.nonneg s
    · rw [div_le_iff₀ hq]
      exact mul_le_mul_of_nonneg_right (hinner s) (Q.nonneg s) |>.trans_eq (mul_comm _ _)
  have hpos : ∀ ω, 0 < μ.mass ω → 0 < I.mass (X.noisyIn R ω) ∧ 0 < Q.mass ω.2
      ∧ 0 < q.mass (X.syndrome R ω.2) := by
    intro ω hω
    have hQ : 0 < Q.mass ω.2 := by
      rcases eq_or_lt_of_le (Q.nonneg ω.2) with h0 | h
      · exfalso
        have : μ.mass ω = 0 := by
          show P.mass ω.1 * Q.mass ω.2 = 0
          rw [← h0, mul_zero]
        linarith
      · exact h
    exact ⟨hω.trans_le (FinDist.mass_le_map _ μ ω), hQ,
      hQ.trans_le (FinDist.mass_le_map _ Q ω.2)⟩
  have h := μ.entropy_le_crossEntropy r hr hsum fun ω hω => by
    obtain ⟨h1, h2, h3⟩ := hpos ω hω
    exact div_pos (mul_pos h1 h2) h3
  have hsplit : ∀ ω, μ.mass ω * Real.log (r ω)
      = μ.mass ω * Real.log (I.mass (X.noisyIn R ω)) + μ.mass ω * Real.log (Q.mass ω.2)
        - μ.mass ω * Real.log (q.mass (X.syndrome R ω.2)) := by
    intro ω
    rcases eq_or_lt_of_le (μ.nonneg ω) with h0 | hω
    · rw [← h0]
      simp
    · obtain ⟨h1, h2, h3⟩ := hpos ω hω
      simp only [r]
      rw [Real.log_div (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne']
      ring
  simp_rw [hsplit, Finset.sum_sub_distrib, Finset.sum_add_distrib] at h
  have h1 : ∑ ω, μ.mass ω * Real.log (I.mass (X.noisyIn R ω))
      = ∑ p, I.mass p * Real.log (I.mass p) :=
    μ.sum_mass_comp (X.noisyIn R) (fun p => Real.log (I.mass p))
  have h2 : ∑ ω, μ.mass ω * Real.log (Q.mass ω.2) = ∑ s, Q.mass s * Real.log (Q.mass s) := by
    have := μ.sum_mass_comp Prod.snd (fun s => Real.log (Q.mass s))
    rw [FinDist.map_snd_prod] at this
    exact this
  have h3 : ∑ ω, μ.mass ω * Real.log (q.mass (X.syndrome R ω.2))
      = ∑ τ, q.mass τ * Real.log (q.mass τ) := by
    have := μ.sum_mass_comp (X.syndrome R ∘ Prod.snd) (fun τ => Real.log (q.mass τ))
    rw [FinDist.map_comp, FinDist.map_snd_prod] at this
    exact this
  rw [h1, h2, h3] at h
  have hμ := FinDist.entropy_prod P Q
  have eI : I.entropy = -∑ p, I.mass p * Real.log (I.mass p) := rfl
  have eQ : Q.entropy = -∑ s, Q.mass s * Real.log (Q.mass s) := rfl
  have eq : q.entropy = -∑ τ, q.mass τ * Real.log (q.mass τ) := rfl
  linarith

/-- **The tick law**: the next law's entropy plus the tick's erasure is
at least the current law's entropy plus the syndrome entropy. -/
theorem entropy_tick {M : Type u} [Fintype M] (P : FinDist (X.cocyclesR R × M))
    (Q : FinDist (G.E → R)) (Φ : (G.E → R) × M → X.cocyclesR R × M) :
    P.entropy + (Q.map (X.syndrome R)).entropy
      ≤ (((P.prod Q).map (X.noisyIn R)).map Φ).entropy
        + ((P.prod Q).map (X.noisyIn R)).condEntropy Φ := by
  rw [← FinDist.entropy_eq_map_add_condEntropy]
  exact X.entropy_input_ge R P Q

/-- **THE RATE LAW**: over `T` ticks, the total erasure is at least
`T` syndrome entropies, less what the state space can hold. -/
theorem sum_condEntropy_ge {M : Type u} [Fintype M] [Nonempty M]
    (Q : FinDist (G.E → R)) (P : ℕ → FinDist (X.cocyclesR R × M))
    (Φ : ℕ → (G.E → R) × M → X.cocyclesR R × M)
    (hP : ∀ t, P (t + 1) = ((P t).prod Q |>.map (X.noisyIn R)).map (Φ t)) (T : ℕ) :
    T * (Q.map (X.syndrome R)).entropy + (P 0).entropy
        - Real.log (Fintype.card (X.cocyclesR R × M))
      ≤ ∑ t ∈ Finset.range T, ((P t).prod Q |>.map (X.noisyIn R)).condEntropy (Φ t) := by
  have key : ∀ T : ℕ, T * (Q.map (X.syndrome R)).entropy + (P 0).entropy
      ≤ (P T).entropy
        + ∑ t ∈ Finset.range T, ((P t).prod Q |>.map (X.noisyIn R)).condEntropy (Φ t) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      have := X.entropy_tick R (P T) Q (Φ T)
      rw [← hP T] at this
      rw [Finset.sum_range_succ]
      push_cast
      linarith
  have hT : (P T).entropy ≤ Real.log (Fintype.card (X.cocyclesR R × M)) := by
    have := (P T).defect_nonneg
    unfold FinDist.defect at this
    linarith
  linarith [key T]

variable {X R}

/-- **Attainment**: a decoder's reset erases at most the syndrome
entropy per tick. -/
theorem Decoder.condEntropy_reset_le {M : Type u} [Fintype M] (D : X.Decoder R)
    (P : FinDist (X.cocyclesR R × M)) (Q : FinDist (G.E → R)) :
    ((P.prod Q).map (X.noisyIn R)).condEntropy D.reset
      ≤ (Q.map (X.syndrome R)).entropy := by
  set I := (P.prod Q).map (X.noisyIn R)
  have hinj : Function.Injective fun p : (G.E → R) × M =>
      (D.reset p, (X.syndrome R ∘ Prod.fst) p) := by
    rintro ⟨y, m⟩ ⟨y', m'⟩ h
    have h1 := congrArg Prod.fst h
    have hσ : X.syndrome R y = X.syndrome R y' := congrArg Prod.snd h
    have hx : y - D.decode (X.syndrome R y) = y' - D.decode (X.syndrome R y') :=
      congrArg (fun z : X.cocyclesR R × M => (z.1 : G.E → R)) h1
    have hm : m = m' := congrArg Prod.snd h1
    rw [hσ] at hx
    exact Prod.ext (sub_left_inj.mp hx) hm
  have hsub := I.entropy_le_map_add_map D.reset (X.syndrome R ∘ Prod.fst) hinj
  rw [X.map_syndrome_input R P Q] at hsub
  have hchain := FinDist.entropy_eq_map_add_condEntropy D.reset I
  linarith

end TwoComplex

end Meno
