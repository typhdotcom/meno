import Meno.FundamentalPresentation

/-! # Basis Independence (C3)

**Any two integral presentations of a graph are `GL(r,ℤ)`-related**,
and the partition function is a function of the graph alone.

The mathematical spine:

* **Primitivity is forced** (`exists_int_coords`): every integral
  cycle lies in the `ℤ`-span of any presentation's basis. The proof
  pairs the cycle with the unit-period realizers supplied by
  `periods_onto`: if `x = Σ aᵢ ĉᵢ` over `ℝ` and `τ⁽ⁱ⁾` has periods
  `δᵢ`, then `aᵢ = ⟨τ⁽ⁱ⁾, x⟩ ∈ ℤ`. This is exactly where the Phase-24
  primitivity hypothesis is consumed: `periods_onto` *is*
  primitivity.
* **Unimodular relatedness** (`exists_rebase_related`): expressing
  each basis in the other yields integer matrices `U, W` with
  `U · W = 1` (coordinates are unique by linear independence), so
  `U ∈ GL(r,ℤ)` and the second presentation is literally a `rebase`
  of the first — up to the `Fin`-cast along `r = r'` (both ranks are
  `b₁`, by `r_eq_b1`).
* **Energy transports variationally** (`energy_reindex`): both
  energies are the least element of the *same* set of realizing
  cochain energies (`ofCycles_energy_isLeast`), so they are equal by
  `IsLeast.unique` — no matrix-inverse reindexing anywhere.
* **The partition function does not see the presentation**
  (`partFn_welldef`): reindex the Boltzmann sum along the rank
  equality, transport each term variationally, and finish with the
  Phase-23 `rebase_partFn`.

The graph-level readout: `IncidenceGraph.partFn`, with
`IntegralCyclePresentation.partFn_eq` saying every presentation
computes it. -/

namespace Meno

open scoped BigOperators
open Matrix

universe u v

variable {G : IncidenceGraph.{u, v}}

private lemma cast_dotProduct {ι : Type*} [Fintype ι] (x y : ι → ℤ) :
    ((x ⬝ᵥ y : ℤ) : ℝ) = (fun e => (x e : ℝ)) ⬝ᵥ (fun e => (y e : ℝ)) := by
  show ((∑ e, x e * y e : ℤ) : ℝ) = ∑ e, (x e : ℝ) * (y e : ℝ)
  push_cast
  rfl

/-! ## Independence and unique coordinates -/

/-- A presentation's cycles are `ℝ`-linearly independent — the
topological basis field itself (review #4: independence is data of
`CycleBasis`, not a consequence of the Gram). -/
theorem CyclePresentation.cycles_independent (P : CyclePresentation G)
    (x : Fin P.r → ℝ)
    (hx : (fun e => ∑ i, x i * P.cycles i e) = 0) : x = 0 :=
  P.independent x hx

namespace IntegralCyclePresentation

variable (Q : IntegralCyclePresentation G)

/-- The integer basis vectors are cycles. -/
theorem cyclesZ_mem (j : Fin Q.r) : Q.cyclesZ j ∈ G.cycleLattice := by
  rw [IncidenceGraph.mem_cycleLattice]
  intro v
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_zero, ← G.boundary_castR]
  rw [show (fun e => ((Q.cyclesZ j e : ℤ) : ℝ)) = Q.cycles j from
    funext fun e => Q.cyclesZ_cast j e]
  exact Q.cycles_closed j v

/-- Integer coordinates are unique. -/
theorem coords_unique {a b : Fin Q.r → ℤ}
    (h : (fun e => ∑ i, a i * Q.cyclesZ i e)
      = fun e => ∑ i, b i * Q.cyclesZ i e) : a = b := by
  have hcast : (fun e => ∑ i, ((a i - b i : ℤ) : ℝ) * Q.cycles i e) = 0 := by
    funext e
    show ∑ i, ((a i - b i : ℤ) : ℝ) * Q.cycles i e = 0
    have he := congrFun h e
    have hcasteq : ((∑ i, a i * Q.cyclesZ i e : ℤ) : ℝ)
        = ((∑ i, b i * Q.cyclesZ i e : ℤ) : ℝ) := by rw [he]
    push_cast at hcasteq ⊢
    simp only [Q.cyclesZ_cast] at hcasteq
    have hsplit : ∑ i, ((a i : ℝ) - (b i : ℝ)) * Q.cycles i e
        = (∑ i, (a i : ℝ) * Q.cycles i e)
          - ∑ i, (b i : ℝ) * Q.cycles i e := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, hcasteq, sub_self]
  have := Q.toCyclePresentation.cycles_independent _ hcast
  funext i
  have hi := congrFun this i
  have : ((a i - b i : ℤ) : ℝ) = 0 := hi
  have : (a i - b i : ℤ) = 0 := by exact_mod_cast this
  omega

/-- **Primitivity is a theorem**: every integral cycle is an integer
combination of any presentation's basis. `periods_onto` supplies
unit-period realizers `τ⁽ⁱ⁾`; pairing with them shows the real
coordinates are the integers `⟨τ⁽ⁱ⁾, x⟩`. -/
theorem exists_int_coords {x : G.E → ℤ} (hx : x ∈ G.cycleLattice) :
    ∃ a : Fin Q.r → ℤ, x = fun e => ∑ i, a i * Q.cyclesZ i e := by
  have hclosed : ∀ v, G.boundary (fun e => ((x e : ℤ) : ℝ)) v = 0 := by
    intro v
    rw [G.boundary_castR, (G.mem_cycleLattice.mp hx) v, Int.cast_zero]
  obtain ⟨aR, haR⟩ := Q.spanning (fun e => ((x e : ℤ) : ℝ)) hclosed
  choose τ hτ using Q.periods_onto
  refine ⟨fun i => τ (Pi.single i 1) ⬝ᵥ x, ?_⟩
  have key : ∀ i, aR i = ((τ (Pi.single i 1) ⬝ᵥ x : ℤ) : ℝ) := by
    intro i
    have hchain : (fun e => ((τ (Pi.single i 1) e : ℤ) : ℝ))
        ⬝ᵥ (fun e => ∑ j, aR j * Q.cycles j e) = aR i := by
      calc (fun e => ((τ (Pi.single i 1) e : ℤ) : ℝ))
          ⬝ᵥ (fun e => ∑ j, aR j * Q.cycles j e)
          = ∑ e, ((τ (Pi.single i 1) e : ℤ) : ℝ)
              * ∑ j, aR j * Q.cycles j e := rfl
        _ = ∑ j, aR j * ∑ e, ((τ (Pi.single i 1) e : ℤ) : ℝ)
              * Q.cycles j e := by
            calc ∑ e, ((τ (Pi.single i 1) e : ℤ) : ℝ)
                  * ∑ j, aR j * Q.cycles j e
                = ∑ e, ∑ j, aR j * (((τ (Pi.single i 1) e : ℤ) : ℝ)
                    * Q.cycles j e) := by
                  refine Finset.sum_congr rfl fun e _ => ?_
                  rw [Finset.mul_sum]
                  exact Finset.sum_congr rfl fun j _ => by ring
              _ = ∑ j, ∑ e, aR j * (((τ (Pi.single i 1) e : ℤ) : ℝ)
                    * Q.cycles j e) := Finset.sum_comm
              _ = ∑ j, aR j * ∑ e, ((τ (Pi.single i 1) e : ℤ) : ℝ)
                    * Q.cycles j e := by
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [Finset.mul_sum]
        _ = ∑ j, aR j * (Pi.single i (1 : ℝ) : Fin Q.r → ℝ) j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            congr 1
            have h1 : (∑ e, ((τ (Pi.single i 1) e : ℤ) : ℝ) * Q.cycles j e)
                = ((τ (Pi.single i 1) ⬝ᵥ Q.cyclesZ j : ℤ) : ℝ) := by
              rw [cast_dotProduct]
              refine Finset.sum_congr rfl fun e _ => ?_
              show ((τ (Pi.single i 1) e : ℤ) : ℝ) * Q.cycles j e
                = ((τ (Pi.single i 1) e : ℤ) : ℝ) * ((Q.cyclesZ j e : ℤ) : ℝ)
              rw [Q.cyclesZ_cast]
            rw [h1, hτ (Pi.single i 1) j]
            exact IncidenceGraph.cast_single i j
        _ = aR i := by
            rw [show (fun j => aR j * (Pi.single i (1 : ℝ) : Fin Q.r → ℝ) j)
                = fun j => if j = i then aR j else 0 from funext fun j => by
              rcases eq_or_ne j i with h | h
              · subst h
                rw [if_pos rfl, Pi.single_eq_same, mul_one]
              · rw [if_neg h, Pi.single_eq_of_ne h, mul_zero]]
            rw [Finset.sum_ite_eq' Finset.univ i aR]
            simp
    rw [cast_dotProduct, show (fun e => ((x e : ℤ) : ℝ))
        = fun e => ∑ j, aR j * Q.cycles j e from haR, hchain]
  funext e
  apply Int.cast_injective (α := ℝ)
  have hxe := congrFun haR e
  rw [hxe]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← key i, Q.cyclesZ_cast]

/-! ## Unimodular relatedness -/

/-- **C3's acceptance**: any two integral presentations of the same
graph are related by a unimodular change of basis — the second is a
`rebase` of the first, up to the `Fin`-cast along the rank equality. -/
theorem exists_rebase_related (P P' : IntegralCyclePresentation G) :
    ∃ (U : Matrix (Fin P.r) (Fin P.r) ℤ) (hU : IsUnit U.det),
      ∀ (i : Fin P.r) (e : G.E),
        P'.cycles (Fin.cast (P.r_eq_b1.trans P'.r_eq_b1.symm) i) e
          = (P.toCyclePresentation.rebase U hU).cycles i e := by
  have hr : P.r = P'.r := P.r_eq_b1.trans P'.r_eq_b1.symm
  choose Uf hUf using fun i : Fin P.r =>
    P.exists_int_coords (P'.cyclesZ_mem (Fin.cast hr i))
  choose Wf hWf using fun j : Fin P.r =>
    P'.exists_int_coords (P.cyclesZ_mem j)
  have hUW : ∀ i : Fin P.r,
      (fun l => ∑ j, Uf i j * Wf j l)
        = (Pi.single (Fin.cast hr i) 1 : Fin P'.r → ℤ) := by
    intro i
    apply P'.coords_unique
    funext e
    calc ∑ l, (∑ j, Uf i j * Wf j l) * P'.cyclesZ l e
        = ∑ l, ∑ j, Uf i j * (Wf j l * P'.cyclesZ l e) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j, ∑ l, Uf i j * (Wf j l * P'.cyclesZ l e) := Finset.sum_comm
      _ = ∑ j, Uf i j * ∑ l, Wf j l * P'.cyclesZ l e := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ j, Uf i j * P.cyclesZ j e := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← congrFun (hWf j) e]
      _ = P'.cyclesZ (Fin.cast hr i) e := (congrFun (hUf i) e).symm
      _ = ∑ l, (Pi.single (Fin.cast hr i) 1 : Fin P'.r → ℤ) l
            * P'.cyclesZ l e := by
          rw [show (fun l => (Pi.single (Fin.cast hr i) 1 : Fin P'.r → ℤ) l
              * P'.cyclesZ l e)
              = fun l => if l = Fin.cast hr i then P'.cyclesZ l e else 0 from
            funext fun l => by
              rcases eq_or_ne l (Fin.cast hr i) with h | h
              · subst h
                rw [if_pos rfl, Pi.single_eq_same, one_mul]
              · rw [if_neg h, Pi.single_eq_of_ne h, zero_mul]]
          rw [Finset.sum_ite_eq' Finset.univ (Fin.cast hr i)
            (fun l => P'.cyclesZ l e)]
          simp
  set U : Matrix (Fin P.r) (Fin P.r) ℤ := Matrix.of fun i j => Uf i j with hU
  set W : Matrix (Fin P.r) (Fin P.r) ℤ :=
    Matrix.of fun j i => Wf j (Fin.cast hr i) with hW
  have hUWone : U * W = 1 := by
    ext i i'
    show ∑ j, Uf i j * Wf j (Fin.cast hr i') = (1 : Matrix _ _ ℤ) i i'
    have := congrFun (hUW i) (Fin.cast hr i')
    rw [this]
    rw [Matrix.one_apply]
    rcases eq_or_ne i' i with h | h
    · subst h
      rw [Pi.single_eq_same, if_pos rfl]
    · rw [Pi.single_eq_of_ne (fun hc => h (Fin.ext (by
        have := congrArg Fin.val hc
        simpa using this))), if_neg (Ne.symm h)]
  have hUdet : IsUnit U.det := by
    have hdet := congrArg Matrix.det hUWone
    rw [Matrix.det_mul, Matrix.det_one] at hdet
    exact IsUnit.of_mul_eq_one _ hdet
  refine ⟨U, hUdet, fun i e => ?_⟩
  show P'.cycles (Fin.cast hr i) e = ∑ j, (U i j : ℝ) * P.cycles j e
  rw [← P'.cyclesZ_cast, congrFun (hUf i) e]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [P.cyclesZ_cast]
  rfl

/-! ## Energy and partition function transport -/

/-- Energies transport variationally across equal cycle families:
both are the least element of the same set of realizing energies. -/
theorem energy_reindex (P P' : IntegralCyclePresentation G)
    (hr : P.r = P'.r)
    (U : Matrix (Fin P.r) (Fin P.r) ℤ) (hU : IsUnit U.det)
    (hcyc : ∀ i e, P'.cycles (Fin.cast hr i) e
      = (P.toCyclePresentation.rebase U hU).cycles i e)
    (k : Fin P'.r → ℤ) :
    P'.toGramData.energy k
      = (P.toCyclePresentation.rebase U hU).toGramData.energy
          (fun i => k (Fin.cast hr i)) := by
  have h1 := HarmonicGramData.ofCycles_energy_isLeast (V := G.V)
    P'.cycles P'.gram_posDef k
  have h2 := HarmonicGramData.ofCycles_energy_isLeast (V := G.V)
    (P.toCyclePresentation.rebase U hU).cycles
    (P.toCyclePresentation.rebase U hU).gram_posDef
    (fun i => k (Fin.cast hr i))
  have hset : {E : ℝ | ∃ ω : G.E → ℝ,
      (∀ j, ω ⬝ᵥ (P.toCyclePresentation.rebase U hU).cycles j
        = ((fun i => k (Fin.cast hr i)) j : ℝ)) ∧ E = ω ⬝ᵥ ω}
      = {E : ℝ | ∃ ω : G.E → ℝ,
      (∀ j, ω ⬝ᵥ P'.cycles j = (k j : ℝ)) ∧ E = ω ⬝ᵥ ω} := by
    ext E
    constructor
    · rintro ⟨ω, hper, rfl⟩
      refine ⟨ω, fun j => ?_, rfl⟩
      have hj : Fin.cast hr (Fin.cast hr.symm j) = j := Fin.ext rfl
      have hthis : ω ⬝ᵥ (P.toCyclePresentation.rebase U hU).cycles
          (Fin.cast hr.symm j)
          = ((k (Fin.cast hr (Fin.cast hr.symm j)) : ℤ) : ℝ) :=
        hper (Fin.cast hr.symm j)
      rw [hj] at hthis
      rw [show (P.toCyclePresentation.rebase U hU).cycles (Fin.cast hr.symm j)
          = P'.cycles j from funext fun e => by
        rw [← hcyc (Fin.cast hr.symm j) e, hj]] at hthis
      exact hthis
    · rintro ⟨ω, hper, rfl⟩
      refine ⟨ω, fun i => ?_, rfl⟩
      show ω ⬝ᵥ (P.toCyclePresentation.rebase U hU).cycles i
        = ((k (Fin.cast hr i) : ℤ) : ℝ)
      rw [show (P.toCyclePresentation.rebase U hU).cycles i
          = P'.cycles (Fin.cast hr i) from funext fun e => (hcyc i e).symm]
      exact hper (Fin.cast hr i)
  rw [hset] at h2
  exact h1.unique h2

/-- **The partition function does not see the presentation.** -/
theorem partFn_welldef (P P' : IntegralCyclePresentation G) :
    P'.toGramData.toQuadraticAction.toSectorAction.partFn
      = P.toGramData.toQuadraticAction.toSectorAction.partFn := by
  obtain ⟨U, hU, hcyc⟩ := exists_rebase_related P P'
  have hr : P.r = P'.r := P.r_eq_b1.trans P'.r_eq_b1.symm
  rw [← P.toCyclePresentation.rebase_partFn U hU]
  show (∑' k : Fin P'.r → ℤ, Real.exp (-(P'.toGramData.energy k)))
    = ∑' k : Fin P.r → ℤ,
        Real.exp (-((P.toCyclePresentation.rebase U hU).toGramData.energy k))
  rw [← Equiv.tsum_eq (Equiv.arrowCongr (finCongr hr) (Equiv.refl ℤ))
    (fun k => Real.exp (-(P'.toGramData.energy k)))]
  refine tsum_congr fun k => ?_
  have hk : (fun i => ((Equiv.arrowCongr (finCongr hr) (Equiv.refl ℤ)) k)
      (Fin.cast hr i)) = k := by
    funext i
    show k ((finCongr hr).symm (Fin.cast hr i)) = k i
    exact congrArg k (Fin.ext rfl)
  rw [energy_reindex P P' hr U hU hcyc
    ((Equiv.arrowCongr (finCongr hr) (Equiv.refl ℤ)) k)]
  exact congrArg (fun t =>
    Real.exp (-(P.toCyclePresentation.rebase U hU).toGramData.energy t)) hk

end IntegralCyclePresentation

/-- **The partition function of the graph** — computed through the
fundamental presentation; every presentation agrees
(`IntegralCyclePresentation.partFn_eq`). -/
noncomputable def IncidenceGraph.partFn (G : IncidenceGraph.{u, v}) : ℝ :=
  G.fundamentalPresentation.toGramData.toQuadraticAction.toSectorAction.partFn

/-- Every integral presentation computes the graph's partition
function: the physics is a function of the graph alone. -/
theorem IntegralCyclePresentation.partFn_eq
    (Q : IntegralCyclePresentation G) :
    Q.toGramData.toQuadraticAction.toSectorAction.partFn = G.partFn :=
  IntegralCyclePresentation.partFn_welldef G.fundamentalPresentation Q

end Meno
