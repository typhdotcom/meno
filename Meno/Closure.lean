import Meno.Symmetry

/-! # Closure: when a coarse observation has a one-valued successor

A step `r : W → W' → Prop` (deterministic or not) is **closed** over
observations `π : W → O`, `π' : W' → O'` when the successor's
observation is a function of the current observation
(`StepClosed`): every successor of every state in the fiber over `o`
lands in the one fiber over `g o`. The fiberwise form is
`stepClosed_iff`; on a surjective observation of a total step the
successor map is unique (`StepClosed.unique`).

On the carrier, fine states are cochains and the observation is the
class map. The face's anchors:

* **The exact law** (`noisyStep_closed_iff`): linear dynamics `f`
  followed by additive error from `S ∋ 0` has a one-valued class step
  **iff** `f` carries gauge into gauge and every error is pure gauge.
* **The symmetry instance** (`Auto.stepClosed`): an automorphism's
  pullback is closed on classes at every coefficient ring.
* **The edge law** (`edgeNoise_closed_iff`): single-edge error at `e`
  is closed iff the indicator of `e` is exact.
* **The strictness witness** (`cycle_edgeNoise_not_closed`): on `C_n`
  at any resolution `q > 1`, single-edge error at any edge is not
  closed — on a graph the class has error distance one.
* **The boundary witness** (`bridge_edgeNoise_closed`): on the
  one-edge graph, single-edge error is closed.

What the closed step forgets is priced by the ratchet: the fiber of
the class map is the gauge group (`card_fiber`), so recovering a
representative costs `log |gauge|` (`recoveryCost_compression`). -/

namespace Meno

universe u v w x

/-! ## Closed steps -/

section Step

variable {W : Type u} {W' : Type v} {O : Type w} {O' : Type x}

/-- **A closed step**: the observation of every successor is a
function of the current observation. -/
def StepClosed (r : W → W' → Prop) (π : W → O) (π' : W' → O') : Prop :=
  ∃ g : O → O', ∀ a a', r a a' → π' a' = g (π a)

/-- **The fiberwise form**: a step is closed iff any two successors of
any two states in one fiber lie in one fiber. -/
theorem stepClosed_iff [Nonempty O'] (r : W → W' → Prop) (π : W → O)
    (π' : W' → O') :
    StepClosed r π π' ↔ ∀ a₁ a₂ a₁' a₂', π a₁ = π a₂ →
      r a₁ a₁' → r a₂ a₂' → π' a₁' = π' a₂' := by
  classical
  constructor
  · rintro ⟨g, hg⟩ a₁ a₂ a₁' a₂' hπ h₁ h₂
    rw [hg _ _ h₁, hg _ _ h₂, hπ]
  · intro h
    refine ⟨fun o => if hex : ∃ p : W × W', π p.1 = o ∧ r p.1 p.2
      then π' hex.choose.2 else Classical.arbitrary O', ?_⟩
    intro a a' hr
    have hex : ∃ p : W × W', π p.1 = π a ∧ r p.1 p.2 := ⟨(a, a'), rfl, hr⟩
    dsimp only
    rw [dif_pos hex]
    exact h _ _ _ _ hex.choose_spec.1.symm hr hex.choose_spec.2

/-- **The successor is unique**: on a surjective observation of a step
every state of which has a successor, two successor maps agree. -/
theorem StepClosed.unique {r : W → W' → Prop} {π : W → O} {π' : W' → O'}
    (hπ : Function.Surjective π) (htot : ∀ a, ∃ a', r a a')
    {g₁ g₂ : O → O'} (h₁ : ∀ a a', r a a' → π' a' = g₁ (π a))
    (h₂ : ∀ a a', r a a' → π' a' = g₂ (π a)) : g₁ = g₂ := by
  funext o
  obtain ⟨a, rfl⟩ := hπ o
  obtain ⟨a', ha'⟩ := htot a
  rw [← h₁ _ _ ha', h₂ _ _ ha']

end Step

/-! ## The exact law for noisy linear steps -/

section Linear

variable {R : Type*} {M : Type*} {M' : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

/-- **A noisy linear step**: linear dynamics `f` followed by an
additive error drawn from `S`. -/
def noisyStep (f : M →ₗ[R] M') (S : Set M') (a : M) (a' : M') : Prop :=
  ∃ s ∈ S, a' = f a + s

/-- **THE CLOSURE LAW**: with the errorless step allowed, a noisy linear
step has a one-valued step on quotients iff the dynamics carries `N`
into `N'` and every error lies in `N'`. -/
theorem noisyStep_closed_iff (f : M →ₗ[R] M') (N : Submodule R M)
    (N' : Submodule R M') (S : Set M') (h0 : (0 : M') ∈ S) :
    StepClosed (noisyStep f S) N.mkQ N'.mkQ ↔ N ≤ N'.comap f ∧ S ⊆ N' := by
  constructor
  · rintro ⟨g, hg⟩
    have key : ∀ a, ∀ s ∈ S, (Submodule.Quotient.mk (f a + s) : M' ⧸ N')
        = g (Submodule.Quotient.mk a) :=
      fun a s hs => hg a _ ⟨s, hs, rfl⟩
    have hg0 : g 0 = 0 := by
      have := key 0 0 h0
      rw [map_zero, add_zero, Submodule.Quotient.mk_zero,
        Submodule.Quotient.mk_zero] at this
      exact this.symm
    refine ⟨fun a ha => ?_, fun s hs => ?_⟩
    · have := key a 0 h0
      rw [add_zero, (Submodule.Quotient.mk_eq_zero N).mpr ha, hg0] at this
      exact (Submodule.Quotient.mk_eq_zero N').mp this
    · have := key 0 s hs
      rw [map_zero, zero_add, Submodule.Quotient.mk_zero, hg0] at this
      exact (Submodule.Quotient.mk_eq_zero N').mp this
  · rintro ⟨hN, hS⟩
    refine ⟨N.mapQ N' f hN, ?_⟩
    rintro a _ ⟨s, hs, rfl⟩
    simp [(Submodule.Quotient.mk_eq_zero N').mpr (hS hs)]

/-- **The errorless law**: linear dynamics has a one-valued step on
quotients iff it carries `N` into `N'`. -/
theorem linearStep_closed_iff (f : M →ₗ[R] M') (N : Submodule R M)
    (N' : Submodule R M') :
    StepClosed (fun a a' => a' = f a) N.mkQ N'.mkQ ↔ N ≤ N'.comap f := by
  have hr : (fun a a' => a' = f a) = noisyStep f {0} := by
    funext a a'
    simp [noisyStep]
  rw [hr, noisyStep_closed_iff f N N' {0} rfl]
  simp

end Linear

/-! ## On the carrier -/

namespace IncidenceGraph

variable {G : IncidenceGraph.{u}} (R : Type*) [CommRing R]

/-- **The symmetry instance**: an automorphism's pullback has a
one-valued step on classes. -/
theorem Auto.stepClosed (φ : G.Auto) :
    StepClosed (fun ω ω' => ω' = φ.cochainMap R ω)
      (LinearMap.range (G.gradLin R)).mkQ
      (LinearMap.range (G.gradLin R)).mkQ :=
  (linearStep_closed_iff _ _ _).mpr (by
    rintro ω ⟨f, rfl⟩
    exact Submodule.mem_comap.mpr
      ⟨fun v => f (φ.vertexEquiv v), (φ.cochainMap_grad R f).symm⟩)

variable (G)

/-- **The noise law on the carrier**: under additive cochain error from
`S ∋ 0`, the class step is one-valued iff every error is exact. -/
theorem cochainNoise_closed_iff (S : Set (G.E → R)) (h0 : (0 : G.E → R) ∈ S) :
    StepClosed (noisyStep (LinearMap.id (R := R)) S)
      (LinearMap.range (G.gradLin R)).mkQ
      (LinearMap.range (G.gradLin R)).mkQ ↔
      S ⊆ LinearMap.range (G.gradLin R) := by
  rw [noisyStep_closed_iff _ _ _ S h0]
  exact and_iff_right fun _ h => h

/-- **The edge law**: single-edge error at `e` is closed on classes iff
the indicator of `e` is exact. -/
theorem edgeNoise_closed_iff (e : G.E) :
    StepClosed (noisyStep (LinearMap.id (R := R)) {0, Pi.single e 1})
      (LinearMap.range (G.gradLin R)).mkQ
      (LinearMap.range (G.gradLin R)).mkQ ↔
      Pi.single e 1 ∈ LinearMap.range (G.gradLin R) := by
  rw [cochainNoise_closed_iff G R _ (Set.mem_insert _ _)]
  constructor
  · exact fun h => h (Set.mem_insert_of_mem _ rfl)
  · rintro h s (rfl | rfl)
    · exact Submodule.zero_mem _
    · exact h

end IncidenceGraph

/-! ## The witnesses -/

/-- **No edge of `C_n` is exact at resolution `q > 1`**: a gradient
has winding `0`, an edge indicator has winding `1`. -/
theorem cycle_single_not_exact (n q : ℕ) (hn : 0 < n) [NeZero q] (hq : 1 < q)
    (e : Fin n) :
    Pi.single e 1 ∉ LinearMap.range ((cycleGraph n hn).gradLin (ZMod q)) := by
  have : Fact (1 < q) := ⟨hq⟩
  intro hex
  have h0 := (Submodule.Quotient.mk_eq_zero _).mpr hex
  have hw := congrArg (fun ξ => (cycleGraph n hn).latticeQuotEquivQ
    (cycleLatticeBasis n hn) q ξ 0) h0
  simp only [map_zero, Pi.zero_apply] at hw
  rw [cycle_latticeQuotEquivQ_mk, Finset.sum_pi_single'] at hw
  simp at hw

/-- **THE STRICTNESS WITNESS**: on `C_n` at resolution `q > 1`,
single-edge error at any edge has no one-valued class step. -/
theorem cycle_edgeNoise_not_closed (n q : ℕ) (hn : 0 < n) [NeZero q]
    (hq : 1 < q) (e : Fin n) :
    ¬ StepClosed (noisyStep (LinearMap.id (R := ZMod q)) {0, Pi.single e 1})
      (LinearMap.range ((cycleGraph n hn).gradLin (ZMod q))).mkQ
      (LinearMap.range ((cycleGraph n hn).gradLin (ZMod q))).mkQ :=
  fun h => cycle_single_not_exact n q hn hq e
    ((IncidenceGraph.edgeNoise_closed_iff (cycleGraph n hn) (ZMod q) e).mp h)

/-- The one-edge graph: two vertices, one edge `0 → 1`. -/
@[reducible] def bridgeGraph : IncidenceGraph :=
  { V := Fin 2
    E := Unit
    src := fun _ => 0
    tgt := fun _ => 1 }

/-- **THE BOUNDARY WITNESS**: on the one-edge graph, single-edge error
is closed on classes at every coefficient ring — the edge is a bridge,
its indicator the gradient of a vertex indicator. -/
theorem bridge_edgeNoise_closed (R : Type*) [CommRing R] :
    StepClosed (noisyStep (LinearMap.id (R := R)) {0, Pi.single () 1})
      (LinearMap.range (bridgeGraph.gradLin R)).mkQ
      (LinearMap.range (bridgeGraph.gradLin R)).mkQ := by
  refine (IncidenceGraph.edgeNoise_closed_iff bridgeGraph R ()).mpr
    ⟨Pi.single 1 1, funext fun _ => ?_⟩
  show (Pi.single 1 1 : Fin 2 → R) 1 - (Pi.single 1 1 : Fin 2 → R) 0 = 1
  simp

end Meno
