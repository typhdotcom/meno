import Meno.ThetaHarmonic
import Meno.ThetaBinding
import Meno.CycleHarmonic
import Meno.WedgePresentation
import Meno.UniformAction
import Meno.Groupoid

/-! # The statement-coverage bundle (reviews #18, #19, #29)

**Coverage as a Lean object.** `MenoStatementCoverage` is derived
from Part I — by hand, one field per acceptance signature, verified
at review: every Part-I acceptance signature of
C1–C10 appears as a field in exactly one law package —

* `GraphTopologyLaws` (C1–C2): gauge, Euler, the fundamental basis,
  the ℤ/ℝ keystones, period surjectivity, integral potentials,
  exactness, independence, spanning, integral coordinates;
* `HarmonicCarrierLaws` (C3–C4): rank well-definedness, unimodular
  transport, the graph partition function, the variational identity,
  chart independence, positive energy;
* `MatterBindingLaws` (C6–C7): mass positivity/leastness/charts, the
  trapped paradox, annihilation, existence, the restriction image,
  attached rank, the kill theorem, exact surviving energies, the
  exact spectral decomposition, strict weight loss;
* `ResolutionCodingLaws` (C8–C9 on the graph; review #21 split):
  K1–K3, gauge counting, compression sections/costs, recovery;
* `CodingGravityLaws` (C8–C9 generic, graph-free; review #21 split):
  section counting, the coding theorem with its `ℝ≥0∞` boundary, and
  the gravity/time laws — the gravity theorem
  `SectorAction.complexity_gravity` with counting gravity as its
  zero-energy corollary (review #25);
* `ThermalDualityLaws`, `InformationLaws`, `ResolutionTowerLaws`
  (C9/C12 analytic, information, and resolution spines — defined in
  this file, across the certificate boundary, since review #29);
* `FlagshipLaws` (C5 + consumers): the concrete cycle, wedge, theta,
  binding, and geodesic results.

`menoStatementCoverage` is the **one derivation**, by direct
named-theorem assignment only.

**Scope** (reviews #19, #29). The bundle enforces
**statement coverage**: every acceptance signature is a field, so
deleting an underlying theorem breaks the derivation as written.
Proof **provenance** — that each field is proved by the named engine
rather than an independently replayed proof — is enforced by this
file's direct-assignment discipline, module boundaries, and
substantive review; Lean's kernel does not distinguish routes.
Repository invariants are outside the kernel entirely: C11's
deletion state and C12's import-DAG and no-duplication constraints
are facts about the source tree. Closure is the five-leg
conjunction, and the kernel carries one leg — this coverage bundle
compiles; the others are the import DAG matching Part I, the
recorded deletions holding, `lake build Meno` green with zero
`sorry`/`axiom`/warnings, and substantive source review finding the
derivation routes direct.
-/

namespace Meno

universe u v w

/-! ## The three spine law packages (reviews #18, #29)

`ThermalDualityLaws`, `InformationLaws`, and `ResolutionTowerLaws`
bundle the thermal, information, and resolution-tower spines, one
`Prop` package per subject, each with one derivation. Review #29
moved them across the certificate boundary into this file: a law
package assembles model theorems for acceptance and is never a
model consumer of them — every theorem a package bundles must earn
its place in the tree through a public claim or a model reader. -/

namespace QuadLatticeAction

/-- **The thermal-duality laws** of a bundled lattice action
(review #18): the scale algebra, the scaling of the discriminant,
equivalence invariance of the scaled moments, the dual involution,
the inversion of temperature through the dual, and the partition,
mean-energy, and variance functional equations with the self-dual
fixed point. -/
structure ThermalDualityLaws (Q : QuadLatticeAction.{u}) : Prop where
  scale_one : Q.scale 1 one_pos = Q
  scale_scale : ∀ (β β' : ℝ) (hβ : 0 < β) (hβ' : 0 < β'),
    (Q.scale β hβ).scale β' hβ' = Q.scale (β' * β) (mul_pos hβ' hβ)
  disc_scale : ∀ (β : ℝ) (hβ : 0 < β),
    (Q.scale β hβ).disc = β ^ Q.rank * Q.disc
  moments_equiv : ∀ {Q' : QuadLatticeAction.{u}}, Q.Equiv Q' →
    ∀ β : ℝ,
    Q'.scaledPartFn β = Q.scaledPartFn β
      ∧ Q'.scaledMoment β = Q.scaledMoment β
      ∧ Q'.scaledMoment2 β = Q.scaledMoment2 β
      ∧ Q'.meanEnergy = Q.meanEnergy
  dual_involution : ∀ x y : Q.Λ,
    Q.dual.dual.form (Module.evalEquiv ℤ Q.Λ x)
        (Module.evalEquiv ℤ Q.Λ y)
      = Q.form x y
  scale_dual : ∀ (β : ℝ) (hβ : 0 < β),
    (Q.scale β hβ).dual = Q.dual.scale β⁻¹ (inv_pos.mpr hβ)
  partFn_equation : ∀ (β : ℝ), 0 < β →
    Q.dual.scaledPartFn β⁻¹
      = (β ^ Q.rank * Q.disc / Real.pi ^ Q.rank) ^ ((1 : ℝ) / 2)
        * Q.scaledPartFn β
  mean_equation : ∀ (β : ℝ), 0 < β →
    Q.meanEnergy β + β⁻¹ ^ 2 * Q.dual.meanEnergy β⁻¹
      = Q.rank / (2 * β)
  variance_equation : ∀ (β : ℝ) (hβ : 0 < β),
    (Q.scaledSector β hβ).gibbsVariance (fun a => Q.form a a)
      + 2 * β⁻¹ ^ 3 * Q.dual.meanEnergy β⁻¹
      - β⁻¹ ^ 4 * ((Q.dual.scaledSector β⁻¹
          (inv_pos.mpr hβ)).gibbsVariance (fun φ => Q.dual.form φ φ))
      = Q.rank / (2 * β ^ 2)
  selfDual_fixed : Nonempty (Q.Equiv Q.dual) →
    Q.meanEnergy 1 = Q.rank / 4

/-- **Every bundled lattice action satisfies the thermal-duality
laws** (review #18) — one derivation, assembled from the proved
engine. -/
theorem thermalDualityLaws (Q : QuadLatticeAction.{u}) :
    ThermalDualityLaws Q where
  scale_one := Q.scale_one
  scale_scale := fun β β' hβ hβ' => Q.scale_scale β β' hβ hβ'
  disc_scale := fun β hβ => Q.disc_scale β hβ
  moments_equiv := fun e β =>
    ⟨e.scaledPartFn_eq β, e.scaledMoment_eq β, e.scaledMoment2_eq β,
      e.meanEnergy_eq⟩
  dual_involution := fun x y => Q.dual_dual x y
  scale_dual := fun β hβ => Q.scale_dual β hβ
  partFn_equation := fun β hβ => Q.scaled_duality β hβ
  mean_equation := fun β hβ => Q.meanEnergy_T_dual β hβ
  variance_equation := fun β hβ => Q.gibbsVariance_T_dual β hβ
  selfDual_fixed := fun ⟨e⟩ => Q.meanEnergy_self_dual e

end QuadLatticeAction

namespace FinDist

/-- **The information laws** of a finite distribution (review #18):
pushforward functoriality, the unconditional entropy chain rule with
its conditional corollaries, the support-aware Gibbs inequality with
its characterization, and data processing. -/
structure InformationLaws {X : Type u} [Fintype X] [DecidableEq X]
    (P : FinDist X) : Prop where
  map_id : P.map id = P
  map_comp : ∀ {D E : Type u} [Fintype D] [Fintype E] [DecidableEq D]
    [DecidableEq E] (f : X → D) (g : D → E),
    P.map (g ∘ f) = (P.map f).map g
  entropy_chain : ∀ {D : Type u} [Fintype D] [DecidableEq D]
    (f : X → D), P.entropy = (P.map f).entropy + P.condEntropy f
  condEntropy_id : P.condEntropy id = 0
  condEntropy_comp : ∀ {D E : Type u} [Fintype D] [Fintype E]
    [DecidableEq D] [DecidableEq E] (f : X → D) (g : D → E),
    P.condEntropy (g ∘ f) = P.condEntropy f + (P.map f).condEntropy g
  relEntropy_nonneg : ∀ (Q : FinDist X) (hQ : Q.FullSupport),
    0 ≤ P.relativeEntropy Q hQ
  relEntropy_eq_zero_iff : ∀ (Q : FinDist X) (hQ : Q.FullSupport),
    P.relativeEntropy Q hQ = 0 ↔ P = Q
  dataProcessing : ∀ {D : Type u} [Fintype D] [DecidableEq D]
    (f : X → D) (hf : Function.Surjective f) (Q : FinDist X)
    (hQ : Q.FullSupport),
    (P.map f).relativeEntropy (Q.map f) (hQ.map f hf)
      ≤ P.relativeEntropy Q hQ

/-- **Every finite distribution satisfies the information laws**
(review #18) — one derivation, assembled from the proved engine. -/
theorem informationLaws {X : Type u} [Fintype X] [DecidableEq X]
    (P : FinDist X) : InformationLaws P where
  map_id := P.map_id
  map_comp := fun f g => map_comp f g P
  entropy_chain := fun f => entropy_eq_map_add_condEntropy f P
  condEntropy_id := P.condEntropy_id
  condEntropy_comp := fun f g => condEntropy_comp f g P
  relEntropy_nonneg := fun Q hQ => relativeEntropy_nonneg P Q hQ
  relEntropy_eq_zero_iff := fun Q hQ => relativeEntropy_eq_zero_iff P Q hQ
  dataProcessing := fun f hf Q hQ => relativeEntropy_map_le f hf P Q hQ

end FinDist

namespace IncidenceGraph

/-- **The resolution-tower laws** of a graph (review #18): the tower
maps form a category (identity, composition, surjectivity);
distributions and actions push forward, with the
identity and composition laws; the identity step has zero price and
zero cost; prices and costs add; deficits telescope and are
monotone; and genuine refinements are strictly priced. -/
structure ResolutionTowerLaws (G : IncidenceGraph.{u, v}) : Prop where
  map_id : ∀ (q : ℕ) [NeZero q],
    G.h1TowerMap q q dvd_rfl = LinearMap.id
  map_comp : ∀ (q q' q'' : ℕ) [NeZero q] [NeZero q'] [NeZero q'']
    (h₁ : q ∣ q') (h₂ : q' ∣ q''),
    (G.h1TowerMap q q' h₁).comp (G.h1TowerMap q' q'' h₂)
      = G.h1TowerMap q q'' (h₁.trans h₂)
  map_surjective : ∀ (q q' : ℕ) [NeZero q] [NeZero q'] (h : q ∣ q'),
    Function.Surjective (G.h1TowerMap q q' h)
  dist_push : ∀ (q q' : ℕ) [NeZero q] [NeZero q'] (h : q ∣ q'),
    (G.residueDist q').map (⇑(G.h1TowerMap q q' h)) = G.residueDist q
  dist_comp : ∀ (q q' q'' : ℕ) [NeZero q] [NeZero q'] [NeZero q'']
    (h₁ : q ∣ q') (h₂ : q' ∣ q''),
    ((G.residueDist q'').map (⇑(G.h1TowerMap q' q'' h₂))).map
        (⇑(G.h1TowerMap q q' h₁))
      = (G.residueDist q'').map (⇑(G.h1TowerMap q q'' (h₁.trans h₂)))
  action_push : ∀ (q q' : ℕ) [NeZero q] [NeZero q'] (h : q ∣ q'),
    (G.residueAction q').coarseGrain (⇑(G.h1TowerMap q q' h)) 0
        (G.residueAction_tower_weight_pos q q' h)
        (G.residueAction_tower_weight_le q q' h)
      = G.residueAction q
  action_comp : ∀ (q q' q'' : ℕ) [NeZero q] [NeZero q'] [NeZero q'']
    (h₁ : q ∣ q') (h₂ : q' ∣ q''),
    (G.residueAction q').coarseGrain (⇑(G.h1TowerMap q q' h₁)) 0
        (G.residueAction_tower_weight_pos q q' h₁)
        (G.residueAction_tower_weight_le q q' h₁)
      = (G.residueAction q'').coarseGrain
          (⇑(G.h1TowerMap q q'' (h₁.trans h₂))) 0
          (G.residueAction_tower_weight_pos q q'' (h₁.trans h₂))
          (G.residueAction_tower_weight_le q q'' (h₁.trans h₂))
  price_id : ∀ (q : ℕ) [NeZero q],
    (G.residueDist q).condEntropy (⇑(G.h1TowerMap q q dvd_rfl)) = 0
  cost_id : ∀ (q : ℕ) [NeZero q],
    sectionCost (⇑(G.h1TowerMap q q dvd_rfl)) = 0
  price_add : ∀ (q q' q'' : ℕ) [NeZero q] [NeZero q'] [NeZero q'']
    (h₁ : q ∣ q') (h₂ : q' ∣ q''),
    (G.residueDist q'').condEntropy
        (⇑(G.h1TowerMap q q'' (h₁.trans h₂)))
      = (G.residueDist q'').condEntropy (⇑(G.h1TowerMap q' q'' h₂))
        + (G.residueDist q').condEntropy (⇑(G.h1TowerMap q q' h₁))
  cost_add : ∀ (q q' q'' : ℕ) [NeZero q] [NeZero q'] [NeZero q'']
    (h₁ : q ∣ q') (h₂ : q' ∣ q''),
    sectionCost (⇑(G.h1TowerMap q q'' (h₁.trans h₂)))
        / Nat.card (H1Reduction G q)
      = sectionCost (⇑(G.h1TowerMap q' q'' h₂))
            / Nat.card (H1Reduction G q')
        + sectionCost (⇑(G.h1TowerMap q q' h₁))
            / Nat.card (H1Reduction G q)
  deficit_telescope : ∀ (q q' q'' c c' : ℕ) [NeZero q] [NeZero q']
    [NeZero q''] (h₁ : q ∣ q') (h₂ : q' ∣ q''),
    q' = c * q → q'' = c' * q' →
    (G.residueDist q'').condEntropy
        (⇑(G.h1TowerMap q q'' (h₁.trans h₂)))
      = G.b1 * Real.log ((c' * c : ℕ))
        - (G.residueDefect q'' - G.residueDefect q)
  deficit_mono : ∀ (q q' : ℕ) [NeZero q] [NeZero q'],
    q ∣ q' → G.residueDefect q ≤ G.residueDefect q'
  price_strict : ∀ (q q' c : ℕ) [NeZero q] [NeZero q'],
    0 < G.b1 → 1 < c → ∀ (hdvd : q ∣ q'), q' = c * q →
    0 < (G.residueDist q').condEntropy (⇑(G.h1TowerMap q q' hdvd))
      ∧ (G.residueDist q').condEntropy (⇑(G.h1TowerMap q q' hdvd))
          < G.b1 * Real.log c
      ∧ G.residueDefect q < G.residueDefect q'

/-- **Every graph satisfies the resolution-tower laws** (review #18)
— one derivation, assembled from the proved tower theorems. -/
theorem resolutionTowerLaws (G : IncidenceGraph.{u, v}) :
    ResolutionTowerLaws G where
  map_id := fun q _ => G.h1TowerMap_id q
  map_comp := fun q q' q'' _ _ _ h₁ h₂ =>
    G.h1TowerMap_comp q q' q'' h₁ h₂
  map_surjective := fun q q' _ _ h => G.h1TowerMap_surjective q q' h
  dist_push := fun q q' _ _ h => G.residueDist_tower q q' h
  dist_comp := fun q q' q'' _ _ _ h₁ h₂ =>
    G.residueDist_tower_trans q q' q'' h₁ h₂
  action_push := fun q q' _ _ h => G.residueAction_tower q q' h
  action_comp := fun q q' q'' _ _ _ h₁ h₂ =>
    G.residueAction_tower_trans q q' q'' h₁ h₂
  price_id := fun q _ => G.residue_tower_price_id q
  cost_id := fun q _ => G.sectionCost_h1TowerMap_id q
  price_add := fun q q' q'' _ _ _ h₁ h₂ =>
    G.residue_tower_condEntropy_trans q q' q'' h₁ h₂
  cost_add := fun q q' q'' _ _ _ h₁ h₂ =>
    G.sectionCost_h1TowerMap_trans q q' q'' h₁ h₂
  deficit_telescope := fun q q' q'' c c' _ _ _ h₁ h₂ hq' hq'' =>
    G.residue_tower_price_trans q q' q'' c c' h₁ h₂ hq' hq''
  deficit_mono := fun q q' _ _ h => G.residueDefect_mono q q' h
  price_strict := fun q q' c _ _ hb hc hdvd hq' =>
    G.residue_tower_price_strict q q' c hb hc hdvd hq'

end IncidenceGraph

/- `thetaGraph` is reducible, so its projections reduce to concrete
types in instance goals and the generic instances' graph
metavariable cannot be solved by unification — apply them by name
(review #14 pattern, `Meno/ThetaHarmonic.lean`). -/

noncomputable local instance :
    Fintype (IncidenceGraph.H1Reduction thetaGraph 2) :=
  thetaGraph.h1ReductionFintype 2

local instance : Nonempty (IncidenceGraph.H1Reduction thetaGraph 2) :=
  thetaGraph.h1ReductionNonempty 2

noncomputable local instance :
    Fintype (IncidenceGraph.H1Reduction thetaGraph 4) :=
  thetaGraph.h1ReductionFintype 4

noncomputable local instance :
    Fintype (IncidenceGraph.H1Reduction thetaGraph 8) :=
  thetaGraph.h1ReductionFintype 8

noncomputable local instance :
    DecidableEq (IncidenceGraph.H1Reduction thetaGraph 2) :=
  thetaGraph.h1ReductionDecEq 2

noncomputable local instance :
    DecidableEq (IncidenceGraph.H1Reduction thetaGraph 4) :=
  thetaGraph.h1ReductionDecEq 4

noncomputable local instance :
    Fintype (SGD.Pullback (thetaGraph.carrierCompression 2)
      (thetaGraph.carrierCompression 2)) :=
  thetaGraph.carrierPullbackFintype 2

local instance :
    Nonempty (SGD.Pullback (thetaGraph.carrierCompression 2)
      (thetaGraph.carrierCompression 2)) :=
  thetaGraph.carrierPullbackNonempty 2

/-! ## C1–C2: the topology laws -/

/-- **The graph-topology laws** (C1–C2): every Part-I acceptance
signature of the foundation and the intrinsic integral topology. -/
structure GraphTopologyLaws (G : IncidenceGraph.{u, v}) : Prop where
  gauge : Module.finrank ℝ (LinearMap.ker (G.gradLin ℝ))
    = G.componentCard
  euler : (G.b1 : ℤ)
    = (Fintype.card G.E : ℤ) - Fintype.card G.V + G.componentCard
  basis_exists : Nonempty (Module.Basis (Fin G.b1) ℤ G.cycleLattice)
  keystone_int :
    Nonempty (((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))
      ≃ₗ[ℤ] (Fin G.b1 → ℤ))
  keystone_real :
    Nonempty (((G.E → ℝ) ⧸ LinearMap.range (G.gradLin ℝ))
      ≃ₗ[ℝ] (Fin G.b1 → ℝ))
  cochainQuot_rank :
    Module.finrank ℝ ((G.E → ℝ) ⧸ LinearMap.range (G.gradLin ℝ))
      = G.b1
  cycle_rank : Module.finrank ℝ (LinearMap.ker (G.boundaryLin ℝ))
    = G.b1
  periods_onto : ∀ {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) (k : Fin n → ℤ),
    ∃ τ : G.E → ℤ, ∀ j, τ ⬝ᵥ G.cyclesZ B j = k j
  periodsR_onto : ∀ {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) (k : Fin n → ℝ),
    ∃ ω : G.E → ℝ, ∀ j, ω ⬝ᵥ G.cyclesR B j = k j
  integral_potentials : ∀ {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) (ω : G.E → ℤ),
    (∀ j, ω ⬝ᵥ G.cyclesZ B j = 0) → ∃ g : G.V → ℤ, G.grad g = ω
  exactness : ∀ {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) (ω : G.E → ℝ),
    (∀ i, ω ⬝ᵥ G.cyclesR B i = 0) ↔ ∃ f : G.V → ℝ, G.grad f = ω
  independence : ∀ {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) (x : Fin n → ℝ),
    (fun e => ∑ i, x i * G.cyclesR B i e) = 0 → x = 0
  spanning : ∀ {r : ℕ}, r = G.b1 → ∀ (c : Fin r → G.E → ℝ),
    (∀ i v, G.boundary (c i) v = 0) →
    (∀ x : Fin r → ℝ, (fun e => ∑ i, x i * c i e) = 0 → x = 0) →
    ∀ (ω : G.E → ℝ), (∀ v, G.boundary ω v = 0) →
    ∃ a : Fin r → ℝ, ω = fun e => ∑ i, a i * c i e
  int_coords : ∀ {r : ℕ} (c : Fin r → G.E → ℤ),
    (∀ ω : G.E → ℝ, (∀ v, G.boundary ω v = 0) →
      ∃ a : Fin r → ℝ, ω = fun e => ∑ i, a i * ((c i e : ℤ) : ℝ)) →
    (∀ k : Fin r → ℤ, ∃ τ : G.E → ℤ, ∀ j, τ ⬝ᵥ c j = k j) →
    ∀ {x : G.E → ℤ}, x ∈ G.cycleLattice →
    ∃ a : Fin r → ℤ, x = fun e => ∑ i, a i * c i e

/-- **Every graph satisfies the topology laws** — direct
assignments. -/
theorem graphTopologyLaws (G : IncidenceGraph.{u, v}) :
    GraphTopologyLaws G where
  gauge := G.finrank_gauge
  euler := G.b1_eq
  basis_exists := ⟨G.cycleBasis⟩
  keystone_int := ⟨G.h1QuotEquiv⟩
  keystone_real := ⟨G.cochainQuotEquivR⟩
  cochainQuot_rank := G.finrank_cochainQuotR
  cycle_rank := G.finrank_ker_boundaryLin
  periods_onto := G.periods_onto
  periodsR_onto := G.periodsR_onto
  integral_potentials := G.integral_potentials
  exactness := G.period_eq_zero_iff_exists_grad
  independence := G.cast_independent
  spanning := G.spanning_of_card_eq_b1
  int_coords := G.exists_int_coords

/-! ## C3–C4: the harmonic-carrier laws -/

/-- **The harmonic-carrier laws** (C3–C4): rank well-definedness,
unimodular basis transport, the basis-free partition function, the
variational identity, chart independence, and positive energy. -/
structure HarmonicCarrierLaws (G : IncidenceGraph.{u, v}) : Prop where
  rank_well_defined : ∀ {n : ℕ},
    Module.Basis (Fin n) ℤ G.cycleLattice → n = G.b1
  unimodular : ∀ {n : ℕ}
    (B B' : Module.Basis (Fin n) ℤ G.cycleLattice),
    ∃ U : Matrix (Fin n) (Fin n) ℤ, IsUnit U.det ∧
      ∀ j, G.cyclesZ B' j = fun e => ∑ i, U i j * G.cyclesZ B i e
  partFn_graph : ∀ {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice),
    (G.basisGramData B).toQuadraticAction.toSectorAction.partFn
      = G.partFn
  energy_least : ∀ κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ),
    IsLeast {E : ℝ | ∃ ω : G.E → ℝ,
        (∀ j, ω ⬝ᵥ G.fundCyclesR j = ((G.h1QuotEquiv κ j : ℤ) : ℝ))
          ∧ E = ω ⬝ᵥ ω}
      (G.harmonicEnergy κ)
  chart_energy : ∀ {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice) (τ : G.E → ℤ),
    (G.basisGramData B).energy (fun j => τ ⬝ᵥ G.cyclesZ B j)
      = G.harmonicEnergy (Submodule.Quotient.mk τ)
  energy_pos :
    ∀ {κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ)}, κ ≠ 0 →
    0 < G.harmonicEnergy κ

/-- **Every graph satisfies the harmonic-carrier laws** — direct
assignments. -/
theorem harmonicCarrierLaws (G : IncidenceGraph.{u, v}) :
    HarmonicCarrierLaws G where
  rank_well_defined := G.card_eq_b1
  unimodular := G.exists_unimodular_relating
  partFn_graph := G.basisGramData_partFn
  energy_least := G.harmonicEnergy_isLeast
  chart_energy := G.energy_eq_harmonicEnergy
  energy_pos := G.harmonicEnergy_pos

/-! ## C6–C7: the matter-binding laws -/

/-- **The matter-binding laws** (C6–C7): the intrinsic matter facts
and the generic geometric-binding theorems on 2-complexes. -/
structure MatterBindingLaws (G : IncidenceGraph.{u, v}) : Prop where
  mass_pos : ∀ m : MatterSector G, 0 < m.mass
  mass_least : ∀ m : MatterSector G,
    IsLeast {E : ℝ | ∃ ω : G.E → ℝ,
        (∀ j, ω ⬝ᵥ G.fundCyclesR j = ((G.h1QuotEquiv m.val) j : ℝ))
          ∧ E = ω ⬝ᵥ ω} m.mass
  mass_chart : ∀ (m : MatterSector G) {n : ℕ}
    (B : Module.Basis (Fin n) ℤ G.cycleLattice),
    (G.basisGramData B).energy (G.latticeQuotEquiv B m.val) = m.mass
  trapped : ∀ (m : MatterSector G) (ω : G.E → ℝ),
    (∀ j, ω ⬝ᵥ G.fundCyclesR j = ((G.h1QuotEquiv m.val) j : ℝ)) →
    ¬ ∃ f : G.V → ℝ, G.grad f = ω
  annihilation : ∀ m : MatterSector G,
    (G.basisGramData G.cycleBasis).bindingEnergy
      (G.h1QuotEquiv m.val) (G.h1QuotEquiv m.neg.val) = 2 * m.mass
  matter_exists : 0 < G.b1 → Nonempty (MatterSector G)
  restrict_inj : ∀ X : TwoComplex.{u, v, w} G,
    Function.Injective X.restrict
  restrict_range : ∀ X : TwoComplex.{u, v, w} G,
    LinearMap.range X.restrict = X.survivors
  kills : ∀ (X : TwoComplex.{u, v, w} G) (m : MatterSector G)
    (i : X.Faces),
    G.classPairing (X.face i) (X.face_mem i) m.val ≠ 0 →
    ¬ ∃ κ' : X.h1, X.restrict κ' = m.val
  attach_equiv : ∀ (c : G.E → ℤ) (hc : c ∈ G.cycleLattice),
    Nonempty ((G.attach c hc : TwoComplex.{u, v, w} G).h1Homology
      ≃ₗ[ℤ] (↥G.cycleLattice ⧸ (ℤ ∙ (⟨c, hc⟩ : G.cycleLattice))))
  attach_rank : ∀ (c : G.E → ℤ) (hc : c ∈ G.cycleLattice)
    (τ : G.E → ℤ), c ⬝ᵥ τ = 1 →
    Module.finrank ℤ
        (G.attach c hc : TwoComplex.{u, v, w} G).h1Homology
      = G.b1 - 1
  survivor_energy : ∀ (X : TwoComplex.{u, v, w} G) (κ' : X.h1),
    IsLeast {E : ℝ | ∃ ω : G.E → ℝ,
        ((∀ j, ω ⬝ᵥ G.fundCyclesR j
            = ((G.h1QuotEquiv (X.restrict κ')) j : ℝ))
          ∧ ∀ i, ω ⬝ᵥ (fun e => ((X.face i e : ℤ) : ℝ)) = 0)
        ∧ E = ω ⬝ᵥ ω}
      (G.harmonicEnergy (X.restrict κ'))
  spectral : ∀ X : TwoComplex.{u, v, w} G,
    X.partFn + (∑' κ : ↥((X.survivors :
        Set ((G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))))ᶜ,
      Real.exp (-G.harmonicEnergy κ.val)) = G.classPartFn
  weight_bound : ∀ (X : TwoComplex.{u, v, w} G) (m : MatterSector G)
    (i : X.Faces),
    G.classPairing (X.face i) (X.face_mem i) m.val ≠ 0 →
    X.partFn + Real.exp (-m.mass) ≤ G.classPartFn
  partFn_strict : ∀ (X : TwoComplex.{u, v, w} G) (m : MatterSector G)
    (i : X.Faces),
    G.classPairing (X.face i) (X.face_mem i) m.val ≠ 0 →
    X.partFn < G.classPartFn

/-- **Every graph satisfies the matter-binding laws** — direct
assignments. -/
theorem matterBindingLaws (G : IncidenceGraph.{u, v}) :
    MatterBindingLaws.{u, v, w} G where
  mass_pos := MatterSector.mass_pos
  mass_least := MatterSector.mass_isLeast
  mass_chart := MatterSector.mass_chart
  trapped := MatterSector.not_gradient
  annihilation := MatterSector.annihilation
  matter_exists := exists_matter G
  restrict_inj := TwoComplex.restrict_injective
  restrict_range := TwoComplex.range_restrict
  kills := TwoComplex.binding_kills_matter
  attach_equiv := fun c hc => ⟨attach_h1 c hc⟩
  attach_rank := finrank_attach_h1Homology
  survivor_energy := TwoComplex.energy_isLeast
  spectral := TwoComplex.partFn_add_killed
  weight_bound := TwoComplex.attach_partFn_add_le
  partFn_strict := TwoComplex.attach_partFn_lt

/-! ## C8–C9 on the graph: the resolution-coding laws -/

/-- **The resolution-coding laws of a graph** (C8–C9's
graph-dependent family; split from the generic `CodingGravityLaws`
by review #21): K1–K3 at every modulus, gauge counting, compression
sections and costs, and per-class recovery — every field mentions
the graph. -/
structure ResolutionCodingLaws (G : IncidenceGraph.{u, v}) : Prop where
  k1 : ∀ {n : ℕ}, Module.Basis (Fin n) ℤ G.cycleLattice →
    ∀ (q : ℕ) [NeZero q],
    Nat.card ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
      = q ^ n
  k1_intrinsic : ∀ (q : ℕ) [NeZero q],
    Nat.card ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
      = q ^ G.b1
  k1_reduction : ∀ (q : ℕ) [NeZero q],
    Nat.card (IncidenceGraph.H1Reduction G q) = q ^ G.b1
  k2 : ∀ {n : ℕ}, Module.Basis (Fin n) ℤ G.cycleLattice →
    ∀ (q : ℕ) [NeZero q],
    Real.log (Nat.card (G.E → ZMod q))
      = Real.log (Nat.card (LinearMap.range (G.gradLin (ZMod q))))
        + n * Real.log q
  k3 : ∀ (q : ℕ)
    (x : (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))),
    Nat.card {y : G.E → ZMod q //
        (Submodule.Quotient.mk y :
          (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) = x}
      = Nat.card (LinearMap.range (G.gradLin (ZMod q)))
  gauge_count : ∀ {n : ℕ}, Module.Basis (Fin n) ℤ G.cycleLattice →
    ∀ (q : ℕ) [NeZero q],
    Nat.card (LinearMap.range (G.gradLin (ZMod q)))
      = q ^ (Fintype.card G.E - n)
  compression_sections : ∀ {n : ℕ},
    Module.Basis (Fin n) ℤ G.cycleLattice → ∀ (q : ℕ) [NeZero q],
    Nat.card {s : ((G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))
        → (G.E → ZMod q) //
        ∀ x, (Submodule.Quotient.mk (s x) :
          (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))) = x}
      = Nat.card (LinearMap.range (G.gradLin (ZMod q))) ^ (q ^ n)
  compression_cost : ∀ {n : ℕ},
    Module.Basis (Fin n) ℤ G.cycleLattice → ∀ (q : ℕ) [NeZero q],
    sectionCost (fun y : G.E → ZMod q =>
        (Submodule.Quotient.mk y :
          (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))))
      = (q : ℝ) ^ n
        * Real.log (Nat.card (LinearMap.range (G.gradLin (ZMod q))))
  recovery : ∀ (q : ℕ) [NeZero q]
    (x : (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q))),
    recoveryCost (fun y : G.E → ZMod q =>
        (Submodule.Quotient.mk y :
          (G.E → ZMod q) ⧸ LinearMap.range (G.gradLin (ZMod q)))) x
      = Real.log (Nat.card (LinearMap.range (G.gradLin (ZMod q))))

/-- **Every graph satisfies the resolution-coding laws** — direct
assignments. -/
theorem resolutionCodingLaws (G : IncidenceGraph.{u, v}) :
    ResolutionCodingLaws G where
  k1 := G.card_quotient
  k1_intrinsic := G.card_quotient_eq
  k1_reduction := G.card_H1Reduction
  k2 := G.log_card_split
  k3 := G.card_fiber
  gauge_count := G.card_gauge
  compression_sections := G.card_compression_sections
  compression_cost := G.sectionCost_compression
  recovery := G.recoveryCost_compression

/-! ## C8–C9 generic: the coding-gravity laws -/

/-- **The coding-gravity laws** (C8's generic coding theorems and
C9's generic gravity/time laws; graph-free after review #21's split
— no vacuous graph quantifier): section counting, the coding theorem
with its `ℝ≥0∞` boundary, the uniform action, the priced
gravity and time identities of sector actions, and counting gravity
as the zero-energy corollary of the gravity theorem
`SectorAction.complexity_gravity` (review #25). -/
structure CodingGravityLaws : Prop where
  sections_count : ∀ {A B : Type u} [Finite A] [Fintype B]
    (f : A → B),
    Nat.card {s : B → A // ∀ b, f (s b) = b}
      = ∏ b : B, Nat.card (f ⁻¹' {b})
  coding : ∀ {A B : Type u} [Fintype A] [Fintype B] [DecidableEq B]
    {f : A → B}, Function.Surjective f →
    sectionCost f = fiberInfoCost f
  cost_top : ∀ {A B : Type u} [Finite A] [Finite B] (f : A → B),
    sectionCostE f = ⊤ ↔ ¬ Function.Surjective f
  cost_zero : ∀ {A B : Type u} [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B), sectionCostE f = 0 ↔ Function.Bijective f
  forward_cost : ∀ {A B : Type u} [Fintype A] [Fintype B] (f : A → B),
    descriptionCost f = Real.log (Nat.card (A → B))
  uniform_partFn : ∀ (A : Type u) [Fintype A] [Nonempty A],
    (uniformAction A).partFn = Fintype.card A
  uniform_complexity : ∀ (A : Type u) [Fintype A] [Nonempty A],
    (uniformAction A).complexity = Real.log (Fintype.card A)
  counting_gravity : ∀ {X Y D : Type u} [Fintype X] [Fintype Y]
    [Fintype D] [Nonempty D] (f : X → D) (g : Y → D)
    {m m' : ℕ}, 0 < m → 0 < m' →
    (∀ d, Nat.card {x : X // f x = d} = m) →
    (∀ d, Nat.card {y : Y // g y = d} = m') →
    Real.log (Nat.card (SGD.Pullback f g)) + Real.log (Nat.card D)
      = Real.log (Nat.card X) + Real.log (Nat.card Y)
  priced_gravity_partFn : ∀ (A : SectorAction.{u})
    {X Y : Type u} [Fintype X] [Fintype Y]
    (f : X → A.Λ) (g : Y → A.Λ) [Fintype (SGD.Pullback f g)]
    {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m')
    (hf : ∀ d, Nat.card {x : X // f x = d} = m)
    (hg : ∀ d, Nat.card {y : Y // g y = d} = m'),
    (A.coupling f g hm hm' hf hg).partFn * A.partFn
      = (A.uniformLift f hm hf).partFn
        * (A.uniformLift g hm' hg).partFn
  priced_gravity_complexity : ∀ (A : SectorAction.{u})
    {X Y : Type u} [Fintype X] [Fintype Y]
    (f : X → A.Λ) (g : Y → A.Λ) [Fintype (SGD.Pullback f g)]
    {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m')
    (hf : ∀ d, Nat.card {x : X // f x = d} = m)
    (hg : ∀ d, Nat.card {y : Y // g y = d} = m'),
    (A.coupling f g hm hm' hf hg).complexity + A.complexity
      = (A.uniformLift f hm hf).complexity
        + (A.uniformLift g hm' hg).complexity
  priced_gravity_entropy : ∀ (A : SectorAction.{u}) [Fintype A.Λ]
    {X Y : Type u} [Fintype X] [Fintype Y]
    (f : X → A.Λ) (g : Y → A.Λ) [Fintype (SGD.Pullback f g)]
    {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m')
    (hf : ∀ d, Nat.card {x : X // f x = d} = m)
    (hg : ∀ d, Nat.card {y : Y // g y = d} = m'),
    shannonEntropy (A.coupling f g hm hm' hf hg).gibbsMass
        + shannonEntropy A.gibbsMass
      = shannonEntropy (A.uniformLift f hm hf).gibbsMass
        + shannonEntropy (A.uniformLift g hm' hg).gibbsMass
  priced_time : ∀ (A : SectorAction.{u}) [Fintype A.Λ]
    {X : Type u} [Fintype X] (f : X → A.Λ) {m : ℕ} (hm : 0 < m)
    (hfib : ∀ d, Nat.card {x : X // f x = d} = m),
    sectionCost f / Fintype.card A.Λ
      = (A.uniformLift f hm hfib).complexity - A.complexity

/-- **The coding-gravity laws hold** — direct assignments. -/
theorem codingGravityLaws : CodingGravityLaws.{u} where
  sections_count := card_sections
  coding := sectionCost_eq_fiberInfoCost
  cost_top := sectionCostE_eq_top_iff
  cost_zero := sectionCostE_eq_zero_iff
  forward_cost := descriptionCost_eq
  uniform_partFn := uniformAction_partFn
  uniform_complexity := uniformAction_complexity
  counting_gravity := Meno.counting_gravity
  priced_gravity_partFn := SectorAction.partFn_gravity
  priced_gravity_complexity := SectorAction.complexity_gravity
  priced_gravity_entropy := SectorAction.entropy_gravity
  priced_time := SectorAction.sectionCost_uniformLift

/-! ## C5 and the flagship consumers -/

/-- **The flagship laws** (C5 + consumers): the concrete cycle,
wedge, theta, binding, and geodesic results — hand-built bases
unimodularly related to fundamental ones, closed-form Grams and
masses, `b₁` corroborations, the theta counts, dualities, priced
faces, tower prices, the thermal circle, and the geodesic–harmonic
duality. -/
structure FlagshipLaws : Prop where
  cycle_b1 : ∀ (n : ℕ) (hn : 0 < n), (cycleGraph n hn).b1 = 1
  theta_b1 : thetaGraph.b1 = 2
  wedge_b1 : ∀ (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂),
    (wedgeGraph n₁ n₂ h₁ h₂).b1 = 2
  cycle_basis_unimodular : ∀ (n : ℕ) (hn : 0 < n),
    ∃ U : Matrix (Fin (cycleGraph n hn).b1) (Fin (cycleGraph n hn).b1) ℤ,
      IsUnit U.det ∧
      ∀ j, (cycleGraph n hn).cyclesZ
          ((cycleLatticeBasis n hn).reindex
            (finCongr ((cycleGraph n hn).card_eq_b1
              (cycleLatticeBasis n hn)))) j
        = fun e => ∑ i, U i j
            * (cycleGraph n hn).cyclesZ (cycleGraph n hn).cycleBasis i e
  theta_basis_unimodular :
    ∃ U : Matrix (Fin thetaGraph.b1) (Fin thetaGraph.b1) ℤ,
      IsUnit U.det ∧
      ∀ j, thetaGraph.cyclesZ
          (thetaLatticeBasis.reindex
            (finCongr (thetaGraph.card_eq_b1 thetaLatticeBasis))) j
        = fun e => ∑ i, U i j * thetaGraph.cyclesZ thetaGraph.cycleBasis i e
  wedge_basis_unimodular : ∀ (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂),
    ∃ U : Matrix (Fin (wedgeGraph n₁ n₂ h₁ h₂).b1)
        (Fin (wedgeGraph n₁ n₂ h₁ h₂).b1) ℤ,
      IsUnit U.det ∧
      ∀ j, (wedgeGraph n₁ n₂ h₁ h₂).cyclesZ
          ((wedgeLatticeBasis n₁ n₂ h₁ h₂).reindex
            (finCongr ((wedgeGraph n₁ n₂ h₁ h₂).card_eq_b1
              (wedgeLatticeBasis n₁ n₂ h₁ h₂)))) j
        = fun e => ∑ i, U i j
            * (wedgeGraph n₁ n₂ h₁ h₂).cyclesZ
                (wedgeGraph n₁ n₂ h₁ h₂).cycleBasis i e
  theta_gram : (thetaGraph.basisGramData thetaLatticeBasis).gram
    = !![1/3, -(1/6); -(1/6), 1/3]
  theta_matter_mass : thetaMatter.mass = 1/3
  wedge_matter_mass : ∀ (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3),
    (wedgeMatter₁ n₁ n₂ h₁ h₂).mass = 1 / n₁
  wedge_matter : ∀ (n₁ n₂ : ℕ) (h₁ : n₁ ≥ 3) (h₂ : n₂ ≥ 3),
    Nonempty (MatterSector (wedgeGraph n₁ n₂ (by omega) (by omega)))
  theta_residue_count : ∀ (q : ℕ) [NeZero q],
    Nat.card ((Fin 6 → ZMod q)
        ⧸ LinearMap.range (thetaGraph.gradLin (ZMod q)))
      = q ^ 2
  theta_gauge_count : ∀ (q : ℕ) [NeZero q],
    Nat.card (LinearMap.range (thetaGraph.gradLin (ZMod q))) = q ^ 4
  theta_binding :
    ¬ ∃ κ' : thetaFilled.h1, thetaFilled.restrict κ' = thetaMatter.val
  theta_attach_rank : Module.finrank ℤ thetaFilled.h1Homology = 1
  theta_removed_weight :
    thetaFilled.partFn + Real.exp (-(1/3 : ℝ))
      ≤ thetaGraph.classPartFn
  cycle_T_duality : ∀ (n : ℕ) (hn : n ≥ 3),
    (↑(QuadraticAction.scalarPartFn (Real.pi ^ 2 * n)) : ℂ)
      = ↑((1 / (n : ℝ)) / Real.pi) ^ ((1 : ℂ) / 2)
        * ↑(Simplicial.partitionFn n hn)
  theta_duality :
    (↑(thetaHarmonicGramData.toQuadraticAction.dual.toSectorAction.partFn)
        : ℂ)
      = ↑((1/12 : ℝ) / Real.pi ^ 2) ^ ((1 : ℂ) / 2)
        * ↑(thetaHarmonicGramData.toQuadraticAction.toSectorAction.partFn)
  gravity_time_faces :
    ((thetaGraph.pairAction 2).partFn * (thetaGraph.residueAction 2).partFn
        = (thetaGraph.descriptionAction 2).partFn
          * (thetaGraph.descriptionAction 2).partFn)
      ∧ ((thetaGraph.pairAction 2).complexity
            + (thetaGraph.residueAction 2).complexity
          = (thetaGraph.descriptionAction 2).complexity
            + (thetaGraph.descriptionAction 2).complexity)
      ∧ (sectionCost (thetaGraph.carrierCompression 2)
            / Nat.card (IncidenceGraph.H1Reduction thetaGraph 2)
          = (thetaGraph.descriptionAction 2).complexity
            - (thetaGraph.residueAction 2).complexity)
      ∧ ((uniformAction
              (IncidenceGraph.H1Reduction thetaGraph 2)).complexity
            = (thetaGraph.residueAction 2).complexity
              + (thetaGraph.residueAction 2).gibbsExpect
                  (thetaGraph.residueAction 2).E
              + thetaGraph.residueDefect 2
          ∧ 0 < (thetaGraph.residueAction 2).complexity
          ∧ 0 < (thetaGraph.residueAction 2).gibbsExpect
              (thetaGraph.residueAction 2).E
          ∧ 0 < thetaGraph.residueDefect 2)
      ∧ ((uniformAction (thetaGraph.E → ZMod 2)).complexity
            = (thetaGraph.descriptionAction 2).complexity
              + (thetaGraph.descriptionAction 2).gibbsExpect
                  (thetaGraph.descriptionAction 2).E
              + thetaGraph.residueDefect 2
          ∧ 0 < (thetaGraph.descriptionAction 2).complexity
          ∧ 0 < (thetaGraph.descriptionAction 2).gibbsExpect
              (thetaGraph.descriptionAction 2).E
          ∧ 0 < thetaGraph.residueDefect 2)
      ∧ ((uniformAction (SGD.Pullback (thetaGraph.carrierCompression 2)
              (thetaGraph.carrierCompression 2))).complexity
            = (thetaGraph.pairAction 2).complexity
              + (thetaGraph.pairAction 2).gibbsExpect
                  (thetaGraph.pairAction 2).E
              + thetaGraph.residueDefect 2
          ∧ 0 < (thetaGraph.pairAction 2).complexity
          ∧ 0 < (thetaGraph.pairAction 2).gibbsExpect
              (thetaGraph.pairAction 2).E
          ∧ 0 < thetaGraph.residueDefect 2)
      ∧ 0 < (thetaGraph.residueAction 2).gibbsVariance
          (thetaGraph.residueAction 2).E
      ∧ 0 < (thetaGraph.descriptionAction 2).gibbsVariance
          (thetaGraph.descriptionAction 2).E
      ∧ 0 < (thetaGraph.pairAction 2).gibbsVariance
          (thetaGraph.pairAction 2).E
  theta_tower_prices :
    ((thetaGraph.residueDist 8).condEntropy
          (⇑(thetaGraph.h1TowerMap 2 8 (by norm_num)))
        = (thetaGraph.residueDist 8).condEntropy
              (⇑(thetaGraph.h1TowerMap 4 8 (by norm_num)))
          + (thetaGraph.residueDist 4).condEntropy
              (⇑(thetaGraph.h1TowerMap 2 4 (by norm_num))))
      ∧ sectionCost (⇑(thetaGraph.h1TowerMap 2 8 (by norm_num)))
            / Nat.card (IncidenceGraph.H1Reduction thetaGraph 2)
          = sectionCost (⇑(thetaGraph.h1TowerMap 4 8 (by norm_num)))
                / Nat.card (IncidenceGraph.H1Reduction thetaGraph 4)
            + sectionCost (⇑(thetaGraph.h1TowerMap 2 4 (by norm_num)))
                / Nat.card (IncidenceGraph.H1Reduction thetaGraph 2)
      ∧ (thetaGraph.residueDist 8).condEntropy
            (⇑(thetaGraph.h1TowerMap 2 8 (by norm_num)))
          = 2 * Real.log 4
            - (thetaGraph.residueDefect 8 - thetaGraph.residueDefect 2)
  theta_mean_equation : ∀ (β : ℝ), 0 < β →
    thetaGraph.classMeanEnergy β
        + β⁻¹ ^ 2 * (thetaGraph.cycleAction).meanEnergy β⁻¹
      = 1 / β
  theta_variance_equation : ∀ (β : ℝ) (hβ : 0 < β),
    (thetaGraph.classSectorActionβ β hβ).gibbsVariance
        thetaGraph.harmonicEnergy
      + 2 * β⁻¹ ^ 3 * (thetaGraph.cycleAction).meanEnergy β⁻¹
      - β⁻¹ ^ 4 * (((thetaGraph.cycleAction).scaledSector β⁻¹
          (inv_pos.mpr hβ)).gibbsVariance
          (fun c => (thetaGraph.cycleAction).form c c))
      = 1 / β ^ 2
  geodesic_duality : ∀ (n : ℕ) (hn : n ≥ 3),
    Geodesic.length (Simplicial.canonicalLoop n hn)
      * (cyclePeriodData n (by omega)).energy ![1] = 1

/-- **The flagship laws hold** — direct assignments. -/
theorem flagshipLaws : FlagshipLaws where
  cycle_b1 := cycleGraph_b1'
  theta_b1 := thetaGraph_b1'
  wedge_b1 := wedgeGraph_b1'
  cycle_basis_unimodular := cycleLatticeBasis_unimodular_related
  theta_basis_unimodular := thetaLatticeBasis_unimodular_related
  wedge_basis_unimodular := wedgeLatticeBasis_unimodular_related
  theta_gram := basisGramData_theta_gram
  theta_matter_mass := thetaMatter_mass
  wedge_matter_mass := wedgeMatter₁_mass
  wedge_matter := wedge_exists_matter
  theta_residue_count := Meno.theta_residue_count
  theta_gauge_count := Meno.theta_gauge_count
  theta_binding := theta_binding_kills
  theta_attach_rank := theta_attach_finrank
  theta_removed_weight := Meno.theta_removed_weight
  cycle_T_duality := partitionFn_T_duality_via_spine
  theta_duality := theta_siegelPoisson_duality
  gravity_time_faces := theta_priced_faces
  theta_tower_prices := theta_tower_price_triangle
  theta_mean_equation := theta_classMeanEnergy_T_dual
  theta_variance_equation := theta_gibbsVariance_T_dual
  geodesic_duality := Simplicial.geodesic_harmonic_duality

/-! ## The statement-coverage bundle -/

/-- **THE STATEMENT-COVERAGE BUNDLE** (reviews #18, #19, #21, #29):
every Part-I acceptance family, one field each, assembled — the four
graph-quantified Part-I law packages, the graph-free coding-gravity
package, the three spine law packages, and the
flagship consumers. Lean's kernel certifies these propositions —
statement coverage; C11's deletion state and C12's import-DAG and
duplication constraints are repository invariants checked by the
build and by review, not by the kernel. -/
structure MenoStatementCoverage : Prop where
  topology : ∀ G : IncidenceGraph.{u, v}, GraphTopologyLaws G
  harmonic : ∀ G : IncidenceGraph.{u, v}, HarmonicCarrierLaws G
  matter_binding : ∀ G : IncidenceGraph.{u, v},
    MatterBindingLaws.{u, v, w} G
  resolution_coding : ∀ G : IncidenceGraph.{u, v},
    ResolutionCodingLaws G
  coding_gravity : CodingGravityLaws.{u}
  thermal : ∀ Q : QuadLatticeAction.{u},
    QuadLatticeAction.ThermalDualityLaws Q
  information : ∀ {X : Type u} [Fintype X] [DecidableEq X]
    (P : FinDist X), FinDist.InformationLaws P
  tower : ∀ G : IncidenceGraph.{u, v},
    IncidenceGraph.ResolutionTowerLaws G
  flagship : FlagshipLaws

/-- **THE COVERAGE BUNDLE, DERIVED** (reviews #18, #19, #29): every
field a direct named-theorem assignment. Closure in full is the
five-leg conjunction, of which this bundle is the kernel-checked
leg; the others are the import DAG of Part I, the recorded
deletions, `lake build Meno` green with zero `sorry`/`axiom`/
warnings, and substantive source review of the derivation routes. -/
theorem menoStatementCoverage : MenoStatementCoverage.{u, v, w} where
  topology := graphTopologyLaws
  harmonic := harmonicCarrierLaws
  matter_binding := matterBindingLaws
  resolution_coding := resolutionCodingLaws
  coding_gravity := codingGravityLaws
  thermal := QuadLatticeAction.thermalDualityLaws
  information := FinDist.informationLaws
  tower := IncidenceGraph.resolutionTowerLaws
  flagship := flagshipLaws

end Meno
