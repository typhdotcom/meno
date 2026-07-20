# Meno II — The Obstruction Program

Adopted 2026-07-20. This plan replaces the first program (63 phases,
29 external reviews), which was executed, made current, and retired.
Its excision record is `scripts/deleted.txt`; its narrative is the
repository log. The inherited tree is green — zero `sorry`, zero
`axiom`, zero warnings, every audit leg passing — and nothing here
reopens that record. This plan exists because a current record is
not the same thing as finished mathematics.

## The stake

The universe must describe itself, and cannot: there is no objective
bit, no universal encoding, no preferred chart. The claim staked is
that this impossibility is the *source* of law, not its obstacle —
a globally unsatisfiable system still hosts observables that obey
exact laws, and the laws live on the obstruction itself.

The claim has mathematical coordinates. The diagonal fixed-point
argument is the common core of the Gödel-type incompleteness
phenomena (Lawvere's fixed-point theorem); the reading of
no-global-section obstructions as physical content is the
sheaf-theoretic treatment of contextuality. Meno's carrier is the
graph-sized incarnation of both: an `H¹` class is locally consistent
and globally unsatisfiable (`MatterSector`, `not_gradient`), the
laws of the model are proved on that obstruction lattice, and
descriptions are priced (`sectionCost`) but never canonical.

The standing tree proves the local skeleton of the stake. What it
does not yet prove is the spine: the impossibilities as theorems,
each law carrying its own correction term, and one statement at the
top that forecloses the entire stack.

## The foreclosure principle

A theorem's value is what its statement makes impossible beneath
it. A statement that compiles in every possible world is a
definition wearing a theorem's name: it can organize, it cannot
certify. The first program's discipline policed overstatement; this
program adds the dual rule and makes both binding.

1. **Four anchors per face.** A face is CLOSED when it carries:
   (a) an **impossibility** — a "there is no X" theorem;
   (b) an **exact law** whose statement contains its own correction
   term; (c) a **strictness** — a concrete witness where the
   correction term is nonzero; (d) a **boundary** — the exact
   characterization of where it vanishes. Anything less is OPEN.
2. **Repairs go upward.** A mismatch between claim and theorem is
   repaired by strengthening the theorem. Prose descends only when
   the stated ceiling is falsified, and the falsification is kept as
   a theorem — the standing model is
   `exists_dualityFlow_eq_zero_not_selfDual`.
3. **Demotion, not deletion, for true statements.** A theorem
   superseded by a stronger one is re-derived as its instance in the
   same phase: the name survives, the independent proof route dies.
4. Goal states are OPEN and CLOSED. No goal statement contains
   "or". Falsification consequences are prescribed here, never
   decided at execution time. The first discipline's rules remain in
   force where they do not conflict with this list; this list
   governs conflicts.
5. **Standing invariants** (hygiene, never acceptance): zero
   `sorry`/`axiom`/warnings; `scripts/audit.py` green on all legs —
   citations, deletions, ghosts, architecture, reachability.

## Inventory of the inherited tree

**The crown — untouched.** Siegel–Poisson at full generality with
its intrinsic bundle form; the zeta chain (`meno_mellin`,
`meno_zeta_functional_equation_real`, `menoSpectralIntegral`);
fluctuation–dissipation at every rank; the temperature–duality
functional equations; the strict modal bound
(`periodization_lt_periodization_zero`).

**The foundation — untouched.** The incidence substrate, the
keystones, Euler, the fundamental basis, the perfect pairing
(`cyclePairing`, `cyclesDualEquiv`), the attained variational
identity (`harmonicEnergy_isLeast`), matter, binding, the
resolution tower.

**The demotions — executed inside G1–G6.**
`SectorAction.complexity_gravity` and its carrier instances become
the zero-covariance instance of G2; `SectorAction.sectionCost_uniformLift`
becomes the constant-redundancy instance of G5;
`Simplicial.geodesic_harmonic_duality` becomes the equality case of
G1; `theta_interaction` and `theta_binding_attractive` become
instances of G6.

**The harvest — executed at the phases named in the Harvest
section.** The coverage bundle and its law packages fall when G7's
dichotomy replaces them; the Groupoid/Simplicial layer keeps exactly
what G1 consumes.

## The faces

### G1 — The systole inequality (geometry ⋈ matter) — CLOSED (Meno/Systole.lean)

**The exact law.** For every finite graph, every class, and every
integral cycle, pairing squared is bounded by energy times chain
norm:

```lean
theorem pairing_sq_le_energy_mul_normSq (G : IncidenceGraph)
    (κ : (G.E → ℤ) ⧸ LinearMap.range (G.gradLin ℤ))
    (c : ↥G.cycleLattice) :
    (((G.cyclePairing c) κ : ℤ) : ℝ) ^ 2
      ≤ G.harmonicEnergy κ
        * ((fun e => ((c : G.E → ℤ) e : ℝ)) ⬝ᵥ (fun e => ((c : G.E → ℤ) e : ℝ)))
```

Route: a realizer `ω` of `κ`'s periods pairs with `c` as the integer
pairing (linearity over the fundamental coordinates of `c`);
Cauchy–Schwarz for `⬝ᵥ` (`Finset.sum_mul_sq_le_sq_mul_sq`); the
infimum is attained (`harmonicEnergy_isLeast`).

**The boundary (dual-norm attainment).** The bound is sharp at the
harmonic representative — which lies in the real cycle space, since
the least-norm representative is the explicit combination
`periodRep` with coefficients `(gramOf c)⁻¹ *ᵥ k`. Acceptance: for
every real cycle combination `z ≠ 0`,
`(pairingR z κ)² / ‖z‖² ≤ harmonicEnergy κ`, with equality, for a
nonzero class (`κ ≠ 0` — at the zero class equality holds at every
`z` while no nonzero `z` is parallel to the zero representative),
iff `z` is parallel to the harmonic representative. Prerequisite
identity, standing (`basisGramData_gram`,
`Meno/BasisIndependence.lean`, a `rfl`): the priced Gram of a
lattice basis is the inverse of its chain Gram —
`(G.basisGramData B).gram = (gramOf (G.cyclesR B))⁻¹`.

**The systole corollary.** Matter's mass is bounded below by the
reciprocal shortest pairing cycle:

```lean
theorem MatterSector.mass_systole (m : MatterSector G)
    (c : ↥G.cycleLattice) (h : G.cyclePairing c m.val ≠ 0) :
    1 / ((fun e => ((c : G.E → ℤ) e : ℝ)) ⬝ᵥ (fun e => ((c : G.E → ℤ) e : ℝ)))
      ≤ m.mass
```

(the integer pairing squared is at least one).

**The strictness.** At the theta graph: every integral cycle pairing
nontrivially with `thetaMatter` has chain norm at least `4` (the
chain Gram is `!![4, 2; 2, 4]`; `a² + ab + b² ≥ 1` for nonzero
integer pairs), so the systole bound reads `1/4 ≤ 1/3` — **strict**:
`theta_mass_gt_systole : 1/4 < thetaMatter.mass`. The harmonic
representative of a theta class is supported on no single cycle.

**The boundary witness.** On `cycleGraph n` with the full cycle
(`gramOf_cycleAllOnes = !![n]`, geodesic length of
`Simplicial.canonicalLoop` equal to `n`), the bound is equality:
mass `1/n`, pairing `1`, norm `n`.
`Simplicial.geodesic_harmonic_duality` is re-derived as this
equality instance (demotion, rule 3), through the bridge
`Geodesic.length (canonicalLoop) = chain norm of the full cycle`.

**The impossibility.** `not_gradient` — already standing — is this
face's impossibility anchor, restated in the face's docstring as
such: the class whose mass the inequality bounds admits no global
potential.

**Foreclosure.** The statement elaborates only if Stokes, the
keystone, the inverse-Gram variational layer, and attainment are all
sound. **Falsification:** if the `cycleGraph` equality case fails,
the walk-length bridge is false; consequence — the Groupoid layer
loses its consumer and is harvested in the same phase.

### G2 — Covariance gravity — CLOSED (Meno/InfoRatchet.lean)

**Constructions** (`Meno/InfoRatchet.lean`): the priced lift and
coupling **without fiber hypotheses** — `SectorAction.lift`
(pull back the energy of a finite-sector action along any surjective
map from a finite type — surjectivity carries the zero-energy sector
upstairs; no constant-fiber assumption) and `SectorAction.couple`
(the pullback `SGD.Pullback f g` priced by the base), plus the
covariance `SectorAction.gibbsCov φ ψ :=
gibbsExpect (φ * ψ) − gibbsExpect φ * gibbsExpect ψ` (whose diagonal
is the existing `gibbsVariance`), and the fiber-count observable
`fiberCount f : A.Λ → ℝ := fun d => Nat.card {x // f x = d}`.

**The exact law.** For surjective `f`, `g` on finite types over a
finite-sector base, with the four-term defect named
(`gravityDefect f g hf hg :=
((couple).complexity + K) − ((lift f).complexity + (lift g).complexity)`):

```lean
theorem gravity_defect (A : SectorAction) [Fintype A.Λ] …
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    A.gravityDefect f g hf hg
    = Real.log (A.gibbsExpect (fiberCount f * fiberCount g))
      - Real.log (A.gibbsExpect (fiberCount f))
      - Real.log (A.gibbsExpect (fiberCount g))
```

with the evaluations `lift_complexity :
K(lift) = K + log ⟨fiberCount⟩` and `couple_complexity` as the
supporting exact identities. **Sharing two descriptions over one
base saves exactly the base — corrected by the log-correlation of
their redundancy profiles.** The correction term is a fluctuation
quantity: gravity's exactness is measured by the uncertainty face.

**The boundary.** `gravity_defect_eq_zero_iff : defect = 0 ↔
gibbsCov (fiberCount f) (fiberCount g) = 0`. The standing
`SectorAction.complexity_gravity` is re-derived as the constant-
fiber instance (demotion, rule 3), as are its carrier instances.

**The strictness.** A named two-sector witness: base `Bool` with
energies `0` and `1`, fiber counts `(1, 2)` for both maps; the
defect is `log⟨m²⟩ − 2 log⟨m⟩ > 0` — positive by strict Gibbs
fluctuation of the non-constant profile (`gibbsVariance_pos`), the
log split by strict monotonicity.

**The direction theorem.** Comonotone redundancy binds:
`0 ≤ defect` when
`∀ d d', 0 ≤ (fiberCount f d − fiberCount f d') * (fiberCount g d − fiberCount g d')`,
by the double-sum identity
`gibbsCov φ ψ = ½ Σ_{d,d'} μ_d μ_{d'} (φ d − φ d')(ψ d − ψ d')`.

**The impossibility.** There is no correlation-free general
coupling: the strictness witness shows the defect is not
identically zero, so the uniform identity is not a law of coupling —
it is the zero-covariance chart. Stated as the face's negative:
`exists_gravity_defect_ne_zero`.

**Falsification:** none expected (finite algebra); if the defect
were provably identically zero the constructions are degenerate —
consequence: the face is excised and gravity reverts to the
constant-fiber statement, labeled as such.

### G3 — Arithmetic gravity on the tower — OPEN

**CRT.** For `q, q' ≥ 1`, the finer reduction is the fiber product
of the coarser ones over their common coarsening:
`H1Reduction G (lcm q q') ≃ SGD.Pullback (h1TowerMap q _) (h1TowerMap q' _)`
— componentwise Chinese remainder through the keystone coordinates;
the counting identity is `Nat.gcd_mul_lcm` raised to `b₁`.

**The key lemma.** The modal coset weight is the scaled partition
function: `residueWeight q 0 = classScaledPartFn (q²)` — the fiber
of zero is `q · H¹` (`ker_h1Res`), multiplication by `q` is
injective on the free lattice, and the energy is quadratic
(`E(q • κ) = q² · E(κ)`).

**The exact law.** Via `classPartFn_eq_residueWeight_mul`, the
four-resolution gravity defect is a cross-ratio of scaled partition
functions:

```lean
theorem residue_gravity_crossRatio (hq : 1 ≤ q) (hq' : 1 ≤ q') :
    ((G.residueAction (Nat.lcm q q')).complexity
        + (G.residueAction (Nat.gcd q q')).complexity)
      - ((G.residueAction q).complexity + (G.residueAction q').complexity)
    = (Real.log (G.classScaledPartFn (q^2))
        + Real.log (G.classScaledPartFn (q'^2)))
      - (Real.log (G.classScaledPartFn ((Nat.gcd q q')^2))
        + Real.log (G.classScaledPartFn ((Nat.lcm q q')^2)))
```

**The boundary.** `q ∣ q'` makes `{gcd, lcm} = {q, q'}` and the
defect vanish identically: **gravity is exact on the tower exactly
along chains** (`residue_gravity_dvd`).

**The strictness.** On `cycleGraph 3` at `(q, q') = (2, 3)`:
`Z(1)·Z(36) > Z(4)·Z(9)` by explicit partial sums with Gaussian
tail bounds (the estimate discipline demonstrated in
`Meno/Zeta.lean`), so the defect is strictly negative —
**incomparable resolutions couple supermodularly**
(`cycle3_crossRatio_neg`).

**The impossibility.** Same theorem, read as the face's negative:
there is no resolution-independent gravity on the tower — exactness
selects the divisibility order.

**Falsification:** if the cross-ratio identity fails, the residue
factorization is unsound — consequence: the residue-action layer's
priced claims are excised and the tower reverts to counting.

### G4 — The symmetry no-go (no objective bit) — CLOSED (Meno/Symmetry.lean)

**Infrastructure** (new, generic, small): `IncidenceGraph.Auto` —
vertex and edge equivalences commuting with `src` and `tgt`; the
pullback action on `R`-cochains; commutation with the gradient;
the descended actions on `H¹` and on `H1Reduction`. The rotation
`cycleRot n : (cycleGraph n hn).Auto` (successor on vertices and
edges), acting transitively on edges and trivially on classes.

**The impossibility.** At any resolution sharing a factor with `n`,
the generator class has **no symmetric description**:

```lean
theorem cycle_no_invariant_representative
    (h : 1 < Nat.gcd n q) :
    ¬ ∃ ω : Fin n → ZMod q,
      (cycleRot n hn).cochainMap ω = ω ∧
      G.h1ResClass ω = windingOneClass n q
```

Route: rotation-invariance on a transitive edge action forces a
constant cochain; a constant cochain's winding is `n • c`, and
`1 ∉ n • ZMod q` exactly when `1 < gcd n q`.

**The exact law (the iff).** A rotation-equivariant section of the
resolution-`q` compression exists **iff** `gcd n q = 1`
(`cycle_equivariant_section_iff`) — the forward construction is the
constant cochain scaled by `n⁻¹ mod q`.

**The strictness / boundary witnesses.** `(n, q) = (4, 2)`: no
equivariant section, no invariant representative of the generator.
`(n, q) = (3, 2)`: the equivariant section, exhibited.

**The reading, stated as fact** (docstring and README at the R
phase): descriptions exist and are priced; a description respecting
the system's own symmetry can fail to exist at all; where it fails,
every encoding breaks the symmetry — the choice of bit is physical.

**Falsification:** if an invariant representative exists at
`1 < gcd n q`, the winding computation is unsound — consequence:
the descriptions reading of K1–K3 is withdrawn tree-wide and the
counting layer reverts to cochain vocabulary.

### G5 — Time, non-uniform — CLOSED (Meno/InfoRatchet.lean)

**The exact laws** (consuming G2's `lift`): the priced increment is
the log Gibbs-mean redundancy —
`lift_complexity : K(lift f) = K(base) + log ⟨fiberCount f⟩_Gibbs`,
delivered at G2 — and the counted cost stays exact and non-uniform,
`sectionCost_eq_sum_log_fiberCount : sectionCost f = Σ_d log (fiberCount f d)`
(from the standing `card_sections` and `sectionCost_eq_fiberInfoCost`).

**The law with correction term.** Jensen:

```lean
theorem lift_complexity_ge_gibbs_log_rate (hf : Function.Surjective f) :
    A.gibbsExpect (fun d => Real.log (fiberCount f d))
      ≤ (A.lift f hf).complexity - A.complexity
```

with the gap zero **iff** the redundancy is constant on the sectors
(`lift_complexity_sub_eq_iff_fiberCount_const` — full Gibbs support
makes the boundary exact) — the ratchet's defect is the Jensen gap
of redundancy, one more fluctuation quantity.

**The strictness.** G2's two-sector witness, reused
(`twoSector_jensen_gap_pos`).

**The boundary / demotion.** Constant fibers collapse both sides to
`log m` and recover `SectorAction.sectionCost_uniformLift` as the
instance (rule 3).

**The impossibility.** `sectionCostE_eq_zero_iff` — standing — is
the face's impossibility anchor (free reversal is impossible off
bijections), restated as such.

**Falsification:** none expected; if the Jensen gap were identically
zero the lift construction is degenerate — consequence as in G2.

### G6 — The binding sign criterion — CLOSED (Meno/BindingSign.lean)

**The exact law.** At `b₁ = 2` with basis cycles `c₁, c₂`, the
priced Gram is the inverse chain Gram (the standing
`basisGramData_gram`), so the two-by-two inverse
(`Matrix.inv_def` with `Matrix.adjugate_fin_two`) gives the closed
form: interaction `= −⟨c₁,c₂⟩ / det`
(`ofCycles_interaction_fin_two`), binding energy
`= 2⟨c₁,c₂⟩ / det` (`ofCycles_bindingEnergy_fin_two`), `det > 0`.

**The iff.** `binding_attractive_iff :
0 < bindingEnergyClass (h1Basis B 0) (h1Basis B 1) ↔ 0 < ⟨c₁, c₂⟩`
— **binding is attraction exactly when the cycles overlap with
consistent orientation**, with the left side the intrinsic binding
energy of the classes.

**The strictness witness.** Theta: `⟨c₁,c₂⟩ = 2`, `det = 12` —
`theta_interaction` and `theta_binding_attractive` re-derived as
instances (rule 3).

**The boundary witness.** The wedge: `⟨c₁,c₂⟩ = 0`
(`gramOf_wedgeCycles` diagonal) — disjoint matter does not bind;
stated as `wedge_binding_zero`.

**The impossibility.** With positive overlap there is no
non-attractive joint sector: the sign is forced by topology, not by
choice of basis — invariance under the unimodular action is part of
the statement, since `bindingEnergyClass` is defined through the
basis-free `harmonicEnergy` and every basis chart computes it
(`bindingEnergyClass_chart`).

**Falsification:** if theta refuses the closed form, the derived
Gram is unsound — consequence: `Meno/ThetaHarmonic.lean`'s derived
pricing is excised in favor of the literal, and the face closes on
the literal.

### G7 — The dichotomy (the completion object) — OPEN

One biconditional at the top of the tree, replacing the coverage
bundle:

```lean
theorem meno_dichotomy (G : IncidenceGraph) :
    0 < G.b1 ↔
      Nonempty (MatterSector G)
      ∧ 1 < G.classPartFn
      ∧ 0 < G.classSectorAction.gibbsVariance G.harmonicEnergy
      ∧ (∀ q, 1 < q → 0 < G.residueDefect q)
      ∧ (∀ q c, 1 < c → 1 ≤ q →
          0 < sectionCost (⇑(G.h1TowerMap q (c * q) (dvd_mul_left q c))))
```

(exact instance arguments fixed at execution; the conjunct list is
this list — matter, spectrum, fluctuation, deficit, arrow).

Forward: the standing strictness theorems (`exists_matter`,
`classSectorAction_gibbsVariance_energy_pos`, `residueDefect_pos`,
`card_h1TowerMap_fiber`). Reverse: `b₁ = 0` collapses every
conjunct — `H¹` is a subsingleton, the partition function is `1`,
the variance and deficit vanish, tower fibers are singletons.

**This is the completion object.** It cannot compile if any face is
hollow — a hollow face cannot deliver its strict conjunct — and it
breaks if any strictness theorem is deleted. Review of the program
is reading this one statement. **The universe of the model is
interesting exactly when it is globally unsatisfiable.**

On close, the Harvest executes: the coverage bundle and the law
packages are deleted and deny-listed; the README's bundle section is
replaced by the dichotomy.

**Falsification:** not falsifiable as a whole; each conjunct's
failure is its face's falsification with the consequence prescribed
at that face.

### G8 — Self-reference (the diagonal corner) — OPEN

The diagonal kernel of the stake, exactly this and no more:

```lean
theorem no_self_enumeration (A : Type u) :
    ¬ ∃ e : A → (A → ZMod 2), Function.Surjective e
```

by the direct diagonal (`g a := e a a + 1`; a preimage of `g`
yields `0 = 1` in `ZMod 2`), with the cost corollary
`Real.log (Nat.card A) < descriptionCost f` for any
`f : A → ZMod 2` on a nontrivial finite `A`: **no description
system enumerates its own binary predicates, and the shortfall is
priced.** Scope stated plainly: this is the Lawvere/Cantor core in
Meno's vocabulary, not a formalization of the incompleteness
theorems.

**Falsification:** none (the diagonal is unconditional).

## Harvest

The deletion ledger. Names listed here are scheduled excisions;
entries are struck into `scripts/deleted.txt` at the executing
phase. This section is exempt from the audit's ghosts leg; nothing
outside a `Harvest` entry cites a deleted name.

- **At G7 close:** `MenoStatementCoverage`, `menoStatementCoverage`,
  `GraphTopologyLaws`, `graphTopologyLaws`, `HarmonicCarrierLaws`,
  `harmonicCarrierLaws`, `MatterBindingLaws`, `matterBindingLaws`,
  `ResolutionCodingLaws`, `resolutionCodingLaws`,
  `CodingGravityLaws`, `codingGravityLaws`, `FlagshipLaws`,
  `flagshipLaws`, `ThermalDualityLaws`, `thermalDualityLaws`,
  `InformationLaws`, `informationLaws`, `ResolutionTowerLaws`,
  `resolutionTowerLaws` — the dichotomy plus the faces' anchors are
  the successor. `Meno/Completion.lean` then contains the dichotomy
  and nothing else.
- **At G1 close:** every Groupoid/Simplicial declaration not
  consumed by the walk-length bridge, the retained spine
  identifications, or the standing README claims — enumerated at
  that phase, deleted, recorded.
- **At G2/G5 close:** nothing — demotions re-derive standing
  theorems as instances and keep their names (rule 3).

## Execution order

G4 → G1 → G2 → G5 → G6 → G3 → G8 → G7 → R.

Rationale: G4 first — it builds the only new generic infrastructure
(`IncidenceGraph.Auto`) and is the shortest path to the stake's
sharpest sentence. G1 second — pure consumption of the standing
variational layer, and it settles the Groupoid harvest early. G2 and
G5 share the non-uniform constructions. G6 is small and consumes
G1's inverse-Gram lemma. G3 needs G2's shape and carries the
estimate work. G8 is independent and small. G7 assembles everything
and executes the main Harvest. R is the README rewrite: the stake,
the crown, the eight faces with their anchors, the dichotomy as the
completion object — no coverage bundle, no review chronology.

## Status Ledger

| Face | Anchors delivered | Status |
|------|-------------------|--------|
| G1 systole inequality | impossibility `MatterSector.not_gradient` (standing, restated); law `pairing_sq_le_energy_mul_normSq` + `MatterSector.mass_systole`; boundary `dualNorm_combination_le` / `dualNorm_combination_eq_iff` + equality `cycle_systole_equality` (with `geodesic_harmonic_duality` demoted to its instance); strictness `theta_pairing_normSq_ge_four`, `theta_mass_gt_systole`. Harvest enumerated: empty | **CLOSED** |
| G2 covariance gravity | constructions `SectorAction.lift` / `SectorAction.couple` / `gibbsCov` / `fiberCount`; law `gravity_defect` (with `lift_complexity`, `couple_complexity`); boundary `gravity_defect_eq_zero_iff` (`complexity_gravity` demoted to the zero-covariance chart); strictness `twoSector_gravityDefect_pos`; direction `gravityDefect_nonneg_of_comonotone` (via `gibbsCov_double_sum`); impossibility `exists_gravity_defect_ne_zero` | **CLOSED** |
| G3 arithmetic gravity | — | **OPEN** |
| G4 symmetry no-go | impossibility `cycle_no_invariant_representative`; law `cycle_equivariant_section_iff`; strictness `cycle_four_two_no_equivariant_section`, `cycle_four_two_no_invariant_representative`; boundary `cycle_three_two_equivariant_section` | **CLOSED** |
| G5 non-uniform time | laws `lift_complexity` (G2) + `sectionCost_eq_sum_log_fiberCount`; Jensen `lift_complexity_ge_gibbs_log_rate` with boundary `lift_complexity_sub_eq_iff_fiberCount_const`; strictness `twoSector_jensen_gap_pos`; demotion `sectionCost_uniformLift` to the constant-redundancy chart; impossibility `sectionCostE_eq_zero_iff` (standing, restated) | **CLOSED** |
| G6 binding sign | closed form `ofCycles_interaction_fin_two` / `ofCycles_bindingEnergy_fin_two`; iff `binding_attractive_iff` on the intrinsic `bindingEnergyClass` (invariance via `bindingEnergyClass_chart`); strictness `theta_interaction` / `theta_binding_attractive` demoted to instances; boundary `wedge_binding_zero` | **CLOSED** |
| G7 dichotomy | — | **OPEN** |
| G8 self-reference | — | **OPEN** |
| R README rewrite | — | **OPEN** |
