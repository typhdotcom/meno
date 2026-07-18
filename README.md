# Meno

*Structural Geometrodynamics in Lean 4*

Meno formalizes a speculative thesis: **a universe minimizes the cost of
describing itself**, and gravity, matter, time, and uncertainty are
faces of that minimization. The carrier of the thesis is a **sector
lattice with a positive-definite quadratic action**: the lattice
enumerates the discrete sectors a system can occupy, the action prices
them, the Boltzmann sum reads the partition function, and duality,
minimization, and counting theorems connect the faces. For a graph the
carrier is one bundled formal object — `IncidenceGraph.classQuadAction`,
the lattice `H¹(G;ℤ)` with the polarized form `classForm`, positive
definite on the real scalar extension `ℝ ⊗[ℤ] H¹` (`classForm_self`,
`classForm_chart`; integral positivity and summability are derived,
`Meno/LatticeAction.lean`); `classSectorAction` is its analytic
projection. Every basis-coordinate quadratic action is a
form-preserving chart of it (`chartAction_h1Basis`), it carries an
intrinsic dual lattice with the `π²`-scaled inverse form and the
Siegel–Poisson duality intrinsically (`classQuadAction_duality`,
`QuadLatticeAction.dual_dual`), every finite-resolution residue is its
quotient (`h1ResQuotEquiv`), its Gibbs distribution pushes to a
residue distribution on that quotient (`residueMass`), gravity is the
entropy of sharing one of its finite sectors
(`carrier_gravity_entropy`, with `carrier_gravity_complexity` the
uniform specialization), the gauge-fixing cost of reading a
description is the time face — the conditional entropy per sector
(`sectionCost_carrierCompression_div`) — and Gibbs fluctuation
specializes to it (`classSectorAction_gibbsVariance_nonneg`).

Everything below is a checked theorem — zero `sorry`, zero `axiom`
declarations, ~3300 build jobs green against Lean 4.26.0 / Mathlib.
The program, its completion discipline, and the per-goal ledger live in
[`PLAN.md`](PLAN.md); all twelve goals of the Completion Path are
closed.

## What is proved

**Duality.** The Siegel–Poisson duality
`Z(π²·Q⁻¹) = √(det Q / π^r) · Z(Q)` at full generality — non-diagonal
Gram forms, any rank — via multidimensional Poisson summation
(`QuadraticAction.duality`, `Meno/SiegelPoisson.lean`), consumed by a
genuinely non-diagonal instance, the theta graph's coupled Gram form
(`theta_siegelPoisson_duality`). The scalar case reproduces the
cycle-graph T-duality through the spine with no bespoke modular input
(`partitionFn_T_duality_via_spine`), and Riemann's derivation of the
functional equation runs through the same single analytic source
(`Meno/Zeta.lean`). The duality is also **intrinsic**: the carrier
bundle has a dual on `Module.Dual ℤ Λ` with the `π²`-scaled inverse
real form — no basis in the definition — every dual basis charts it
as the coordinate dual (`chartAction_dual`), the discriminant is
basis-independent (`disc_eq`), the duality holds with prefactor
`√(disc/π^rank)` (`QuadLatticeAction.duality`), the double dual is
the original along reflexivity (`dual_dual`), and the per-chart
coordinate duality is a corollary (`basisGramData_duality`,
`Meno/LatticeAction.lean`).

**Topology, intrinsically.** Every finite multigraph
(`IncidenceGraph`) carries an intrinsic integral cycle lattice
`H₁(G;ℤ) = ker ∂ℤ` and cohomology `H¹(G;ℤ) = ℤ-cochains ⧸ gradients`.
A presentation **is** a lattice basis
`Module.Basis (Fin n) ℤ G.cycleLattice` — no presentation structure,
no stored fields: closedness, real/integer independence, period
realizability, integral potentials, spanning, the positive-definite
unit-edge Gram, and the keystone equivalences are all *theorems* of
any basis (`Meno/GraphHomology.lean`). The fundamental basis
(`IncidenceGraph.cycleBasis`) equips *every* finite graph with one,
via a saturation argument, the PID structure theorem, and a
walk-integration engine. Consequences for every finite graph:
`H¹(G;ℤ) ≃ ℤ^{b₁}` (`h1QuotEquiv`), Euler's formula
`b₁ = |E| − |V| + c` (`b1_eq`, proved in the topology layer), and the
gauge theorem `dim(ker grad) = #components` (`finrank_gauge`) —
connectivity governs gauge, never exactness
(`period_eq_zero_iff_exists_grad` needs no connectivity).

**Basis independence.** Every lattice basis has exactly `b₁` elements
(`card_eq_b1`); any two are unimodularly related
(`exists_unimodular_relating`, `Meno/BasisIndependence.lean`);
primitivity is forced (`exists_int_coords`), and energies, masses, and
the partition function are functions of the graph alone
(`basisGramData_partFn`, `IncidenceGraph.partFn`,
`MatterSector.mass_chart`).

**Matter.** A matter sector is a nonzero class of `H¹(G;ℤ)`
(`MatterSector`, `Meno/Matter.lean`). Its mass is the intrinsic
harmonic energy (`IncidenceGraph.harmonicEnergy`), positive for every
nonzero class (`harmonicEnergy_pos`), attained as the least cochain
energy among realizers (`harmonicEnergy_isLeast`), and computed by
every presentation (`energy_eq_harmonicEnergy`). **Matter is trapped
paradox**: every cochain realizing a nonzero class admits no potential
(`not_gradient`) — locally consistent, globally unsatisfiable.
Nontrivial topology forces matter (`exists_matter`). Annihilation
releases the pair's full rest mass (`annihilation`).

**Binding.** Attaching a 2-cell along a cycle changes the space and
kills the matter that wrapped it (`Meno/Binding.lean`). The induced
restriction `H¹(X) → H¹(G)` is injective with image exactly the
classes annihilating the attached cycles (`restrict_injective`,
`range_restrict`); a sector with nonzero period around a filled face
has **no image at all** (`binding_kills_matter`). On homology,
`H₁(X) = H₁(G)/⟨c⟩` (`attach_h1`), free of rank `b₁ − 1` for primitive
`c` (`finrank_attach_h1Homology`). Survivors keep their exact mass
(`TwoComplex.energy_isLeast`), and the partition function strictly
drops — by at least the killed sector's entire Boltzmann weight
(`attach_partFn_add_le`, `attach_partFn_lt`). Concretely: filling the
theta graph's first cycle kills its `1/3`-mass sector and costs the
spectrum at least `exp(−1/3)` (`theta_binding_kills`,
`theta_removed_weight`, `Meno/ThetaBinding.lean`). The spectrum *partitions exactly* into
survivors and casualties (`TwoComplex.partFn_add_killed`); the drop is
a removed Boltzmann weight — the theorem that releases an *energy*
equal to a rest mass is algebraic annihilation.

**Time and information.** Descriptions at resolution `q` modulo local
re-description number exactly `q^{b₁}` (`card_quotient` — K1, for
every modulus and every finite graph); description cost splits as
gauge + incompressible residue (`log_card_split` — K2); every
compression fiber is uniform (`card_fiber` — K3), with the gauge group
`q^{|E|−b₁}` (`card_gauge`) — Euler's formula read as a factorization
of counts. The ratchet is **derived, not defined**: the reverse
descriptions of a map are its sections, counted exactly
(`card_sections`), so reverse-description cost *equals* fiber
information as a coding theorem (`log_card_sections`,
`sectionCost_compression` for the global gauge-fixing,
`recoveryCost_compression` for a single class). The numerical costs are
defined only on finite types — `Nat.card`'s junk zero on infinite
types is refused, not exploited. The extended cost is `⊤` when no
section exists, zero cost characterizes bijections
(`sectionCostE_eq_top_iff`, `sectionCostE_eq_zero_iff`), the extended
per-output cost prices unproducible outputs at `⊤`
(`recoveryCostE_eq_top_iff`), and the extended coding identity holds
on both sides of the boundary
(`sectionCostE_eq_sum_recoveryCostE`) — an impossible inverse is not
free. Where fibers are infinite, the
cardinality-free form holds: a section of a non-injective map always
misses states (`section_not_surjective_of_not_injective`,
`simplicial_ratchet`). And the information face inhabits the thesis's
**one integral carrier**, not merely its API: the intrinsic sector
action is `H¹(G;ℤ)` with the harmonic energy
(`classSectorAction`, `Meno/BasisIndependence.lean`), every
basis-coordinate action is a chart of it (`classSectorAction_energy`,
`basisGramData_partFn_eq_classSectorAction`), and the resolution-`q`
residue is exactly its quotient by `q` — coefficient reduction
`h1Res` is surjective with kernel `q·H¹(G;ℤ)`, giving
`H¹(G;ℤ)⧸q·H¹(G;ℤ) ≃ H¹(G;ZMod q)` (`h1ResQuotEquiv`) with
coordinates commuting with the keystones (`latticeQuotEquivQ_h1Res`).
The residue's uniform complexity `b₁ · log q` and the K2 split are
derived through that reduction
(`uniformAction_h1ResQuot_complexity`,
`uniformComplexity_split_carrier`, `Meno/ResolutionCount.lean`).
The reduction is moreover **priced**: the carrier's intrinsic Gibbs
distribution pushes forward to the residue distribution
(`residueMass` — positive, normalized, computed by every basis chart),
lifts uniformly through the compression (`descriptionMass`), the
description entropy splits as residue entropy plus the gauge log
(`descriptionEntropy_split`), and the per-sector gauge-fixing cost is
exactly that conditional entropy (`sectionCost_carrierCompression_div`)
— time's arrow priced against the Gibbs law, not only against counts.

**Gravity.** A finite type is a sector lattice with zero energy:
`Z = |A|`, `K = log|A|` (`uniformAction`, `Meno/UniformAction.lean`).
Type-level gravity is then a partition-function identity: for uniform
fibers, `Z(A ×_D B) · Z(D) = Z(A) · Z(B)` (`gravity_partFn`) —
sharing a base is worth exactly one copy of it — with the complexity
form `K(P) + K(D) = K(A) + K(B)` (`gravity_complexity`) realizing the
abstract `SGD.gravity` of `Meno/Basic.lean`, and the refactoring bound
`K(P) ≤ K(D) + log(max fiber product)` (`uniform_refactoring_bound`).
On the graph carrier gravity is **priced by the action**: the entropy
of the shared-pair distribution — two descriptions of the same finite
sector, weighted by the intrinsic Gibbs law — is the residue entropy
plus two gauge logs (`carrier_gravity_entropy`,
`Meno/ResolutionCount.lean`), and the uniform complexity identity is
its uniform-distribution specialization
(`carrier_gravity_complexity_of_entropy`; the SGD-bridge derivation
`carrier_gravity_complexity` stands as independent corroboration).

**Uncertainty.** The Gibbs state's fluctuations are the model's
uncertainty, and they are theorems, not vocabulary: the variance of
any observable against the Boltzmann weights is nonnegative
(`gibbsVariance_nonneg`, `Meno/SectorAction.lean`), and the
**fluctuation–dissipation identity** ties response to fluctuation —
on the canonical quadratic family, the derivative of the Gibbs mean
of squared winding in the coupling is *minus the Gibbs variance* of
squared winding
(`hasDerivAt_quadraticMeanEnergy_eq_neg_gibbsVariance`,
`Meno/Duality.lean`); that variance's strict positivity is exactly
why the mean energy strictly falls
(`quadraticMeanEnergy_strictAntiOn`).

**Geometry.** Every symmetric simplicial complex's fundamental
groupoid carries a Lawvere-subadditive geodesic length
(`simplicialGeodesic`, `Meno/Groupoid.lean`), and on the `n`-cycle the
combinatorial and harmonic masses meet: `n · (1/n) = 1`
(`geodesic_harmonic_duality`).

## Architecture

```
Meno/
├── SectorAction.lean          Analytic primitive: sectors, Boltzmann weights, partFn, complexity
├── QuadraticAction.lean       kᵀQk actions; scalar & diagonal Siegel–Poisson duality
├── SiegelPoisson.lean         Full-generality (non-diagonal) Siegel–Poisson via Poisson summation
├── LatticeAction.lean         The carrier bundle: real-extension positivity, charts, intrinsic dual & duality
├── LoopKernel.lean            Categorical presentation: End(base) as sector lattice
├── SectorPresentation.lean    MulEquiv coordinates; duality transport
├── Geodesic.lean              Lawvere-subadditive length class
├── HarmonicForm.lean          HarmonicGramData; variational builder; binding algebra
├── IncidenceGraph.lean        THE graph substrate: ∂, grad, Stokes (any ring); walks; components; gauge; H₁; b₁
├── GraphHomology.lean         Pure graph homology: every lattice basis's derived data; keystones; Euler; basisOfCycles
├── ThetaGraph.lean            The theta graph: incidence data and raw integral cycle facts
├── GraphInstances.lean        Cycle, theta, genuine wedge: connectivity, Euler b₁, and the concrete lattice bases
├── PeriodHarmonic.lean        Least-norm-at-prescribed-periods machinery; cycle & wedge Gram forms
├── HarmonicClass.lean         Priced Gram data of a basis; intrinsic harmonic energy on H¹; variational identity
├── BasisIndependence.lean     Bases unimodularly related; partFn is the graph's; classQuadAction bundled
├── WedgePresentation.lean     C5 acceptance witnesses: wedge matter; hand-built bases related to the fundamental one
├── Matter.lean                MatterSector = nonzero H¹ class; mass, positivity, trapped paradox
├── Binding.lean               2-complexes; the induced map; binding kills matter; exact spectral decomposition
├── ThetaBinding.lean          Binding at the theta graph: kill, rank drop `2 → 1`, removed weight
├── Basic.lean                 Abstract complexity hierarchy; pullback gravity (interface layer)
├── Instances.lean             Log-cardinality instance of the abstract hierarchy
├── UniformAction.lean         Type-level gravity realized on the uniform sector action
├── InfoRatchet.lean           Fiber information; the coding theorem (finite-only costs, extended costs); ratchets
├── ResolutionCount.lean       K1–K3 at every resolution; gauge count; section cost; the Gibbs residue distribution
├── Simplicial.lean            Walk/homotopy/Hodge model (independent corroborating route)
├── Groupoid.lean              Fundamental groupoid; geodesic instance; groupoid complexity
├── CycleHarmonic.lean         Flagship bridge: walk route ≡ period route; T-duality on C_n
├── ThetaHarmonic.lean         The theta graph: non-diagonal Gram derived from topology
├── Hodge.lean                 Graph partition functions (identified with the spine)
├── Duality.lean               Groupoid-facing duality wrappers (identified with the spine)
└── Zeta.lean                  Riemann functional equation through the spine's theta identification
```

The legacy layer (`Simplicial`–`Zeta`) is retained deliberately: it is
a second, independent derivation of the spine's first objects, with
the identifications proved (`cyclePeriodData_energy_eq`,
`quadraticPartFn_eq_scalarPartFn`, `graphPartitionFn_eq_spine`,
`GroupoidObj.gibbsMass_eq_sector`, …). Two derivations, one object.

## Reading the thesis honestly

The words "gravity", "matter", "time", "uncertainty" name formal
analogues inside a finite, discrete model: gravity is a pullback
complexity identity, matter is nontrivial cohomology with variational
mass, time's arrow is the counted cost of reversing compression, and
uncertainty is Gibbs fluctuation with its response identity. The project's claim is that
these analogues are *theorems of one structure* — the sector lattice
with its action — not that the physical world has been derived. Where
a desired statement failed, the failure is recorded in `PLAN.md`
(falsified designs are kept as falsified, with proofs).

## Build

Requires Lean 4.26.0 and the pinned Mathlib.

```bash
lake build
```
