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
form-preserving chart of it (`chartAction_h1Basis`), and its dual
lattice **is graph homology**: period evaluation identifies
`Module.Dual ℤ H¹` with the cycle lattice `H₁(G;ℤ)`
(`cyclesDualEquiv`), the dual action is `π²` times the unit-edge
chain pairing of cycles, and Siegel–Poisson duality holds directly
between harmonic `H¹` sectors and priced `H₁` cycles
(`cycle_harmonic_duality`), with the double dual a bundled
form-preserving involution (`dualDual`, `duality_dualDual`). Every
finite-resolution residue is its quotient (`h1ResQuotEquiv`), its
Gibbs distribution pushes to a residue distribution on that quotient
(`residueMass`), gravity is the four-term identity of sharing one of
its finite sectors — priced at the level of actions,
`K(pair) + K(residue) = 2·K(description)` (`carrier_gravity_action`),
with the entropy form a corollary of the priced calculus
(`carrier_gravity_entropy`) and the uniform complexity identity the
priced identity plus the common deficit — the gauge-fixing cost of
reading a description is the time face — the complexity difference
`K(description) − K(residue)` per sector
(`sectionCost_carrierCompression_action`, a direct specialization of
the generic priced time law) — and Gibbs fluctuation consumes it
unconditionally, strictly on any graph with cycles
(`classSectorAction_gibbsVariance_energy_pos`).

Everything below is a checked theorem — zero `sorry`, zero `axiom`
declarations, ~3300 build jobs green against Lean 4.26.0 / Mathlib.
The program, its completion discipline, and the per-goal ledger live in
[`PLAN.md`](PLAN.md); all twelve goals of the Completion Path are
closed, and the closure itself is a **Lean object**: the semantic
completion certificate `MenoSemanticCompletion`
(`Meno/Completion.lean`) is derived mechanically from the plan's
Part I — every C1–C10 acceptance signature is a field in exactly one
law package (`GraphTopologyLaws`, `HarmonicCarrierLaws`,
`MatterBindingLaws`, `CodingGravityLaws`, `ThermalDualityLaws`,
`InformationLaws`, `ResolutionTowerLaws`, `FlagshipLaws`), and
`menoSemanticCompletion` is its one derivation, by direct
named-theorem assignment. Its scope is stated honestly: the
certificate enforces **statement coverage** (deleting an acceptance
theorem breaks the derivation); proof provenance is enforced by the
direct-assignment discipline and review, and the import-DAG and
deletion constraints are repository invariants checked by the build
and by review — closure is that whole conjunction.

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
basis-independent (`disc_eq`) with the reciprocal law
`disc(Q^∨) = π^{2·rank}/disc(Q)` (`disc_dual`), the duality holds
with prefactor `√(disc/π^rank)` (`QuadLatticeAction.duality`), the
double dual is a **bundled form-preserving involution** —
`Q.dual.dual ≃q Q` (`dualDual`) with rank, energy, discriminant, and
partition function transported, and applying the duality twice
cancels the prefactors and returns the original (`duality_dualDual`).
The per-chart coordinate duality is a corollary
(`basisGramData_duality`). And for a graph the dual is **topology**:
period evaluation is a perfect pairing `H₁(G;ℤ) ≃ Dual ℤ H¹(G;ℤ)`
(`cyclesDualEquiv`, well-defined by Stokes, bijective by the
keystone), the transported form is `π²` times the unit-edge chain
pairing, and the duality reads `Z(priced cycles) =
√(disc/π^{b₁})·Z(harmonic classes)` (`cycle_harmonic_duality`,
`Meno/BasisIndependence.lean`). The form-preserving equivalences are
a calculus: `refl`/`trans`/`symm`/`dual` with identity and
associativity laws, the inverse laws `e ⬝ e⁻¹ = refl` and
`e⁻¹ ⬝ e = refl` (`trans_symm`, `symm_trans`), contravariant
functoriality of the dual — `(e ⬝ e')^∨ = e'^∨ ⬝ e^∨`,
`(refl)^∨ = refl`, `(e⁻¹)^∨ = (e^∨)⁻¹` (`dual_trans`, `dual_refl`,
`dual_symm`) — and dual-double naturality, giving the symmetric
statement `classQuadAction ≃q cycleAction.dual`
(`classActionEquivCycleDual`); the two duality prefactors multiply to
one as a named theorem (`dual_prefactor_mul_one`). **The concrete dualities flow through the
topological theorem**: the theta duality and the cycle-graph
T-duality are `cycle_harmonic_duality` read in the concrete lattice
bases (`theta_siegelPoisson_duality`,
`partitionFn_T_duality_via_spine`). A coordinate action itself embeds
canonically — `ofQuadraticAction` equips `ℤʳ` with the Gram form,
charts back to the original at the standard basis, and dualizes to
the coordinate dual at the standard dual basis — so the coordinate
duality statement is a corollary of the intrinsic one
(`QuadraticAction.duality_via_lattice`), the categorical duality
consumes the corollary (`dualVia_partFn_duality`,
`Meno/SectorPresentation.lean`), and the direct analytic invocation
of `QuadraticAction.duality` occurs once globally — inside
`QuadLatticeAction.duality`. And **duality is temperature,
inverted**: scaling multiplies the discriminant by `β^rank`
(`disc_scale`) and the dual of the scaled bundle *is* the
inverse-scaled dual — `(β·Q)∨ = β⁻¹·(Q∨)` (`scale_dual`, an equality
of bundles). The duality at the scaled bundle is the **scaled
duality** `Z_{Q∨}(β⁻¹) = √(β^rank·disc/π^rank)·Z_Q(β)`
(`scaled_duality`), and its logarithmic derivative is the
**temperature–duality functional equation**
`⟨E⟩_Q(β) + β⁻²·⟨E⟩_{Q∨}(β⁻¹) = rank/(2β)`
(`QuadLatticeAction.meanEnergy_T_dual`) — differentiated once, for
every bundled lattice action. The scalar functional equation and the
self-dual value `⟨k²⟩_π = 1/(4π)` are its unit instance
(`quadraticMeanEnergy_T_dual`, `quadraticMeanEnergy_self_dual`,
`Meno/Duality.lean`); on a graph it locks harmonic `H¹` to priced
`H₁` at reciprocal temperatures —
`⟨E⟩_{H¹}(β) + β⁻²·⟨E⟩_{H₁}(β⁻¹) = b₁/(2β)`
(`classMeanEnergy_T_dual`, `Meno/BasisIndependence.lean`) — and the
non-diagonal theta carrier consumes it
(`theta_classMeanEnergy_T_dual`: `= 1/β`). The circle closes under
response (review #18): differentiating the functional equation once
more — with the established derivative theorems, no new lattice-sum
differentiation — forces the **variance transformation law**
`Var_Q(β) + 2β⁻³·⟨E⟩_{Q∨}(β⁻¹) − β⁻⁴·Var_{Q∨}(β⁻¹) = rank/(2β²)`
(`gibbsVariance_T_dual`), a self-dual bundle sits at the fixed point
`⟨E⟩(1) = rank/4` (`meanEnergy_self_dual`), and both transport to
harmonic `H¹` versus priced `H₁` (`classGibbsVariance_T_dual`,
`classMeanEnergy_self_dual`) with the variance law consumed on theta
(`theta_gibbsVariance_T_dual`: `= 1/β²`).

**Topology, intrinsically.** Every finite multigraph
(`IncidenceGraph`) carries an intrinsic integral cycle lattice
`H₁(G;ℤ) = ker ∂ℤ` and cohomology `H¹(G;ℤ) = ℤ-cochains ⧸ gradients`.
A presentation **is** a lattice basis
`Module.Basis (Fin n) ℤ G.cycleLattice` — no presentation structure,
no stored fields: closedness, real/integer independence, period
realizability, integral potentials, spanning, and the keystone
equivalences are all *theorems* of any basis
(`Meno/GraphHomology.lean`); the positive-definite unit-edge Gram is
a theorem of the **priced** layer (`gramOf_cyclesR_posDef`,
`Meno/PeriodHarmonic.lean`) — the topology layer itself is
deliberately unpriced. The fundamental basis
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
— at the action level, exactly the complexity difference
`K(descriptionAction) − K(residueAction)`
(`sectionCost_carrierCompression_action` — a direct specialization
of the generic priced time law
`sectionCost f / |Λ| = K(uniformLift) − K(base)`,
`SectorAction.sectionCost_uniformLift`) — time's arrow priced
against the action, not only against counts.

**Gravity.** A finite type is a sector lattice with zero energy:
`Z = |A|`, `K = log|A|` (`uniformAction`, `Meno/UniformAction.lean`).
Type-level gravity is then a partition-function identity: for uniform
fibers, `Z(A ×_D B) · Z(D) = Z(A) · Z(B)` (`gravity_partFn`) —
sharing a base is worth exactly one copy of it — with the complexity
form `K(P) + K(D) = K(A) + K(B)` (`gravity_complexity`) realizing the
abstract `SGD.gravity` of `Meno/Basic.lean`, and the refactoring bound
`K(P) ≤ K(D) + log(max fiber product)` (`uniform_refactoring_bound`).
On the graph carrier gravity is **priced by the action**, at the
level of the actions themselves (`Meno/InfoRatchet.lean`,
`Meno/ResolutionCount.lean`). The residue distribution is the Gibbs
law of the **residue action**, and the residue action is *derived*,
not reconstructed: it is the coarse-graining of the harmonic action
at the quotient map (`SectorAction.coarseGrain`, `residueAction`) —
unnormalized coset weights `W ξ = ∑_{κ mod q = ξ} exp(−E_harm κ)`
(`residueWeight`) with `residueMass = W/Z`
(`residueMass_eq_residueWeight_div`), energy the effective
free-energy difference `F ξ − F 0` with `F = −log W`
(`residueAction_E_freeEnergy`), and the harmonic partition function
factorizing as `Z = W 0 · Z_residue`
(`classPartFn_eq_residueWeight_mul`, with the complexity
decomposition `classComplexity_residue_split`). Descriptions and
pairs are actions too: the **priced uniform lift** and **priced
shared-base coupling** (`SectorAction.uniformLift`,
`SectorAction.coupling`) whose Gibbs laws are exactly the `FinDist`
constructions (`uniformLift_gibbsDist`, `coupling_gibbsDist`; on the
carrier `descriptionAction` and `pairAction` with
`descriptionAction_gibbsDist`, `pairAction_gibbsDist`, both coupling
marginals the description distribution — `pairDist_fst`,
`pairDist_snd` — and expected energy and variance transported
untouched: `descriptionAction_gibbsExpect_E`,
`pairAction_gibbsVariance_E`). The gravity identity then holds
**priced**, at partition functions and at complexities —
`Z(pair)·Z(residue) = Z(description)²` (`carrier_gravity_partFn`)
and `K(pair) + K(residue) = 2·K(description)`
(`carrier_gravity_action`) — and the entropy form
`H(pair) + H(residue) = 2·H(description)` is a **corollary of the
priced calculus** (`SectorAction.entropy_gravity` — the four Gibbs
entropy splits, complexity gravity, and the expectation transports —
instantiated at the residue action, `carrier_gravity_entropy`), with
the uniform complexity identity the priced identity plus the common
deficit (`carrier_gravity_complexity_of_entropy`; the SGD-bridge
derivation `carrier_gravity_complexity` stands as independent
corroboration). Pricing and counting are **numerically bridged** by
the uniform entropy defect `Δ(P) = log|X| − H(P)` (`FinDist.defect`
— nonnegative by the maximum entropy theorem, zero exactly at the
uniform distribution, preserved by lifting and coupling), and the
bridge carries pricing **at all three levels with the same
deficit** — `K_uniform = K(action) + ⟨E⟩ + Δ` for residue,
description, and pair (`uniformComplexity_residue_bridge`,
`uniformComplexity_description_bridge`,
`uniformComplexity_pair_bridge`, through the Gibbs entropy split
`H = K + ⟨E⟩`, `SectorAction.entropy_gibbs`). And the decomposition
is **strict** wherever there is anything to price: energy vanishes
exactly at the zero class and is strictly positive exactly off it
(`residueAction_E_eq_zero_iff`, `residueAction_E_pos_iff`) — the
zero class is strictly modal, every nonzero sector carrying strictly
less residue mass (`residueMass_lt_residueMass_zero`, through the
single Gaussian Fourier engine of Siegel–Poisson:
`hasSum_gaussFourier_periodization` feeding both Poisson summation
and the strict modal bound `periodization_lt_periodization_zero`,
`Meno/SiegelPoisson.lean`) — so on every graph with cycles at every
resolution `1 < q` **all three bridge terms are strictly positive**,
`0 < K(residueAction)`, `0 < ⟨E⟩`, `0 < Δ`
(`uniformComplexity_residue_bridge_pos`, subsuming
`residueDist_ne_uniform` and `residueDefect_pos`), concretely at the
theta graph with `q = 2` (`theta_residue_bridge_pos`,
`theta_residueDefect_pos`). The strictness reaches the whole
branch — the description and pair bridges also decompose into three
strictly positive terms (`uniformComplexity_description_bridge_pos`,
`uniformComplexity_pair_bridge_pos`) — and the resolutions form a
**tower**: coarse-graining has identity and composition laws
(`coarseGrain_id`, `coarseGrain_comp`), for `q ∣ q'` the finer
reduction maps canonically onto the coarser (`h1TowerMap` — with
identity, composition, witness-independence, and surjectivity laws,
and weights, distributions, and actions composing across it:
`h1TowerMap_comp`, `residueDist_tower_trans`,
`residueAction_tower_trans`), residue weights, masses, and the Gibbs
law push forward (`residueWeight_tower`, `residueMass_tower`,
`residueDist_tower`), the coarse residue action **is** the
coarse-graining of the finer one (`residueAction_tower` —
concretely at theta, `4 → 2`, `theta_residueAction_tower`, with the
commuting triangle `8 → 4 → 2`, `theta_towerMap_triangle`), and the
partition-function factorization is transitive
(`classPartFn_tower`). **Resolution loss is priced**: one step
`q' = c·q` merges `c^{b₁}` classes per coarse class
(`card_h1TowerMap_fiber`), reversing it costs `b₁·log c` per sector
(`sectionCost_h1TowerMap`), and under the Gibbs law the loss is the
conditional entropy of the tower map — the difference of the two
`K + ⟨E⟩` decompositions (`residue_tower_entropy_chain`,
`residue_tower_condEntropy_eq`). And the **two prices are one
currency**: `H(q'|q) = b₁·log c − (Δ(q') − Δ(q))`
(`residue_tower_condEntropy_eq_defect` — via the generic Gibbs
inequality and the constant-fiber conditional-entropy bounds,
`FinDist.condEntropy_le_log`), strictly for any genuine refinement:
`0 < H(q'|q) < b₁·log c` and `Δ(q) < Δ(q')`
(`residue_tower_price_strict`; on theta at `4 → 2`: fibers of `4`,
cost `2·log 2`, `H(4|2) = 2·log 2 − (Δ(4) − Δ(2))` strict,
`theta_tower_price`). The price **composes**: conditional entropies
add along the tower by the unconditional chain rule
(`FinDist.condEntropy_comp`, `residue_tower_condEntropy_trans` —
`H(q″|q) = H(q″|q′) + H(q′|q)`), section costs add
(`sectionCost_h1TowerMap_trans`), and the deficit increments
telescope (`residue_tower_price_trans`), with the full triangle
consumed on theta (`theta_tower_price_triangle`:
`H(8|2) = H(8|4) + H(4|2) = 2·log 4 − (Δ(8) − Δ(2))`); the identity
step has zero price and zero cost (`residue_tower_price_id`,
`sectionCost_h1TowerMap_id`). The engine
behind every such bound is one definition — the **relative entropy**
(`FinDist.relativeEntropy`), whose admissibility condition is part
of the definition: the reference's full support
(`FinDist.FullSupport`) is a required argument, so the
mathematically invalid expression is unstatable. It is nonnegative,
strict for distinct distributions, zero exactly at equality, the
maximum-entropy defect is its uniform special case
(`defect_eq_relativeEntropy`), the conditional-entropy gap its
fiber-uniformization case (`relativeEntropy_uniformLift_map`), and
**data processing** holds: pushforward along a surjection can only
lose relative entropy (`relativeEntropy_map_le`), which makes the
tower deficit monotone (`residueDefect_mono`) with the Fourier modal
argument needed only for strictness. The entropy chain rule is one
unconditional engine (`entropy_eq_map_add_condEntropy`), its
conditional identity and composition laws corollaries
(`condEntropy_id`, `condEntropy_comp`). One
theorem carries the whole priced package on one explicit graph
(`theta_priced_faces`): partition-function gravity, complexity
gravity, priced time, the **complete residue, description, and pair
bridge packages**, and all three strict energy variances, at
`q = 2`.

**Uncertainty.** The Gibbs state's fluctuations are the model's
uncertainty, and they are theorems, not vocabulary: the variance of
any observable against the Boltzmann weights is nonnegative
(`gibbsVariance_nonneg`, `Meno/SectorAction.lean`), and strictly
positive as soon as the observable misses its own mean somewhere
(`gibbsVariance_pos`). On the intrinsic carrier the moments are
theorems, not hypotheses — both harmonic-energy moments are summable
(`summable_harmonicEnergy_gibbs`, `summable_harmonicEnergy_sq_gibbs`:
a polynomial-times-Gaussian bound against the half-energy Boltzmann
weight) — so the carrier's energy variance is **unconditionally**
nonnegative and **strictly positive** on any graph with cycles
(`classSectorAction_gibbsVariance_energy_nonneg`,
`classSectorAction_gibbsVariance_energy_pos`,
`Meno/BasisIndependence.lean`); the same strictness holds at every
finite resolution, for the residue, description, and pair actions
(`residueAction_gibbsVariance_E_pos` and its transports). And the
**fluctuation–dissipation identity** ties response to fluctuation
**at every rank** (`Meno/Fluctuation.lean`): the inverse-temperature
scaling of any positive-definite quadratic action has differentiable
partition function and mean energy — `Z′ = −M₁`, `M₁′ = −M₂`,
dominated at half temperature — with
**`d⟨E⟩/dβ = −Var_β(E)`**
(`hasDerivAt_meanEnergy_eq_neg_gibbsVariance`) and strict
dissipation from any nonzero-energy sector
(`meanEnergy_strictAntiOn`). Temperature is an **operation on the
carrier bundle** (`QuadLatticeAction.scale`,
`Meno/LatticeAction.lean`): identity, multiplicativity, equivalence
transport, and chart compatibility (`scale_one`, `scale_scale`,
`Equiv.scale`, `scale_chartAction`), with basis-free moments
computing through every chart and fluctuation–dissipation stated
**once for every bundled lattice action**
(`QuadLatticeAction.hasDerivAt_meanEnergy_eq_neg_gibbsVariance`,
`QuadLatticeAction.meanEnergy_strictAntiOn`). The intrinsic carrier
is a direct specialization (`classQuadActionβ :=
classQuadAction.scale`, with `β = 1` recovery proved **once on the
bundle** — sector action, partition function, Gibbs mass,
expectation, variance — and the scaled moments invariant under
`≃q`): `d⟨E⟩/dβ = −Var`
holds intrinsically
(`hasDerivAt_classMeanEnergy_eq_neg_gibbsVariance`), on any graph
with cycles the Gibbs mean energy strictly falls
(`classMeanEnergy_strictAntiOn`, `Meno/BasisIndependence.lean`), and
the genuinely **non-diagonal** theta carrier consumes both
(`theta_hasDerivAt_classMeanEnergy`,
`theta_classMeanEnergy_strictAntiOn`). The canonical scalar family
is the rank-one chart of the same engine, its public theorems
derived from it (`unitQuadAction`,
`hasDerivAt_quadraticMeanEnergy_eq_neg_gibbsVariance`,
`quadraticMeanEnergy_strictAntiOn`,
`quadraticObj_gibbsVariance_pos`, `Meno/Duality.lean`), with the
Cauchy–Schwarz route retained as named corroboration
(`M2_sq_lt_Z_mul_M4`).

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
├── Fluctuation.lean           Fluctuation–dissipation at every rank: β-scaling, d⟨E⟩/dβ = −Var(E), strict dissipation
├── LatticeAction.lean         The carrier bundle: real-extension positivity, charts, intrinsic dual & duality
├── LoopKernel.lean            Categorical presentation: End(base) as sector lattice
├── SectorPresentation.lean    MulEquiv coordinates; duality transport
├── Geodesic.lean              Lawvere-subadditive length class
├── HarmonicForm.lean          HarmonicGramData; variational builder; binding algebra
├── IncidenceGraph.lean        THE graph substrate: ∂, grad, Stokes (any ring); walks; components; gauge; H₁; b₁
├── GraphHomology.lean         Pure graph homology: every basis's derived data; keystones; Euler; the H₁ ≃ Dual H¹ pairing
├── ThetaGraph.lean            The theta graph: incidence data and raw integral cycle facts
├── GraphInstances.lean        Cycle, theta, genuine wedge: connectivity, Euler b₁, and the concrete lattice bases
├── PeriodHarmonic.lean        Least-norm-at-prescribed-periods machinery; cycle & wedge Gram forms
├── HarmonicClass.lean         Priced Gram data of a basis; intrinsic harmonic energy on H¹; variational identity
├── BasisIndependence.lean     Bases unimodularly related; partFn is the graph's; classQuadAction; H₁↔H¹ duality
├── WedgePresentation.lean     C5 acceptance witnesses: wedge matter; hand-built bases related to the fundamental one
├── Matter.lean                MatterSector = nonzero H¹ class; mass, positivity, trapped paradox
├── Binding.lean               2-complexes; the induced map; binding kills matter; exact spectral decomposition
├── ThetaBinding.lean          Binding at the theta graph: kill, rank drop `2 → 1`, removed weight
├── Basic.lean                 Abstract complexity hierarchy; pullback gravity (interface layer)
├── Instances.lean             Log-cardinality instance of the abstract hierarchy
├── UniformAction.lean         Type-level gravity realized on the uniform sector action
├── InfoRatchet.lean           Fiber information; the coding theorem; finite distributions and entropy gravity
├── ResolutionCount.lean       K1–K3 at every resolution; gauge count; section cost; the Gibbs residue distribution
├── Simplicial.lean            Walk/homotopy/Hodge model (independent corroborating route)
├── Groupoid.lean              Fundamental groupoid; geodesic instance; groupoid complexity
├── CycleHarmonic.lean         Flagship bridge: walk route ≡ period route; T-duality on C_n
├── ThetaHarmonic.lean         The theta graph: non-diagonal Gram derived from topology
├── Hodge.lean                 Graph partition functions (identified with the spine)
├── Duality.lean               Groupoid-facing duality wrappers (identified with the spine)
├── Zeta.lean                  Riemann functional equation through the spine's theta identification
└── Completion.lean            THE SEMANTIC COMPLETION CERTIFICATE: every Part-I acceptance signature, one field each, one derivation
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
