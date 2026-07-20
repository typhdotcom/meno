# Meno

*Structural Geometrodynamics in Lean 4*

Meno formalizes a speculative thesis:

> **A universe minimizes the cost of describing itself.**
> Gravity, matter, time, and uncertainty are faces of that minimization.

The carrier of the thesis is a **sector lattice with a
positive-definite quadratic action**: the lattice enumerates the
discrete sectors a system can occupy, the action prices them, the
Boltzmann sum reads the partition function, and duality, minimization,
and counting theorems connect the faces.

Everything below is a checked theorem — zero `sorry`, zero `axiom`
declarations, `lake build` green against Lean 4.26.0 and the pinned
Mathlib. The program, its completion discipline, and the per-goal
ledger live in [`PLAN.md`](PLAN.md); the completion certificate is
itself a Lean object ([The certificate](#the-certificate)).

---

## Why these pieces

**Complexity (`K`).** Every sector is weighted by `exp(−E)`; the
Boltzmann sum is the partition function `Z`, and `K = log Z` is the
cost of describing the system. Counting is the zero-energy special
case: a finite type describes for `log |A|`.

**The carrier.** For a graph the carrier is one bundled formal object —
`IncidenceGraph.classQuadAction`, the lattice `H¹(G;ℤ)` with the
polarized form `classForm`, positive definite on the real scalar
extension `ℝ ⊗[ℤ] H¹` (`classForm_self`, `classForm_chart`; integral
positivity and summability are derived, `Meno/LatticeAction.lean`).
`classSectorAction` is its analytic projection, and every
basis-coordinate quadratic action is a form-preserving chart of it
(`chartAction_h1Basis`).

**Sharing (gravity).** When two structures contain a common component,
encoding it once is cheaper, and the savings equal exactly the shared
component's complexity. Gravity is that identity — proved once, on any
domain with a unit, an equivalence, and an additive product.

**Obstruction (matter).** A nonzero cohomology class is locally
consistent and globally unsatisfiable — no potential realizes it. The
irreducible obstruction carries variational mass.

**Compression (time).** A map that merges states destroys information.
Its reverse descriptions are its sections, and their counted cost is
the arrow of time — derived as a coding theorem, not defined.

**Fluctuation (uncertainty).** The Gibbs state's variance is the
model's uncertainty, and its response to temperature is dissipation —
tied together by the fluctuation–dissipation identity.

---

## What is proved

### Duality

The Siegel–Poisson duality is proved once, in full generality —
non-diagonal Gram forms, any rank — and every duality in the program
flows through it: the carrier bundle carries an intrinsic, basis-free
dual; for a graph the dual **is topology** — priced `H₁` cycles
against harmonic `H¹` classes; and the concrete dualities are the
topological theorem read in concrete lattice bases. Riemann's
derivation of the functional equation runs through the same single
analytic source (`Meno/Zeta.lean`). And duality is **temperature,
inverted**: differentiating the scaled duality — once, then again —
yields the mean-energy and variance functional equations for every
bundled lattice action.

| Result | Statement |
| :--- | :--- |
| `QuadraticAction.duality` | `Z(π²·Q⁻¹) = √(det Q / π^r) · Z(Q)` at full generality, via multidimensional Poisson summation (`Meno/SiegelPoisson.lean`) |
| `QuadLatticeAction.duality` | The intrinsic duality, prefactor `√(disc/π^rank)` — no basis in the definition; outside its defining file the direct analytic invocation of `QuadraticAction.duality` occurs exactly once, here (its in-file scalar/real corollaries in `Meno/SiegelPoisson.lean` sit upstream of the bundle in the import order) |
| `chartAction_dual`, `disc_eq`, `disc_dual` | Every dual basis charts the intrinsic dual as the coordinate dual; the discriminant is basis-independent, with the reciprocal law `disc(Q^∨) = π^{2·rank}/disc(Q)` |
| `dualDual`, `duality_dualDual` | The double dual is a bundled form-preserving involution — rank, energy, discriminant, and partition function transported — and applying the duality twice cancels the prefactors |
| `basisGramData_duality` | The per-chart coordinate duality, as a corollary |
| `cyclesDualEquiv` | Period evaluation is a perfect pairing `H₁(G;ℤ) ≃ Dual ℤ H¹(G;ℤ)` — well-defined by Stokes, bijective by the keystone; the transported form is `π²` times the unit-edge chain pairing |
| `cycle_harmonic_duality` | `Z(priced cycles) = √(disc/π^{b₁})·Z(harmonic classes)` (`Meno/BasisIndependence.lean`) |
| `classActionEquivCycleDual` | `classQuadAction ≃q cycleAction.dual`, through the equivalence calculus — `refl`/`trans`/`symm`/`dual` with identity, associativity, and inverse laws (`trans_symm`, `symm_trans`), contravariant dual functoriality (`dual_trans`, `dual_refl`, `dual_symm`) — with the two prefactors multiplying to one (`dual_prefactor_mul_one`) |
| `theta_siegelPoisson_duality`, `partitionFn_T_duality_via_spine` | The genuinely non-diagonal theta duality and the cycle-graph T-duality are `cycle_harmonic_duality` read in the concrete bases — no bespoke modular input |
| `QuadraticAction.duality_via_lattice`, `dualVia_partFn_duality` | A coordinate action embeds canonically (`ofQuadraticAction`), so the coordinate duality is a corollary of the intrinsic one; the categorical duality consumes the corollary (`Meno/SectorPresentation.lean`) |
| `disc_scale`, `scale_dual`, `scaled_duality` | Scaling multiplies the discriminant by `β^rank`, the dual of the scaled bundle is the inverse-scaled dual — `(β·Q)∨ = β⁻¹·(Q∨)`, an equality of bundles — and `Z_{Q∨}(β⁻¹) = √(β^rank·disc/π^rank)·Z_Q(β)` |
| `QuadLatticeAction.meanEnergy_T_dual` | `⟨E⟩_Q(β) + β⁻²·⟨E⟩_{Q∨}(β⁻¹) = rank/(2β)` — differentiated once, for every bundled lattice action |
| `gibbsVariance_T_dual`, `meanEnergy_self_dual` | Differentiating again — the established derivative theorems, no new lattice-sum differentiation — forces `Var_Q(β) + 2β⁻³·⟨E⟩_{Q∨}(β⁻¹) − β⁻⁴·Var_{Q∨}(β⁻¹) = rank/(2β²)`; a self-dual bundle sits at `⟨E⟩(1) = rank/4` |
| `classMeanEnergy_T_dual`, `classGibbsVariance_T_dual`, `classMeanEnergy_self_dual` | Both laws lock harmonic `H¹` to priced `H₁` at reciprocal temperatures — `⟨E⟩_{H¹}(β) + β⁻²·⟨E⟩_{H₁}(β⁻¹) = b₁/(2β)` |
| `theta_classMeanEnergy_T_dual`, `theta_gibbsVariance_T_dual` | Consumed on the non-diagonal theta carrier: `= 1/β`, `= 1/β²` |
| `quadraticMeanEnergy_T_dual`, `quadraticMeanEnergy_self_dual` | The scalar functional equation and the self-dual value `⟨k²⟩_π = 1/(4π)` as the unit instance (`Meno/Duality.lean`) |

### Topology, intrinsically

Every finite multigraph (`IncidenceGraph`) carries an intrinsic
integral cycle lattice `H₁(G;ℤ) = ker ∂ℤ` and cohomology
`H¹(G;ℤ) = ℤ-cochains ⧸ gradients`. A presentation **is** a lattice
basis `Module.Basis (Fin n) ℤ G.cycleLattice` — no presentation
structure, no stored fields: closedness, real/integer independence,
period realizability, integral potentials, spanning, and the keystone
equivalences are all theorems of any basis (`Meno/GraphHomology.lean`).
The topology layer itself is deliberately unpriced.

| Result | Statement |
| :--- | :--- |
| `IncidenceGraph.cycleBasis` | The fundamental basis equips *every* finite graph, via a saturation argument, the PID structure theorem, and a walk-integration engine |
| `h1QuotEquiv` | `H¹(G;ℤ) ≃ ℤ^{b₁}` for every finite graph |
| `b1_eq` | Euler's formula `b₁ = \|E\| − \|V\| + c`, proved in the topology layer |
| `finrank_gauge`, `period_eq_zero_iff_exists_grad` | The gauge theorem `dim(ker grad) = #components` — connectivity governs gauge, never exactness |
| `gramOf_cyclesR_posDef` | The positive-definite unit-edge Gram is a theorem of the **priced** layer (`Meno/PeriodHarmonic.lean`) |

### Basis independence

Nothing the physics reads depends on a choice of basis.

| Result | Statement |
| :--- | :--- |
| `card_eq_b1` | Every lattice basis has exactly `b₁` elements |
| `exists_unimodular_relating` | Any two bases are unimodularly related (`Meno/BasisIndependence.lean`) |
| `exists_int_coords` | Primitivity is forced |
| `basisGramData_partFn`, `IncidenceGraph.partFn`, `MatterSector.mass_chart` | Energies, masses, and the partition function are functions of the graph alone |

### Matter

A matter sector is a nonzero class of `H¹(G;ℤ)` (`MatterSector`,
`Meno/Matter.lean`); its mass is the intrinsic harmonic energy
(`IncidenceGraph.harmonicEnergy`). **Matter is trapped paradox** —
locally consistent, globally unsatisfiable.

| Result | Statement |
| :--- | :--- |
| `harmonicEnergy_pos` | Mass is positive for every nonzero class |
| `harmonicEnergy_isLeast` | Mass is attained as the least cochain energy among realizers |
| `energy_eq_harmonicEnergy` | Every presentation computes it |
| `not_gradient` | Every cochain realizing a nonzero class admits no potential |
| `exists_matter` | Nontrivial topology forces matter |
| `annihilation` | Annihilation releases the pair's full rest mass |

### Binding

Attaching a 2-cell along a cycle changes the space and kills the
matter that wrapped it (`Meno/Binding.lean`). The theorem that
releases an *energy* equal to a rest mass is algebraic annihilation.

| Result | Statement |
| :--- | :--- |
| `restrict_injective`, `range_restrict` | The induced restriction `H¹(X) → H¹(G)` is injective, with image exactly the classes annihilating the attached cycles |
| `binding_kills_matter` | A sector with nonzero period around a filled face has **no image at all** |
| `attach_h1`, `finrank_attach_h1Homology` | On homology, `H₁(X) = H₁(G)/⟨c⟩` — free of rank `b₁ − 1` for primitive `c` |
| `TwoComplex.energy_isLeast` | Survivors keep their exact mass |
| `attach_partFn_add_le`, `attach_partFn_lt` | The partition function strictly drops — by at least the killed sector's entire Boltzmann weight |
| `TwoComplex.partFn_add_killed` | The spectrum *partitions exactly* into survivors and casualties |
| `theta_binding_kills`, `theta_removed_weight` | Concretely: filling the theta graph's first cycle kills its `1/3`-mass sector and costs the spectrum at least `exp(−1/3)` (`Meno/ThetaBinding.lean`) |

### Time and information

Descriptions at finite resolution are counted exactly, and the ratchet
is **derived, not defined**: reverse-description cost *equals* fiber
information as a coding theorem. The numerical costs are defined only
on finite types — `Nat.card`'s junk zero on infinite types is refused,
not exploited. And the information face inhabits the thesis's **one
integral carrier**, not merely its API: the resolution-`q` residue is
exactly the carrier's quotient, and time's arrow is priced against the
action, not only against counts (`Meno/InfoRatchet.lean`,
`Meno/ResolutionCount.lean`).

| Result | Statement |
| :--- | :--- |
| `card_quotient` | K1: descriptions at resolution `q` modulo local re-description number exactly `q^{b₁}` — every modulus, every finite graph |
| `log_card_split` | K2: description cost splits as gauge + incompressible residue |
| `card_fiber`, `card_gauge` | K3: every compression fiber is uniform, with gauge group `q^{\|E\|−b₁}` — Euler's formula read as a factorization of counts |
| `card_sections`, `log_card_sections` | The reverse descriptions of a map are its sections, counted exactly; reverse-description cost equals fiber information |
| `sectionCost_compression`, `recoveryCost_compression` | The coding theorem, for the global gauge-fixing and for a single class |
| `sectionCostE_eq_top_iff`, `sectionCostE_eq_zero_iff`, `recoveryCostE_eq_top_iff` | The extended cost is `⊤` when no section exists, zero cost characterizes bijections, unproducible outputs are priced at `⊤` |
| `sectionCostE_eq_sum_recoveryCostE` | The extended coding identity holds on both sides of the boundary — an impossible inverse is not free |
| `section_not_surjective_of_not_injective`, `simplicial_ratchet` | Where fibers are infinite, the cardinality-free form: a section of a non-injective map always misses states |
| `classSectorAction`, `classSectorAction_energy`, `basisGramData_partFn_eq_classSectorAction` | The intrinsic sector action is `H¹(G;ℤ)` with the harmonic energy; every basis-coordinate action is a chart of it (`Meno/BasisIndependence.lean`) |
| `h1ResQuotEquiv`, `latticeQuotEquivQ_h1Res` | Coefficient reduction `h1Res` is surjective with kernel `q·H¹(G;ℤ)`, giving `H¹(G;ℤ)⧸q·H¹(G;ℤ) ≃ H¹(G;ZMod q)`, coordinates commuting with the keystones |
| `uniformAction_h1ResQuot_complexity`, `uniformComplexity_split_carrier` | The residue's uniform complexity `b₁ · log q` and the K2 split, derived through that reduction |
| `residueMass`, `descriptionMass` | The carrier's intrinsic Gibbs distribution pushes forward to the residue — positive, normalized, computed by every basis chart — and lifts uniformly through the compression |
| `descriptionEntropy_split` | Description entropy = residue entropy + the gauge log |
| `sectionCost_carrierCompression_div`, `sectionCost_carrierCompression_action` | The per-sector gauge-fixing cost is exactly that conditional entropy — at the action level, exactly `K(descriptionAction) − K(residueAction)` |
| `SectorAction.sectionCost_uniformLift` | The generic priced time law it specializes: `sectionCost f / \|Λ\| = K(uniformLift) − K(base)` |

### Gravity

There is **one gravity theorem**: merging two structures that share a
component saves exactly the shared component's complexity. It is
stated once, on any domain with a unit, an equivalence, and an
additive product, and every gravity identity in the program is that
theorem at an instance — **counting** (finite types under
log-cardinality), **pricing** (sector actions under complexity), and
the **groupoid**. On the graph carrier the identity holds priced by
the action itself, its entropy form is a corollary of the priced
calculus, pricing and counting are numerically bridged with the same
deficit at all three levels, the decomposition is strict wherever
there is anything to price, and the resolutions form a tower whose
losses are priced in one currency.

#### The engine and its instances

| Result | Statement |
| :--- | :--- |
| `SGD.AdditiveComplexityOn.algebraic_gravity` | **The one engine**: `C(d⊗(f⊗g)) + C(d) = C(d⊗f) + C(d⊗g)` on any domain with a unit, an equivalence, and an additive product (`Meno/Basic.lean`) |
| `SGD.gravity` | The engine at the type-level `logCard` instance; the sigma-fiber decompositions supply `A ×_D B ≃ D × (F × G)`, `A ≃ D × F`, `B ≃ D × G` |
| `uniformAction`, `logCard_eq_uniformComplexity` | A finite type is a sector lattice with zero energy — `Z = \|A\|`, `K = log \|A\|` — bridging counting into the priced world (`Meno/UniformAction.lean`) |
| `gravity_logCard`, `refactoring_bound_logCard` | The counting corollaries, invoking the abstract theorems |
| `SectorAction.complexity_gravity` | **Pricing**: `K(coupling) + K(base) = K(lift) + K(lift)` — the engine at the sector-action instance `instAdditiveComplexityOnSectorAction` (complexity, energy-preserving equivalence, independent product; `Meno/InfoRatchet.lean`) |
| `coupling_energyEquiv`, `uniformLift_energyEquiv` | The decompositions supplying the shapes: `coupling ≈ base ⊗ (free ⊗ free)`, `lift ≈ base ⊗ free` |
| `partFn_gravity` | The partition-function form — the exponential of the complexity form |
| `GroupoidObj.shared_component_identity` | The same engine at the groupoid instance (`Meno/Groupoid.lean`) |

#### Gravity priced on the carrier

The residue action is *derived*, not reconstructed, and descriptions
and pairs are actions too (`Meno/InfoRatchet.lean`,
`Meno/ResolutionCount.lean`).

| Result | Statement |
| :--- | :--- |
| `SectorAction.coarseGrain`, `residueAction` | The residue action is the coarse-graining of the harmonic action at the quotient map |
| `residueWeight`, `residueMass_eq_residueWeight_div` | Unnormalized coset weights `W ξ = ∑_{κ mod q = ξ} exp(−E_harm κ)`, with `residueMass = W/Z` |
| `residueAction_E_freeEnergy` | Energy is the effective free-energy difference `F ξ − F 0` with `F = −log W` |
| `classPartFn_eq_residueWeight_mul`, `classComplexity_residue_split` | The harmonic partition function factorizes, `Z = W 0 · Z_residue`, with the complexity decomposition |
| `SectorAction.uniformLift`, `SectorAction.coupling` | The priced uniform lift and priced shared-base coupling |
| `uniformLift_gibbsDist`, `coupling_gibbsDist` | Their Gibbs laws are exactly the `FinDist` constructions |
| `descriptionAction`, `pairAction` | The carrier instances (`descriptionAction_gibbsDist`, `pairAction_gibbsDist`), both coupling marginals the description distribution (`pairDist_fst`, `pairDist_snd`), moments transported untouched (`descriptionAction_gibbsExpect_E`, `pairAction_gibbsVariance_E`) |
| `carrier_gravity_partFn`, `carrier_gravity_action` | Gravity on the carrier, priced: `Z(pair)·Z(residue) = Z(description)²` and `K(pair) + K(residue) = 2·K(description)` |
| `SectorAction.entropy_gravity`, `carrier_gravity_entropy` | The entropy form `H(pair) + H(residue) = 2·H(description)` is a corollary of the priced calculus — the four Gibbs entropy splits, complexity gravity, and the expectation transports — instantiated at the residue action |
| `carrier_gravity_complexity` | The uniform complexity identity: the priced identity plus the common deficit — proved once |

#### The bridge and its strictness

| Result | Statement |
| :--- | :--- |
| `FinDist.defect` | The uniform entropy defect `Δ(P) = log\|X\| − H(P)` — nonnegative by maximum entropy, zero exactly at uniform, preserved by lifting and coupling |
| `uniformComplexity_residue_bridge`, `uniformComplexity_description_bridge`, `uniformComplexity_pair_bridge` | `K_uniform = K(action) + ⟨E⟩ + Δ` at all three levels **with the same deficit**, through the Gibbs entropy split `H = K + ⟨E⟩` (`SectorAction.entropy_gibbs`) |
| `residueAction_E_eq_zero_iff`, `residueAction_E_pos_iff` | Energy vanishes exactly at the zero class and is strictly positive exactly off it |
| `residueMass_lt_residueMass_zero` | The zero class is strictly modal — through the single Gaussian Fourier engine of Siegel–Poisson (`hasSum_gaussFourier_periodization`, `periodization_lt_periodization_zero`, `Meno/SiegelPoisson.lean`) |
| `uniformComplexity_residue_bridge_pos` | On every graph with cycles at every resolution `1 < q`, all three bridge terms are strictly positive — subsuming `residueDist_ne_uniform` and `residueDefect_pos` |
| `uniformComplexity_description_bridge_pos`, `uniformComplexity_pair_bridge_pos` | The strictness reaches the description and pair bridges |
| `theta_residue_bridge_pos`, `theta_residueDefect_pos` | Concretely at the theta graph with `q = 2` |

#### The resolution tower

| Result | Statement |
| :--- | :--- |
| `coarseGrain_id`, `coarseGrain_comp` | Coarse-graining has identity and composition laws |
| `h1TowerMap`, `h1TowerMap_comp` | For `q ∣ q'` the finer reduction maps canonically onto the coarser — identity, composition, witness-independence, and surjectivity laws |
| `residueWeight_tower`, `residueMass_tower`, `residueDist_tower` | Residue weights, masses, and the Gibbs law push forward |
| `residueAction_tower`, `residueDist_tower_trans`, `residueAction_tower_trans` | The coarse residue action **is** the coarse-graining of the finer one; distributions and actions compose across the tower |
| `theta_residueAction_tower`, `theta_towerMap_triangle` | Concretely at theta, `4 → 2`, with the commuting triangle `8 → 4 → 2` |
| `classPartFn_tower` | The partition-function factorization is transitive |
| `card_h1TowerMap_fiber`, `sectionCost_h1TowerMap` | **Resolution loss is priced**: one step `q' = c·q` merges `c^{b₁}` classes per coarse class; reversing it costs `b₁·log c` per sector |
| `residue_tower_entropy_chain`, `residue_tower_condEntropy_eq` | Under the Gibbs law the loss is the conditional entropy of the tower map — the difference of the two `K + ⟨E⟩` decompositions |
| `residue_tower_condEntropy_eq_defect` | **The two prices are one currency**: `H(q'\|q) = b₁·log c − (Δ(q') − Δ(q))` — via the generic Gibbs inequality and the constant-fiber bounds (`FinDist.condEntropy_le_log`) |
| `residue_tower_price_strict`, `theta_tower_price` | Strict for any genuine refinement — `0 < H(q'\|q) < b₁·log c` and `Δ(q) < Δ(q')`; on theta at `4 → 2`: fibers of `4`, cost `2·log 2` |
| `FinDist.condEntropy_comp`, `residue_tower_condEntropy_trans` | Conditional entropies add along the tower by the unconditional chain rule: `H(q″\|q) = H(q″\|q′) + H(q′\|q)` |
| `sectionCost_h1TowerMap_trans`, `residue_tower_price_trans` | Section costs add; the deficit increments telescope |
| `theta_tower_price_triangle` | The full triangle consumed on theta: `H(8\|2) = H(8\|4) + H(4\|2) = 2·log 4 − (Δ(8) − Δ(2))` |
| `residue_tower_price_id`, `sectionCost_h1TowerMap_id` | The identity step has zero price and zero cost |

#### The relative-entropy engine

One definition is behind every such bound, and its admissibility
condition is part of the statement.

| Result | Statement |
| :--- | :--- |
| `FinDist.relativeEntropy`, `FinDist.FullSupport` | The reference's full support is a *required argument* — the mathematically invalid expression is unstatable |
| `defect_eq_relativeEntropy`, `relativeEntropy_uniformLift_map` | Nonnegative, strict for distinct distributions, zero exactly at equality; the maximum-entropy defect is its uniform special case, the conditional-entropy gap its fiber-uniformization case |
| `relativeEntropy_map_le`, `residueDefect_mono` | **Data processing**: pushforward along a surjection can only lose relative entropy — the tower deficit is monotone, the Fourier modal argument needed only for strictness |
| `entropy_eq_map_add_condEntropy`, `condEntropy_id`, `condEntropy_comp` | The entropy chain rule is one unconditional engine; its conditional identity and composition laws are corollaries |
| `theta_priced_faces` | One theorem carries the whole priced package on one explicit graph at `q = 2`: partition-function gravity, complexity gravity, priced time, the complete residue, description, and pair bridge packages, and all three strict energy variances |

### Uncertainty

The Gibbs state's fluctuations are the model's uncertainty, and they
are theorems, not vocabulary. Fluctuation–dissipation is stated once
for every bundled lattice action, and temperature is an operation on
the carrier bundle (`Meno/Fluctuation.lean`, `Meno/LatticeAction.lean`).

| Result | Statement |
| :--- | :--- |
| `gibbsVariance_nonneg`, `gibbsVariance_pos` | The variance of any observable against the Boltzmann weights is nonnegative, and strictly positive as soon as the observable misses its own mean somewhere (`Meno/SectorAction.lean`) |
| `summable_harmonicEnergy_gibbs`, `summable_harmonicEnergy_sq_gibbs` | Both harmonic-energy moments are summable — a polynomial-times-Gaussian bound against the half-energy Boltzmann weight |
| `classSectorAction_gibbsVariance_energy_nonneg`, `classSectorAction_gibbsVariance_energy_pos` | The carrier's energy variance is **unconditionally** nonnegative and **strictly positive** on any graph with cycles (`Meno/BasisIndependence.lean`) |
| `residueAction_gibbsVariance_E_pos` | The same strictness at every finite resolution — residue, description, and pair actions, with its transports |
| `hasDerivAt_meanEnergy_eq_neg_gibbsVariance`, `meanEnergy_strictAntiOn` | **Fluctuation–dissipation**: `d⟨E⟩/dβ = −Var_β(E)` — `Z′ = −M₁`, `M₁′ = −M₂`, dominated at half temperature — with strict dissipation from any nonzero-energy sector (`Meno/Fluctuation.lean`) |
| `QuadLatticeAction.scale` | Temperature as an operation on the carrier bundle: identity, multiplicativity, equivalence transport, chart compatibility (`scale_one`, `scale_scale`, `Equiv.scale`, `scale_chartAction`) |
| `QuadLatticeAction.hasDerivAt_meanEnergy_eq_neg_gibbsVariance`, `QuadLatticeAction.meanEnergy_strictAntiOn` | Stated **once for every bundled lattice action**, basis-free moments computing through every chart |
| `classQuadActionβ`, `hasDerivAt_classMeanEnergy_eq_neg_gibbsVariance`, `classMeanEnergy_strictAntiOn` | The intrinsic carrier is a direct specialization (`classQuadActionβ := classQuadAction.scale`, `β = 1` recovery proved once on the bundle, scaled moments invariant under `≃q`): `d⟨E⟩/dβ = −Var` holds intrinsically, and on any graph with cycles the Gibbs mean energy strictly falls |
| `theta_hasDerivAt_classMeanEnergy`, `theta_classMeanEnergy_strictAntiOn` | Both consumed on the genuinely non-diagonal theta carrier |
| `unitQuadAction`, `hasDerivAt_quadraticMeanEnergy_eq_neg_gibbsVariance`, `quadraticMeanEnergy_strictAntiOn`, `quadraticObj_gibbsVariance_pos` | The canonical scalar family is the rank-one chart of the same engine, its public theorems derived from it (`Meno/Duality.lean`) |
| `M2_sq_lt_Z_mul_M4` | The Cauchy–Schwarz route retained as named corroboration |

### Geometry

Every symmetric simplicial complex's fundamental groupoid carries a
Lawvere-subadditive geodesic length, and on the `n`-cycle the
combinatorial and harmonic masses meet.

| Result | Statement |
| :--- | :--- |
| `simplicialGeodesic` | The geodesic length instance (`Meno/Groupoid.lean`) |
| `geodesic_harmonic_duality` | `n · (1/n) = 1` |

---

## The certificate

All twelve goals of the Completion Path are closed, and the closure
itself is a **Lean object**: the semantic completion certificate
`MenoSemanticCompletion` (`Meno/Completion.lean`) is derived
mechanically from the plan's Part I — every C1–C10 acceptance
signature is a field in exactly one of **nine law packages**, and
`menoSemanticCompletion` is its one derivation, by direct
named-theorem assignment. The graph-dependent packages are quantified
over every finite multigraph `G`, the thermal package over every
bundled lattice action `Q`, the information package over every finite
distribution `P`; the coding-gravity package is **graph-free** — no
vacuous quantifier — and the flagship package pins the concrete
consumers.

| Package | Covers | Derivation |
| :--- | :--- | :--- |
| `GraphTopologyLaws` — `∀ G` | C1–C2: gauge, Euler, independence, spanning, integral coordinates | `graphTopologyLaws` |
| `HarmonicCarrierLaws` — `∀ G` | C3–C4: rank well-definedness, unimodular transport, the basis-free partition function, the variational identity, positive energy | `harmonicCarrierLaws` |
| `MatterBindingLaws` — `∀ G` | C6–C7: the intrinsic matter facts and the generic binding theorems on 2-complexes | `matterBindingLaws` |
| `ResolutionCodingLaws` — `∀ G` | C8–C9, graph-dependent: K1–K3 at every modulus, gauge counting, compression sections and costs, per-class recovery | `resolutionCodingLaws` |
| `CodingGravityLaws` — graph-free | C8–C9, generic: section counting, the coding theorem with its `ℝ≥0∞` boundary, the `logCard` bridge, gravity and the refactoring bound at the counting instance, the priced gravity and time identities | `codingGravityLaws` |
| `ThermalDualityLaws` — `∀ Q` | The scale algebra, the dual involution, temperature inversion, and the partition, mean-energy, and variance functional equations with the self-dual fixed point | `thermalDualityLaws` |
| `InformationLaws` — `∀ P` | Pushforward functoriality, the unconditional entropy chain rule, the support-aware Gibbs inequality, data processing | `informationLaws` |
| `ResolutionTowerLaws` — `∀ G` | The tower category, pushforwards, additive prices and costs, telescoping monotone deficits, strict pricing of genuine refinements | `resolutionTowerLaws` |
| `FlagshipLaws` | C5 and the concrete consumers: cycle, wedge, and theta results — bases, counts, dualities, priced faces, tower prices, the thermal circle, the geodesic–harmonic duality | `flagshipLaws` |

Scope, honestly: the certificate enforces **statement coverage** —
deleting an acceptance theorem breaks the derivation. Proof provenance
is enforced by the direct-assignment discipline and review. Closure in
full is a conjunction: the certificate compiles, the import DAG
matches Part I, the recorded deletions stay deleted, `lake build Meno`
is green with zero `sorry`/`axiom`/warnings, and the derivation routes
and public claims are held to substantive review. The four machine
legs are re-checked by every build; the fifth is a standing
discipline, not a one-time event. Audit chronology lives in
[`PLAN.md`](PLAN.md) Part II.

---

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
├── Basic.lean                 Abstract complexity hierarchy; THE ONE GRAVITY ENGINE (algebraic_gravity); gravity at the counting instance
├── Instances.lean             Log-cardinality instance of the abstract hierarchy
├── UniformAction.lean         The uniform sector action; the pricing instance of the gravity engine; the logCard bridge
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

---

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

---

## Build

Requires Lean 4.26.0 and the pinned Mathlib.

```bash
lake build
```
