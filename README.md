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
Mathlib. The program now underway — the Obstruction Program, with
its four-anchor discipline — lives in [`PLAN.md`](PLAN.md); the
first program's kernel-checked leg is a Lean object ([The coverage
bundle](#the-coverage-bundle)), scheduled for replacement by the
plan's dichotomy theorem.

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

**Sharing (gravity).** When two descriptions couple over a shared
base, encoding the base once is cheaper — and the defect from
exactness is the log-correlation of the two descriptions' redundancy
profiles (`gravity_defect`). Sharing saves exactly the base
precisely at zero covariance; counting is the zero-energy special
case.

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
| `dualDual`, `duality_dualDual`, `partFn_dualDual` | The double dual is a bundled form-preserving involution — rank, energy, discriminant, and partition function transported — and applying the duality twice cancels the prefactors |
| `basisGramData_duality` | The per-chart coordinate duality, as a corollary |
| `cyclesDualEquiv` | Period evaluation is a perfect pairing `H₁(G;ℤ) ≃ Dual ℤ H¹(G;ℤ)` — well-defined by Stokes, bijective by the keystone; the transported form is `π²` times the unit-edge chain pairing |
| `cycle_harmonic_duality` | `Z(priced cycles) = √(disc/π^{b₁})·Z(harmonic classes)` (`Meno/BasisIndependence.lean`) |
| `classActionEquivCycleDual` | `classQuadAction ≃q cycleAction.dual`, through the equivalence calculus — `refl`/`trans`/`symm`/`dual` with identity, associativity, and inverse laws (`Equiv.trans_assoc`, `trans_symm`, `symm_trans`), contravariant dual functoriality (`dual_trans`, `dual_refl`, `dual_symm`) — with the two prefactors multiplying to one (`dual_prefactor_mul_one`) |
| `theta_siegelPoisson_duality`, `partitionFn_T_duality_via_spine` | The genuinely non-diagonal theta duality and the cycle-graph T-duality are `cycle_harmonic_duality` read in the concrete bases — no bespoke modular input |
| `thetaGram_offDiag_ne_zero` | The theta Gram's off-diagonal is `−1/6 ≠ 0` — the non-diagonality of the flagship carrier is a theorem, not a remark |
| `QuadraticAction.selfDual`, `QuadraticAction.selfDual_iff` | Self-duality of a bundled action is the quadratic condition `Q² = π²·1` (`Meno/SiegelPoisson.lean`) |
| `QuadraticAction.dualityFlow`, `QuadraticAction.dualityFlow_eq`, `QuadraticAction.dualityFlow_eq_zero_iff` | The duality flow `K − K∨ = −½·log(det Q/π^r)` at every rank — zero exactly on the critical determinant `det Q = π^r` |
| `exists_dualityFlow_eq_zero_not_selfDual` | Negative result: at rank 2 the flow vanishes without self-duality — the critical surface is strictly bigger than the fixed locus |
| `QuadraticAction.duality_via_lattice`, `dualVia_partFn_duality` | A coordinate action embeds canonically (`ofQuadraticAction`), so the coordinate duality is a corollary of the intrinsic one; the categorical duality consumes the corollary (`Meno/SectorPresentation.lean`) |
| `disc_scale`, `scale_dual`, `scaled_duality` | Scaling multiplies the discriminant by `β^rank`, the dual of the scaled bundle is the inverse-scaled dual — `(β·Q)∨ = β⁻¹·(Q∨)`, an equality of bundles — and `Z_{Q∨}(β⁻¹) = √(β^rank·disc/π^rank)·Z_Q(β)` |
| `QuadLatticeAction.meanEnergy_T_dual` | `⟨E⟩_Q(β) + β⁻²·⟨E⟩_{Q∨}(β⁻¹) = rank/(2β)` — differentiated once, for every bundled lattice action |
| `gibbsVariance_T_dual`, `meanEnergy_self_dual` | Differentiating again — the established derivative theorems, no new lattice-sum differentiation — forces `Var_Q(β) + 2β⁻³·⟨E⟩_{Q∨}(β⁻¹) − β⁻⁴·Var_{Q∨}(β⁻¹) = rank/(2β²)`; a self-dual bundle sits at `⟨E⟩(1) = rank/4` |
| `classMeanEnergy_T_dual`, `classGibbsVariance_T_dual`, `classMeanEnergy_self_dual` | Both laws lock harmonic `H¹` to priced `H₁` at reciprocal temperatures — `⟨E⟩_{H¹}(β) + β⁻²·⟨E⟩_{H₁}(β⁻¹) = b₁/(2β)` |
| `theta_classMeanEnergy_T_dual`, `theta_gibbsVariance_T_dual` | Consumed on the non-diagonal theta carrier: `= 1/β`, `= 1/β²` |
| `quadraticMeanEnergy_T_dual`, `quadraticMeanEnergy_self_dual` | The scalar functional equation and the self-dual value `⟨k²⟩_π = 1/(4π)` as the unit instance (`Meno/Duality.lean`) |
| `scalarPartFn_eq_jacobiTheta` | The scalar partition function **is** Jacobi theta on the imaginary axis — the spine's Boltzmann sum identified with Mathlib's modular object (`Meno/QuadraticAction.lean`) |
| `scalarPartFn_duality`, `scalarPartFn_duality_via_poisson` | One scalar T-duality, two independent proof traditions — the modular `S`-transformation and Poisson summation — corroborating each other inside the spine |
| `menoMellin`, `meno_mellin` | The Mellin transform of the spine's excess partition function: `∫_{α>0} (Z(α)−1)·α^{s−1} = 2·Γ(s)·ζ(2s)` for `s > 1/2` (`Meno/Zeta.lean`) |
| `meno_zeta_functional_equation_real` | Riemann's reflection `π^{−s}·2Γ(s)ζ(2s) = π^{−(1/2−s)}·M(1/2−s)` — the functional equation of `ζ`, derived through the spine's T-duality residual |
| `menoSpectralIntegral`, `riemannZeta_three_eq_meno_spectral_integral` | `ζ(3) = (1/√π)·∫_{α>0} (Z(α)−1)·√α` — Apéry's constant is a spectral integral of the spine |

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
| `cochainQuotEquivR`, `finrank_cochainQuotR` | The real keystone: `(E → ℝ) ⧸ im(grad) ≃ ℝ^{b₁}`, with the dimension count |
| `spanning_of_card_eq_b1` | The Euler criterion for spanning: any `b₁`-many independent closed edge-vectors span every closed edge-vector |
| `thetaGraph_b1'`, `wedgeGraph_b1'` | The concrete Betti numbers `b₁(θ) = 2` and `b₁(C_{n₁} ∨ C_{n₂}) = 2`, recomputed through `card_eq_b1` — corroborating the Euler computations (`Meno/GraphInstances.lean`) |
| `finrank_gauge`, `period_eq_zero_iff_exists_grad` | The gauge theorem `dim(ker grad) = #components` — connectivity governs gauge, never exactness |
| `gramOf_cyclesR_posDef` | The positive-definite unit-edge Gram is a theorem of the **priced** layer (`Meno/PeriodHarmonic.lean`) |

### Basis independence

Nothing the physics reads depends on a choice of basis.

| Result | Statement |
| :--- | :--- |
| `card_eq_b1` | Every lattice basis has exactly `b₁` elements |
| `exists_unimodular_relating` | Any two bases are unimodularly related (`Meno/BasisIndependence.lean`) |
| `cycleLatticeBasis_unimodular_related`, `wedgeLatticeBasis_unimodular_related`, `thetaLatticeBasis_unimodular_related` | The hand-built cycle, wedge, and theta bases are unimodularly related to the fundamental basis — the concrete acceptance witnesses |
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
| `MatterSector.mass_pos`, `MatterSector.mass_isLeast` | The same two facts read at the sector level: every matter sector's mass is positive and variationally attained |
| `energy_eq_harmonicEnergy` | Every presentation computes it |
| `not_gradient` | Every cochain realizing a nonzero class admits no potential |
| `exists_matter` | Nontrivial topology forces matter |
| `wedge_exists_matter`, `wedgeMatter₁_mass` | Concretely on the genuine wedge: matter exists, and the first-cycle sector weighs exactly `1/n₁` (`Meno/CycleHarmonic.lean`) |
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
| `theta_attach_finrank` | Concretely: filling the theta graph's first cycle leaves `H₁` free of rank exactly `1` (`Meno/ThetaBinding.lean`) |
| `TwoComplex.energy_isLeast` | Survivors keep their exact mass |
| `attach_partFn_add_le`, `attach_partFn_lt` | The partition function strictly drops — by at least the killed sector's entire Boltzmann weight |
| `TwoComplex.partFn_add_killed` | The spectrum *partitions exactly* into survivors and casualties |
| `theta_binding_kills`, `theta_removed_weight` | Concretely: filling the theta graph's first cycle kills its `1/3`-mass sector and costs the spectrum at least `exp(−1/3)` (`Meno/ThetaBinding.lean`) |
| `ofCycles_interaction_fin_two`, `ofCycles_bindingEnergy_fin_two` | **The closed form at `b₁ = 2`** (G6, `Meno/BindingSign.lean`): the priced Gram is the inverse chain Gram (`basisGramData_gram`), so the unit sectors' interaction is `−⟨c₁,c₂⟩/det` and their binding energy `2⟨c₁,c₂⟩/det`, with the chain determinant positive |
| `bindingEnergyClass`, `bindingEnergyClass_chart` | **The intrinsic binding energy** of two `H¹` classes, through `harmonicEnergy` — invariant under the unimodular action by construction, computed by every basis chart |
| `binding_attractive_iff`, `theta_binding_attractive_class` | **THE BINDING SIGN CRITERION** (G6): binding is attraction **exactly when the cycles overlap with consistent orientation** — `0 < bindingEnergyClass ↔ 0 < ⟨c₁,c₂⟩`; with positive overlap there is no non-attractive joint sector in any chart — the sign is forced by topology, not by choice of basis. The criterion's strictness witness: the intrinsic binding of the theta classes is positive, because the cycles overlap with `⟨c₁,c₂⟩ = 2` |
| `wedge_binding_zero` | **The boundary** (G6): the wedge's basis cycles share no edge, the overlap is zero — disjoint matter does not bind |
| `HarmonicGramData.bindingEnergy_eq`, `theta_interaction`, `theta_bindingEnergy`, `theta_binding_attractive` | Binding energy is `−2·interaction`; at theta the interaction is `−1/6` — **the closed-form instance** `−2/12` (demoted at G6, rule 3: `⟨c₁,c₂⟩ = 2`, `det = 12`) — the binding energy `1/3`, and the joint sector strictly cheaper than its parts: **attraction**. The criterion's own witness is `theta_binding_attractive_class` |

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
| `theta_residue_count`, `theta_gauge_count` | K1 and the gauge count consumed at the theta graph: `q²` residue classes, `q⁴` gauge volume (`Meno/ThetaHarmonic.lean`) |
| `card_sections`, `log_card_sections` | The reverse descriptions of a map are its sections, counted exactly; reverse-description cost equals fiber information |
| `sectionCost_eq_fiberInfoCost`, `descriptionCost_eq` | The same coding identity named at the cost level for any surjection; the forward cost of describing a map is `log \|A → B\|` |
| `sectionCost_pos_of_not_injective` | Reversing a genuinely lossy map has strictly positive cost — the arrow is strict |
| `card_compression_sections` | The compression's sections in closed form: `\|G_q\|^{q^{b₁}}` — one independent gauge choice per incompressible class |
| `sectionCost_compression`, `recoveryCost_compression` | The coding theorem, for the global gauge-fixing and for a single class |
| `sectionCostE_eq_top_iff`, `sectionCostE_eq_zero_iff`, `recoveryCostE_eq_top_iff` | The extended cost is `⊤` when no section exists, zero cost characterizes bijections, unproducible outputs are priced at `⊤` |
| `sectionCostE_eq_sum_recoveryCostE` | The extended coding identity holds on both sides of the boundary — an impossible inverse is not free |
| `section_not_surjective_of_not_injective`, `simplicial_ratchet` | Where fibers are infinite, the cardinality-free form: a section of a non-injective map always misses states |
| `classSectorAction`, `classSectorAction_energy`, `basisGramData_partFn_eq_classSectorAction` | The intrinsic sector action is `H¹(G;ℤ)` with the harmonic energy; every basis-coordinate action is a chart of it (`Meno/BasisIndependence.lean`) |
| `h1ResQuotEquiv`, `latticeQuotEquivQ_h1Res` | Coefficient reduction `h1Res` is surjective with kernel `q·H¹(G;ℤ)`, giving `H¹(G;ℤ)⧸q·H¹(G;ℤ) ≃ H¹(G;ZMod q)`, coordinates commuting with the keystones |
| `uniformAction_h1ResQuot_complexity`, `uniformComplexity_split_carrier` | The residue's uniform complexity `b₁ · log q` and the K2 split, derived through that reduction |
| `residueMass`, `residueMass_chart`, `descriptionMass` | The carrier's intrinsic Gibbs distribution pushes forward to the residue — positive, normalized, computed by every basis chart — and lifts uniformly through the compression |
| `descriptionEntropy_split` | Description entropy = residue entropy + the gauge log |
| `sectionCost_carrierCompression_div`, `sectionCost_carrierCompression_action` | The per-sector gauge-fixing cost is exactly that conditional entropy — at the action level, exactly `K(descriptionAction) − K(residueAction)` |
| `sectionCost_eq_sum_log_fiberCount` | **The counted cost, non-uniform** (G5): a surjection's reverse-description cost is `Σ_d log (fiberCount f d)` — the coding theorem read through the redundancy profile |
| `lift_complexity_ge_gibbs_log_rate` | **The Jensen ratchet bound** (G5): `⟨log ∘ fiberCount f⟩ ≤ K(lift f) − K` — the priced increment dominates the Gibbs-mean log-redundancy |
| `lift_complexity_sub_eq_iff_fiberCount_const` | **The boundary** (G5): the Jensen gap vanishes iff the redundancy is constant — full Gibbs support makes the boundary exact; the ratchet's defect is one more fluctuation quantity |
| `twoSector_jensen_gap_pos` | **The strictness** (G5): at the two-sector witness the Jensen gap is strictly positive |
| `SectorAction.sectionCost_uniformLift` | **The constant-redundancy chart** (demoted at G5, rule 3): `sectionCost f / \|Λ\| = K(uniformLift) − K(base)` — both sides collapse to `log m` at constant fibers |

### Self-reference

The diagonal corner (G8): **no description system enumerates its own
binary predicates, and the shortfall is priced.** The scope is stated
plainly: this is the Lawvere/Cantor core in Meno's vocabulary — the
fixed-point-free diagonal on `ZMod 2`-valued predicates — not a
formalization of the incompleteness theorems (`Meno/Diagonal.lean`).

| Result | Statement |
| :--- | :--- |
| `no_self_enumeration` | **The impossibility** (G8): for every type `A`, in every universe, with no finiteness hypothesis, there is no surjection `A → (A → ZMod 2)` — the direct diagonal |
| `descriptionCost_split` | **The exact law** (G8): on a nonempty finite carrier the forward cost of a binary predicate is the enumerable budget plus its own correction term — `descriptionCost f = log \|A\| + log (\|A → ZMod 2\| / \|A\|)` |
| `log_card_lt_descriptionCost` | **The strictness — the cost corollary** (G8): the correction term is strictly positive at every nonempty finite carrier — `log \|A\| < descriptionCost f` — derived through the counting shadow of the diagonal itself, not from an independent numeric bound |
| `log_card_eq_descriptionCost_iff` | **The boundary** (G8): budget equals price **iff** the carrier is empty — the shortfall vanishes exactly where there is nothing to describe |

### Symmetry

The no-go face (G4): descriptions exist and are priced (K1–K3), and a
description respecting the system's own symmetry can fail to exist at
all. `IncidenceGraph.Auto` is the generic automorphism — vertex and
edge equivalences commuting with `src` and `tgt` — with the pullback
`Auto.cochainMap` on `R`-cochains, its commutation with the gradient
(`Auto.cochainMap_grad`), and the descended actions `Auto.h1Map` (any
coefficient ring) and `Auto.h1ReductionMap` (the finite reduction of
the intrinsic carrier). On the cycle graph the rotation `cycleRot`
acts transitively on edges — an invariant cochain is constant
(`cycleRot_invariant_eq_const`) — and trivially on classes. The
winding-one generator (`windingOneClass`, through the class map
`h1ResClass`) then admits no symmetric description off coprimality:
where the symmetric description fails, every encoding of the class
breaks the symmetry — the choice of bit is physical.

| Result | Statement |
| :--- | :--- |
| `cycle_no_invariant_representative` | **The impossibility**: at `1 < gcd n q` no rotation-invariant cochain represents the generator class — invariance forces constancy, a constant's winding is `n·c`, and `n·c = 1` in `ZMod q` is exactly invertibility of `n` |
| `cycle_equivariant_section_iff` | **The exact law**: a rotation-equivariant section of the resolution-`q` compression exists iff `gcd n q = 1`; the forward construction is the constant cochain scaled by `n⁻¹ mod q` |
| `cycleRot_h1Map_int`, `cycleRot_h1ReductionMap` | The rotation is trivial on integral classes and on the carrier's finite reduction — the *content* is symmetric even where every *description* of it is not |
| `cycle_four_two_no_invariant_representative`, `cycle_four_two_no_equivariant_section` | **The strictness witness** at `(n, q) = (4, 2)`: no invariant representative, no equivariant section |
| `cycle_three_two_equivariant_section` | **The boundary witness** at `(n, q) = (3, 2)`: the equivariant section, exhibited |

### Gravity

There is **one gravity law** (G2): the four-term defect of coupling
two descriptions over a shared base is exactly the log-correlation
of their redundancy profiles (`gravity_defect`), and it vanishes
precisely at zero Gibbs covariance
(`gravity_defect_eq_zero_iff`). The priced identity
`SectorAction.complexity_gravity` — coupling saves exactly the base
— is its **zero-covariance chart**: constant redundancy profiles
have zero covariance, and the theorem is re-derived as that instance
(demotion, PLAN rule 3), its statement unchanged, its decomposition
lemmas (`coupling_energyEquiv`, `uniformLift_energyEquiv`,
`complexity_prod`) retained as structure. What is established is
that **one statement** has the counting, entropy,
partition-function, and carrier identities as literal instances:
**counting** is the zero-energy special case, **entropy** the
Gibbs-split corollary, and on the graph carrier the identity holds
priced by the action itself, with pricing and counting numerically
bridged by the same deficit at all three levels, strict wherever
there is anything to price, and the resolutions forming a tower
whose losses are priced in one currency.

#### The covariance gravity law (G2)

| Result | Statement |
| :--- | :--- |
| `SectorAction.lift`, `SectorAction.couple` | The unconditioned constructions: energy pulled back along any surjective map from a finite type — surjectivity carries the zero-energy sector — and the pullback `SGD.Pullback` priced by the base; no fiber hypotheses |
| `fiberCount`, `SectorAction.gibbsCov`, `gibbsCov_self` | The redundancy profile of a description map, and the Gibbs covariance whose diagonal is the standing `gibbsVariance` |
| `lift_complexity`, `couple_complexity` | The priced increments are log Gibbs-mean redundancies: `K(lift f) = K + log⟨fiberCount f⟩`, `K(couple) = K + log⟨fiberCount f · fiberCount g⟩` (pullback fibers are fiber products, `fiberCount_pullback_base`) |
| `gravity_defect` | **THE COVARIANCE GRAVITY LAW**: `gravityDefect = log⟨m·m'⟩ − log⟨m⟩ − log⟨m'⟩` — sharing two descriptions over one base saves exactly the base, corrected by the log-correlation of their redundancy profiles; the correction is a fluctuation quantity |
| `gravity_defect_eq_zero_iff` | **The boundary**: the defect vanishes iff `gibbsCov (fiberCount f) (fiberCount g) = 0` — the constant-fiber identity is the zero-covariance chart, not a law of coupling |
| `gibbsCov_double_sum`, `gravityDefect_nonneg_of_comonotone` | **The direction theorem**: `Cov(φ,ψ) = ½ Σ_{d,d'} μ_d μ_{d'} (φ_d − φ_{d'})(ψ_d − ψ_{d'})`, so comonotone redundancy binds — `0 ≤ defect` |
| `twoSectorAction`, `twoSectorMap`, `twoSector_gravityDefect_pos` | **The strictness witness**: base `Bool` with energies `0`/`1` and redundancy profile `(1, 2)` on both legs — the defect is `log⟨m²⟩ − 2 log⟨m⟩ > 0`, by strict Gibbs fluctuation of the non-constant profile |
| `exists_gravity_defect_ne_zero` | **The impossibility**: there is no correlation-free general coupling — the defect is not identically zero |

#### The gravity theorem and its corollaries

| Result | Statement |
| :--- | :--- |
| `SectorAction.complexity_gravity` | **The gravity theorem**: `K(coupling) + K(base) = K(lift) + K(lift)` (`Meno/InfoRatchet.lean`) |
| `coupling_energyEquiv`, `uniformLift_energyEquiv` | Energy-level decompositions of the constant-fiber constructions: `coupling ≈ base ⊗ (free ⊗ free)`, `lift ≈ base ⊗ free` — read through `SectorAction.EnergyEquiv` and `complexity_congr`; retained as structure, the former proof route of `complexity_gravity`, retired at G2 |
| `partFn_gravity` | The partition-function form — the exponential of the complexity form |
| `counting_gravity` | **Counting is the zero-energy corollary**: `log \|X ×_D Y\| + log \|D\| = log \|X\| + log \|Y\|` for uniform-fiber maps into a finite shared base — the gravity theorem instantiated at `uniformAction D` |
| `uniformAction` | A finite type as a sector lattice with zero energy — `Z = \|A\|`, `K = log \|A\|` (`uniformAction_partFn`, `uniformAction_complexity`, `Meno/UniformAction.lean`) |

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
| `carrier_gravity_complexity` | The counting identity on the carrier — `counting_gravity` instantiated at the compression, with the same fiber arguments as the entropy form above |
| `carrier_gravity_deficits_cancel` | The uniform-entropy deficits at all three levels are the same `Δ` and cancel across the identity — why pricing and counting are numerically one face on the carrier |

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
| `h1TowerMap`, `h1TowerMap_comp` | For `q ∣ q'` the finer reduction maps canonically onto the coarser — identity, composition, and surjectivity laws |
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
| `h1ReductionCRT`, `card_h1Reduction_mul_gcd` | **CRT on the tower** (G3, `Meno/TowerGravity.lean`): the `lcm` reduction **is** the fiber product of the two reductions over their common coarsening — the finer resolution is the coupling of the coarser ones; the counting identity is `Nat.gcd_mul_lcm` raised to `b₁` |
| `residueWeight_zero_eq_classScaledPartFn`, `harmonicEnergy_zsmul` | **The key lemma** (G3): the modal coset weight is the scaled partition function — `residueWeight q 0 = classScaledPartFn (q²)`; the fiber of zero is `q·H¹`, enumerated from the carrier by multiplication by `q`, with quadratic energy |
| `residue_gravity_crossRatio` | **THE CROSS-RATIO LAW** (G3): the four-resolution gravity defect on the tower is `(log Z(q²) + log Z(q'²)) − (log Z(gcd²) + log Z(lcm²))` — a cross-ratio of scaled partition functions |
| `residue_gravity_dvd` | **The boundary** (G3): along a divisibility chain the defect vanishes identically — gravity is exact along chains; off them it can strictly fail (`cycle3_crossRatio_neg`) |
| `cycle3_classScaledPartFn`, `cycle3_crossRatio_neg` | **The strictness** (G3): on `C₃` at `(2, 3)` the defect is strictly negative — `Z(1/3)·Z(12) > Z(4/3)·Z(3)` by first-mode lower bounds against geometric tails — **at the witness, incomparable resolutions couple supermodularly**; read as the face's negative: there is no resolution-independent gravity on the tower — exact along the divisibility order, strictly failing at an incomparable pair |
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
| `QuadLatticeAction.scale` | Temperature as an operation on the carrier bundle: identity, multiplicativity, equivalence transport, chart compatibility (`scale_one`, `scale_scale`, `Equiv.scale`, `scale_chartAction`), with the `β = 1` recovery of the unscaled partition function and mean energy (`scaledPartFn_one`, `meanEnergy_one`) |
| `QuadLatticeAction.hasDerivAt_meanEnergy_eq_neg_gibbsVariance`, `QuadLatticeAction.meanEnergy_strictAntiOn` | Stated **once for every bundled lattice action**, basis-free moments computing through every chart |
| `classQuadActionβ`, `hasDerivAt_classMeanEnergy_eq_neg_gibbsVariance`, `classMeanEnergy_strictAntiOn` | The intrinsic carrier is a direct specialization (`classQuadActionβ := classQuadAction.scale`, `β = 1` recovery proved once on the bundle, scaled moments invariant under `≃q`): `d⟨E⟩/dβ = −Var` holds intrinsically, and on any graph with cycles the Gibbs mean energy strictly falls |
| `theta_hasDerivAt_classMeanEnergy`, `theta_classMeanEnergy_strictAntiOn` | Both consumed on the genuinely non-diagonal theta carrier |
| `unitQuadAction`, `hasDerivAt_quadraticMeanEnergy_eq_neg_gibbsVariance`, `quadraticMeanEnergy_strictAntiOn`, `quadraticObj_gibbsVariance_pos` | The canonical scalar family is the rank-one chart of the same engine, its public theorems derived from it (`Meno/Duality.lean`) |
| `M2_sq_lt_Z_mul_M4` | The Cauchy–Schwarz route retained as named corroboration |

### Geometry

The systole face (G1): for every finite graph, every class, and every
integral cycle, **pairing squared is bounded by harmonic energy times
chain norm** — and the bound is the dual-norm characterization of the
harmonic representative, sharp exactly on its scalar multiples. The
impossibility anchor is the standing `MatterSector.not_gradient`: the
class whose mass the inequality bounds admits no global potential.
Every symmetric simplicial complex's fundamental groupoid carries a
Lawvere-subadditive geodesic length, and on the `n`-cycle the
combinatorial and harmonic masses meet — now as the equality case of
the systole inequality, through the walk-length bridge.

| Result | Statement |
| :--- | :--- |
| `pairing_sq_le_energy_mul_normSq` | **The systole inequality** (`Meno/Systole.lean`): `⟨c, κ⟩² ≤ E(κ) · ‖c‖²` for every graph, class, and integral cycle — the attained realizer (`realizer_dotProduct_castCycle`) meets Cauchy–Schwarz |
| `MatterSector.mass_systole` | **The mass–systole bound**: `1/‖c‖² ≤ mass` for every cycle pairing nontrivially with matter — the integer pairing squared is at least one |
| `dualNorm_combination_le`, `dualNorm_combination_eq_iff` | **Dual-norm attainment**: `⟨z, κ⟩²/‖z‖² ≤ E(κ)` for every real cycle combination `z ≠ 0`, with equality iff `z` is parallel to the harmonic representative `periodRep` — whose coefficients are `(gramOf c)⁻¹ *ᵥ k` (`basisGramData_gram`, `harmonicEnergy_eq_periodRep_normSq`) |
| `theta_pairing_normSq_ge_four`, `theta_mass_gt_systole` | **The strictness** at the theta graph: every cycle pairing nontrivially with `thetaMatter` has chain norm at least `4` (chain Gram `!![4, 2; 2, 4]`, coordinates via `castCycle_normSq_eq_repr_quadForm`), so the systole bound `1/4` is strictly below the mass `1/3` |
| `cycleMatter`, `cycleMatter_mass`, `cycleMatter_pairing`, `cycleFullCycle_normSq` | Matter on `C_n`: the winding-one class — mass `1/n`, pairing `1` on the full cycle, chain norm `n` |
| `cycle_systole_equality` | **The equality case**: on `C_n` with the full cycle the systole inequality is equality — `1 = (1/n) · n` |
| `simplicialGeodesic` | The geodesic length instance (`Meno/Groupoid.lean`) |
| `geodesic_harmonic_duality` | `n · (1/n) = 1` — **the systole equality instance** (demoted, PLAN rule 3): geodesic length is the chain norm of the full cycle (`cycleGeodesic_canonical`), the walk-layer energy is the intrinsic mass, and `cycle_systole_equality` closes the circle |
| `cycleCanonicalObj`, `cycleCanonicalObj_partFn_eq_partitionFn` | The canonical cycle groupoid object — winding classes of the fundamental groupoid — with partition function recovering the walk model's `partitionFn`, no extra hypotheses |
| `GroupoidObj.toLoopKernelObj`, `cycleLoopKernel` | Every grounded groupoid object **is** a spine loop kernel — all five data fields transfer verbatim; the cycle instance |
| `cycleSectorPresentation`, `cycleLoopKernel_partFn_eq_partitionFn` | Winding coordinates present the cycle kernel as the rank-one quadratic action `!![1/n]`; its partition function transits the spine to `partitionFn n` — every step a spine theorem |
| `cycleSectorPresentation_partFn_eq_gramData` | Two origins, one analytic object: the groupoid presentation and the Hodge harmonic Gram data produce the same Gram matrix |
| `cycleCanonicalObj_T_duality` | Cycle groupoid T-duality as a corollary of `partitionFn_T_duality_via_spine` — no winding hypothesis, no dual-object construction |
| `cycleLoopKernel_dualVia_partFn` | The categorical dual consumed concretely: `Z(dualVia) = √((1/n)/π)·Z(C_n)` |

---

## The coverage bundle

The first program closed with a kernel-checked leg, a **Lean
object**: the statement-coverage bundle `MenoStatementCoverage`
(`Meno/Completion.lean`) — every acceptance
signature of that program is a field in exactly one of **nine law packages**, and
`menoStatementCoverage` is its one derivation, by direct
named-theorem assignment. The graph-dependent packages are quantified
over every finite multigraph `G`, the thermal package over every
bundled lattice action `Q`, the information package over every finite
distribution `P`; the coding-gravity package is **graph-free** — no
vacuous quantifier — and the flagship package pins the concrete
consumers.

| Package | Covers | Derivation |
| :--- | :--- | :--- |
| `GraphTopologyLaws` — `∀ G` | Gauge, Euler, independence, spanning, integral coordinates | `graphTopologyLaws` |
| `HarmonicCarrierLaws` — `∀ G` | Rank well-definedness, unimodular transport, the basis-free partition function, the variational identity, positive energy | `harmonicCarrierLaws` |
| `MatterBindingLaws` — `∀ G` | The intrinsic matter facts and the generic binding theorems on 2-complexes | `matterBindingLaws` |
| `ResolutionCodingLaws` — `∀ G` | Graph-dependent: K1–K3 at every modulus, gauge counting, compression sections and costs, per-class recovery | `resolutionCodingLaws` |
| `CodingGravityLaws` — graph-free | Generic: section counting, the coding theorem with its `ℝ≥0∞` boundary, the priced gravity and time identities, and counting gravity as the zero-energy corollary | `codingGravityLaws` |
| `ThermalDualityLaws` — `∀ Q` | The scale algebra, the dual involution, temperature inversion, and the partition, mean-energy, and variance functional equations with the self-dual fixed point | `thermalDualityLaws` |
| `InformationLaws` — `∀ P` | Pushforward functoriality, the unconditional entropy chain rule, the support-aware Gibbs inequality, data processing | `informationLaws` |
| `ResolutionTowerLaws` — `∀ G` | The tower category, pushforwards, additive prices and costs, telescoping monotone deficits, strict pricing of genuine refinements | `resolutionTowerLaws` |
| `FlagshipLaws` | The concrete consumers: cycle, wedge, and theta results — bases, counts, dualities, priced faces, tower prices, the thermal circle, the geodesic–harmonic duality | `flagshipLaws` |

Scope: the bundle enforces **statement coverage** —
deleting an acceptance theorem breaks the derivation. Proof provenance
is enforced by the direct-assignment discipline and review. The
repository invariants are machine-assisted by `scripts/audit.py`
(README citations resolve; recorded deletions stay deleted; deleted
names are cited nowhere in living text; the architecture listing
matches the tree; every declaration is reachable from the publicly
claimed results or enumerated with its retention predicate). The
bundle certifies statements, not depth; the Obstruction Program
([`PLAN.md`](PLAN.md)) replaces it with a single dichotomy theorem
whose forward direction requires every face's strictness. Audit
chronology lives in the repository log.

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
├── Systole.lean               The systole inequality (G1): Cauchy–Schwarz law, dual-norm attainment, mass–systole, C_n equality
├── BindingSign.lean           The binding sign criterion (G6): rank-two closed form, intrinsic binding energy, attraction iff overlap
├── TowerGravity.lean          Arithmetic gravity on the tower (G3): CRT, the key lemma, the cross-ratio law, chain exactness, C₃ strictness
├── Basic.lean                 The pullback substrate: fibers, the shared-base pullback, sigma-fiber and marginal equivalences
├── UniformAction.lean         The uniform (zero-energy) sector action; pullback finiteness
├── InfoRatchet.lean           Fiber information; the coding theorem; THE GRAVITY THEOREM and its counting corollary; finite distributions
├── ResolutionCount.lean       K1–K3 at every resolution; gauge count; section cost; the Gibbs residue distribution
├── Symmetry.lean              Graph automorphisms; the rotation; the symmetry no-go and the equivariant-section law (G4)
├── Diagonal.lean              Self-reference (G8): the diagonal no-self-enumeration; the priced shortfall, its split law, its empty-carrier boundary
├── Simplicial.lean            Walk/homotopy/Hodge model (independent corroborating route)
├── Groupoid.lean              Fundamental groupoid; geodesic instance; the cycle bridge to the spine
├── CycleHarmonic.lean         Flagship bridge: walk route ≡ period route; T-duality on C_n
├── ThetaHarmonic.lean         The theta graph: non-diagonal Gram derived from topology
├── Hodge.lean                 Graph partition functions (identified with the spine)
├── Duality.lean               The scalar quadratic family and Gibbs wrappers (identified with the spine)
├── Zeta.lean                  Riemann functional equation through the spine's theta identification
└── Completion.lean            THE STATEMENT-COVERAGE BUNDLE: every Part-I acceptance signature, one field each, one derivation; the three spine law packages
```

The legacy layer (`Meno/Simplicial.lean`–`Meno/Zeta.lean`) is retained
deliberately: it is
a second, independent derivation of the spine's first objects, with
the identifications proved (`cyclePeriodData_energy_eq`,
`quadraticPartFn_eq_scalarPartFn`, `graphPartitionFn_eq_spine`,
`GroupoidObj.gibbsMass_eq_sector`, …). Two derivations, one object.

---

## Scope of the physical vocabulary

The words "gravity", "matter", "time", "uncertainty" name formal
analogues inside a finite, discrete model: gravity is a
priced complexity identity of coupling over a shared base, matter is nontrivial cohomology
with variational mass, time's arrow is the counted cost of reversing
compression, and uncertainty is Gibbs fluctuation with its response
identity. The project's claim is that these analogues are *theorems of
one structure* — the sector lattice with its action — not that the
physical world has been derived. Where a desired statement failed,
the counterexample is kept as a theorem
(`exists_dualityFlow_eq_zero_not_selfDual`), and every excised
design is recorded in `scripts/deleted.txt`.

---

## Build

Requires Lean 4.26.0 and the pinned Mathlib.

```bash
lake build
```
