# Meno

*Structural Geometrodynamics in Lean 4*

Meno is a universe that minimizes the complexity of its own description. Gravity, matter, and the arrow of time emerge from this single principle.

---

## The core idea

> Assign a cost to every structure: the minimum amount of information needed to describe it.
> The universe evolves by rewriting its state to lower that cost.
> Structures that share sub-descriptions merge (gravity).
> Structures that resist compression persist (matter).
> Irreversible computation accumulates (time).

This is formalized at two levels of abstraction that tell the same story with different tools.

---

## Why these pieces

### Complexity (K)

The theory starts by assigning a number K to every structure - its descriptive cost. K is a function from types to an ordered monoid, subject to axioms about how it composes. If two independent things cost K(A) and K(B), their product costs at most K(A) + K(B). For dependent structures (one thing parameterized by another), the cost is bounded by the base plus the worst-case fiber.

### Pullbacks (gravity)

When two structures A and B both contain a shared component D, they can be refactored into a *pullback* - a combined structure that encodes D only once. The savings equal the cost of D.

This is the refactoring bound. Gravity is the gradient of descriptive economy. Systems fall together because the shared state is cheaper.

### The concrete model (matter and mass)

So K decreases when structures share descriptions, and the pullback is the mechanism. Why doesn't everything merge into a single trivial structure?

To answer this we need a concrete space where K can be computed. Meno builds one from a *simplicial complex*: points connected by edges, with some triangles filled in as *faces*. A path through this space is a sequence of adjacent steps - a walk. The complexity of a walk is its length, but length can be reduced: if you step forward and immediately back, those cancel. If three points form a filled triangle, you can shortcut across it. The *geodesic length* is the shortest length achievable after all such reductions.

Here is where obstruction enters. A loop that winds around an *unfilled* triangle has no shortcut available. Every reduction leaves it just as long. Its geodesic length is positive - it carries irreducible cost.

This is matter. A loop whose interior can be filled relaxes to nothing (vacuum). A loop around an absent face persists. When a loop that was stuck in one complex finds new shortcuts through a union with another, the geodesic length drops. The difference is binding energy — the simplicial version of the pullback savings above. In the extreme case, a complementary complex provides exactly the missing face: the loop contracts to nothing and all its mass converts to binding energy. This is annihilation.

The same obstruction measured in different regions gives different geodesic lengths. A cycle near a high-connectivity region (many faces available) has more reduction paths and a shorter geodesic. This is redshift: the same topological charge, measured where there are more ways to relax, appears lighter.

Two notions of complexity coexist. Geodesic length is combinatorial: the mass of the n-cycle is n. But the physically richer measure comes from distributing flow. A *harmonic form* on an n-vertex cycle assigns uniform flow 1/n along each edge. It is a *reproducing kernel*: its inner product with any cochain extracts the winding number. Energy decomposes orthogonally as w²/n + residual (Hodge), and the harmonic form is the unique energy minimizer in each winding class. In this measure, mass scales as 1/n — larger symmetry groups cost less to describe.

### The partition function (quantum sectors)

Summing Boltzmann weights exp(−k²/n) over all integer winding numbers k gives the partition function of the n-cycle. This is a Jacobi theta function ϑ₃(0, e^{−1/n}). The modular S-transformation (T-duality) then follows directly, relating the partition function at coupling 1/n to the dual coupling at π²n.

The vacuum sector (k = 0) contributes weight 1. Every other sector is exponentially suppressed. Particles are rare excitations on top of an overwhelmingly dominant vacuum.

### The ratchet (time)

A map that collapses distinct inputs into one output destroys information. Recovering which input produced a given output costs strictly more than the forward map. This asymmetry - the ratchet - is what we experience as time.

Injective maps preserve all information and are freely reversible: their forward and backward costs are equal. Lossless computation is *timeless*. Only non-injective computation, the kind that increases entropy, creates an arrow.

In the simplicial model, computing a geodesic length is an instance of the word problem for the fundamental group. Tangling (extending a path) is O(1) per step; untangling (finding the geodesic) requires searching over face reductions. The ratchet emerges from computational complexity, not axiom.

---

## What's proved

### Basic.lean — the constitution

The constitutive laws of the Meno universe. Any concrete model (simplicial or otherwise) must satisfy these to be a valid physical realization. Two distinct parts:

**Statics — structural economy (theorems):**

| Level | Class | Key property |
| :--- | :--- | :--- |
| 1 | `ComplexityMeasure` | Subadditive: K(A × B) ≤ K(A) + K(B) |
| 2 | `SigmaComplexity` | Sigma-subadditive: K(Σ d, P d) ≤ K(D) + sup K(P d) |
| 3 | `AdditiveComplexity` | Exact: K(A × B) = K(A) + K(B) |

| Result | Status |
| :--- | :--- |
| Refactoring bound: K(A ×_D B) ≤ K(D) + sup fibers | **Theorem** (from level 2) |
| Gravity: K(Pullback f g) + K(D) = K(A) + K(B) for any f, g with uniform fibers | **Theorem** (from level 3) |
| Log-cardinality instance: C(A) = log\|A\| satisfies all three levels (`Instances.lean`) | **Instance** (AdditiveComplexity ℝ≥0∞) |

**Dynamics — the arrow of time (`TransitionComplexity` class):**

| Law | Statement |
| :--- | :--- |
| `transitionCost` | Every map has a computational cost |
| `transitionCost_pos` | That cost is always positive |
| `ratchet` | Inverting a non-injective map costs strictly more than the forward map |
| `injective_reversible` | Injective maps are losslessly reversible: equal cost in both directions |

The Landauer cost model (`transitionCost f = if Injective f then 2 else 1`) provides a concrete instance. Any right-inverse of a non-injective map is injective (since f ∘ r = id implies r is injective), so the ratchet follows: cost(r) = 2 > 1 = cost(f).

**Structured complexity (`StructuredComplexity` class):**

The type-level hierarchy measures bare types (complexity depends only on cardinality via `congr`). For structured objects like simplicial complexes, complexity depends on topology. `StructuredComplexity` captures the same algebraic law — merge/overlap gravity — for any object type:

| Law | Statement |
| :--- | :--- |
| `merge_overlap` | K(merge A B) + K(overlap A B) = K(A) + K(B) |

The simplicial model instantiates this with K = b₁, merge = union, overlap = intersection. The merge_overlap law is Mayer-Vietoris.

### Simplicial.lean — the concrete model

`Simplicial.lean` imports `Basic.lean`. Paths as explicit data (walks in a simplicial complex). Zero axioms.

**Topology and matter:**

| Result | Statement |
| :--- | :--- |
| `windingCount_homotopy_invariant` | Winding number is a homotopy invariant |
| `cycleGraph_not_contractible` | The canonical cycle on C_n cannot be homotoped to nil |
| `cycleGraph_geodesic_eq_n` | Geodesic length of the canonical cycle is n |
| `binding_releases_mass` | When a cycle contracts in the union, binding energy = full cycle complexity |
| `simplicial_gravity` | Corollary: non-contractible + contracts in union → binding > 0 |
| `matter_noncontractible` | Positive mass implies non-contractibility |

**Hodge theory and the harmonic form:**

| Result | Statement |
| :--- | :--- |
| `innerC1_cycleHarmonicForm` | Reproducing kernel: ⟨h, σ⟩ = winding(σ) · ‖h‖² |
| `hodge_decomposition` | Hodge Pythagoras: energy(σ) = w²/n + energy(residual) |
| `hodge_orthogonality` | Hodge orthogonality: ⟨h, σ − w·h⟩ = 0 |
| `energy_eq_zero_iff` | Positive definiteness: energy(σ) = 0 iff σ = 0 |
| `energy_ge_winding_sq` | Energy ≥ w²/n for winding w (from Hodge + non-negativity) |
| `cycleGraph_harmonicEnergy` | Minimum energy over winding-1 cochains = 1/n |
| `cycleGraph_harmonicEnergy_k` | Instanton spectrum: min energy in sector k = k²/n |
| `hodge_minimizer_eq` | Instanton uniqueness: min-energy cochain = k·h (unique ground state) |
| `cycleEC1_harmonic_eq_smul` | **b₁(C_n) = 1**: every harmonic edge-supported form is proportional to h |

**Partition function:**

| Result | Statement |
| :--- | :--- |
| `partitionFn_pos` | Z(C_n) > 0 |
| `sector_weight_eq_min_energy` | Boltzmann weight = exp(−instanton energy) |
| `sector_weight_lt_one_of_ne_zero` | Non-vacuum sectors exponentially suppressed |

**Structure (products, intersections, dynamics):**

| Result | Statement |
| :--- | :--- |
| `Graph.Symmetric`, `Graph.Irreflexive` | Structural predicates on graphs |
| `cycleGraph_symmetric`, `cycleGraph_irreflexive` | The cycle graph satisfies both predicates |
| `Complex.prod` | Product of two complexes with prism face decomposition |
| `prod_edgeFinset_card` | \|E(C₁ × C₂)\| = \|E₁\|·\|V₂\| + \|V₁\|·\|E₂\| (irreflexivity decomposes edges) |
| `Complex.inter` | Intersection of two complexes |
| `Complex.union` | Union of two complexes |
| `bettiOneZ_cycleGraph` | bettiOneZ(C_n) = 2 = 2·b₁, bridging edge-counting to Hodge-theoretic b₁ |
| `bettiOneZ_mayer_vietoris` | b₁(C₁ ∪ C₂) + b₁(C₁ ∩ C₂) = b₁(C₁) + b₁(C₂) (from edge inclusion-exclusion) |
| `StructuredComplexity` instance | b₁ with union/intersection satisfies the structured gravity law |
| `geodesic_computation_is_lossy` | Quotient map to homotopy classes is non-injective |
| `simplicial_ratchet` | Any section of the quotient costs strictly more than the forward map (TransitionComplexity applied) |

### Theta.lean - the bridge to analytic number theory

| Result | Statement |
| :--- | :--- |
| `partitionFn_eq_jacobiTheta` | Z(C_n) = ϑ₃(0, e^{−1/n}) via Mathlib |
| `cycleTau_S_transform` | Dual coupling: S-transform maps τ = i/(πn) to iπn |
| `cycleTau_prefactor` | Modular prefactor: −iτ = 1/(πn) (positive real) |
| `partitionFn_T_duality` | ϑ₃(iπn) = (1/(πn))^(1/2) · Z(Cₙ) (explicit T-duality) |

---

## Why not HoTT?

Standard Lean 4 uses Axiom K: all proofs of equality are identical. This collapses the topological structure SGD requires - a non-trivial loop would be squashed to reflexivity.

Instead, Meno models paths as **walks** (sequences of adjacent vertices) and homotopy as an explicit equivalence relation (backtracking + face reduction). This recovers the relevant homotopy theory computationally rather than foundationally.

---

## Structure

```
Meno/
├── Basic.lean        Abstract framework: complexity hierarchy, pullback, refactoring bound, ratchet
├── Instances.lean    Log-cardinality instance: C(A) = log|A| satisfies AdditiveComplexity
├── Simplicial.lean   Concrete model (imports Basic): walks, cycles, geodesics, Hodge theory, products, dynamics
└── Theta.lean        Jacobi theta identification and T-duality via Mathlib modular forms
```

---

## Build

Requires Lean 4.26.0 and Mathlib 4.26.0.

```bash
lake build
```
