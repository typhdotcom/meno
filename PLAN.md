# Plan: Complexity on Groupoids

## The problem

The complexity hierarchy in Basic.lean defines `C : Type u → M`. The only instance is log-cardinality: `C(A) = log|A|`. Under this instance, the gravity theorem reduces to a counting identity: `|Pullback| · |D| = |A| · |B|`. Nothing about descriptions, nothing about topology.

This happens because Lean types (Axiom K) can't carry topology. All paths are trivially equal, so `C` can't distinguish a circle from a line segment of the same cardinality. The simplicial shadow was built to work around this — walks and homotopy as explicit data recover the relevant homotopy theory computationally.

But the shadow keeps drifting from the foundation. Without a formal tether, agents treat Simplicial.lean as the theory and Basic.lean as boilerplate. The StructuredComplexity bridge attempted to fix this but ended up proving Euler characteristic inclusion-exclusion (edge counting), not topological gravity.

The partition function (Theta.lean) is the real bridge: Z(C_n) = Σ exp(-k²/n) = ϑ₃(0, e^{-1/n}) sums over descriptions weighted by their complexity. This IS the MDL principle made into physics. But it's not connected back to the abstract hierarchy.

## The solution

Enrich the domain of `C` from bare types to **groupoids**.

A groupoid has objects (points) and morphisms (paths between points). Lean types only have objects — Axiom K kills the morphisms. But the simplicial model already builds a groupoid: vertices are objects, homotopy classes of walks are morphisms. This is `HomotopyClass₂`, already defined.

The partition function becomes `C` evaluated on this groupoid:

- Each element of the automorphism group (each winding number k ∈ ℤ) has a **description length**: the instanton energy k²/n.
- The partition function **sums Boltzmann weights** over all descriptions: Z = Σ exp(-k²/n).
- The **effective complexity** is log Z — the free energy.

This satisfies the hierarchy axioms:

| Axiom | Why it holds |
| :--- | :--- |
| `unique_zero` | Trivial groupoid: Z = exp(0) = 1, log Z = 0 |
| `congr` | Equivalent groupoids have isomorphic automorphism groups, same Z |
| `prod_eq` | Independent groupoids: Z(G×H) = Z(G)·Z(H), so log Z is additive |

The existing results become instances of the abstract theory:

| Current result | Becomes |
| :--- | :--- |
| Z(C_n) = ϑ₃(0, e^{-1/n}) | C evaluated on the cycle's fundamental groupoid |
| T-duality | Symmetry of C under scale transformation |
| Instanton energy k²/n | Description length of the k-th automorphism |
| b₁ = 1 (harmonic uniqueness) | The automorphism group has rank 1 |

## Steps

### 1. Package the fundamental groupoid

The machinery exists in Simplicial.lean: walks, homotopy, `HomotopyClass₂`, composition, reversal. Package this as a Mathlib `CategoryTheory.Groupoid` instance.

- Objects: `V` (vertices of a `Complex V`)
- Hom v w: `HomotopyClass₂ C v w`
- Composition: walk concatenation (quotient-compatible)
- Identity: nil walk
- Inverse: walk reversal

### 2. Define C on groupoids

For a connected groupoid G with base point x:

```
C(G) = log Z  where  Z = Σ_{g ∈ Aut(x)} exp(-K(g))
```

K(g) is the harmonic energy of the minimum-energy representative of g — the instanton energy. For the cycle graph, K(k) = k²/n, and Z = ϑ₃.

For disconnected groupoids, sum over connected components.

The energy function K comes from the Hodge theory: the inner product on cochains determines a quadratic form on the automorphism group. This is the "metric" on descriptions.

### 3. Prove the hierarchy axioms

- `unique_zero`: immediate (trivial group, Z = 1)
- `congr`: groupoid equivalence preserves Aut and energy spectrum
- `prod_eq`: independent groupoids have product automorphism groups, Z factorizes
- `sigma_le`: dependent families of groupoids bounded by base + worst-case fiber

### 4. Gravity on groupoids

The gravity theorem should say: when two groupoids share a sub-groupoid (common morphisms), the pullback has lower total complexity.

The categorical tool is the **homotopy pullback** (iso-comma) of groupoids. At the level of fundamental groups: **Seifert–van Kampen** determines how π₁ composes under unions with connected overlap. The partition function of the composite is constrained by those of the parts.

For abelian fundamental groups (which covers all graphs), the partition function over the composite lattice is a **Siegel theta function** with modular properties generalizing the Jacobi case.

### 5. Generalize the Hodge theory

The energy function K(g) comes from the Hodge inner product. Currently this is cycle-specific (cycleHarmonicForm, winding). Generalize to arbitrary connected graphs:

- The general Hodge decomposition (exact + harmonic, orthogonal) — the EC1 infrastructure is already graph-general
- dim(harmonic subspace) = b₁ = |E| - |V| + 1 for connected graphs
- The energy quadratic form on ℤ^{b₁} determined by the Gram matrix of harmonic generators

Diaspora (~/dev/diaspora/) has solved much of this: `betti_eq_harmonic_dim`, general Hodge decomposition, the dimension formula. The patterns are available.

### 6. Multi-cycle partition functions

For b₁ > 1, the partition function becomes a sum over ℤ^{b₁}:

```
Z = Σ_{k ∈ ℤ^{b₁}} exp(-k^T · Q · k)
```

where Q is the Gram matrix of harmonic generators. This is a **Siegel theta function**. T-duality generalizes via Poisson summation on lattices.

## What can be reused

| Source | What | Status |
| :--- | :--- | :--- |
| Simplicial.lean | Walk, homotopy, HomotopyClass₂ | Ready to package as Groupoid |
| Simplicial.lean | EC1, EC1.IsHarmonic, divergence | General (any Graph V) |
| Simplicial.lean | Partition function, Boltzmann weights | Cycle-specific, needs generalization |
| Theta.lean | Jacobi theta identification, T-duality | Cycle-specific instance of general theory |
| Basic.lean | Pullback infrastructure, hierarchy axioms | Foundation — extend domain to groupoids |
| Diaspora | General Hodge decomposition, b₁ = dim(H) | Patterns for step 5 |
| Mathlib | CategoryTheory.Groupoid, theta functions | Infrastructure |
