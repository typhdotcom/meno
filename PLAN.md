# Meno: Cost-Enriched Sector Theory

**Implementation Plan**

---

## Preamble (Plain Language)

Meno is a Lean 4 project arguing that a universe minimizes the cost of describing itself, and that gravity, matter, time, and uncertainty are different faces of that minimization. The codebase proves several pieces of this thesis through three different vocabularies — type-level complexity (`Basic.lean`), simplicial walks (`Simplicial.lean`, `Groupoid.lean`), and theta-function analytics (`Duality.lean`, `Hodge.lean`, `Zeta.lean`). None of these vocabularies matches the object the proofs are really about.

That object — the one that makes scalar T-duality, the Riemann functional equation, the harmonic energy decomposition on graphs, and matrix-rank duality all express the same identity — is a **sector lattice equipped with a positive-definite quadratic action**. The lattice (e.g. `ℤ`, `ℤ^r`, the endomorphism monoid of a base point, the first integer homology of a complex) records the discrete sectors a system can occupy. The action records the energy of each sector. The Boltzmann sum reads the partition function. Duality permutes lattice and dual lattice while preserving the partition function up to an explicit Gaussian prefactor.

This plan reorganizes Meno around that object. `SectorAction` is the analytic primitive: a type of sectors plus an energy function plus summable Boltzmann weights. `QuadraticAction` is the special case where the energy is `kᵀ Q k` for a positive-definite Gram form `Q`. Scalar T-duality (`α ↦ π²/α`) and matrix-rank Siegel–Poisson duality (`Q ↦ π² Q⁻¹`) live here as theorems about `QuadraticAction`. Both are proved. The matrix case uses multidimensional Poisson summation and the multivariate Gaussian Fourier transform; both are in Mathlib's analysis library or trivially derivable from it.

Categorical structure is a **way of producing** sector actions, not the foundation. `LoopKernelObj` is the wrapper around a basepointed object in a category, presenting `End base` as a sector lattice. `GroupoidObj` is the special case where the category is a groupoid. Simplicial topology produces the sector lattice (via `H₁`); Hodge harmonic minimization produces the Gram form `Q` (variationally, not by squaring a length). These are all "origin" sources for the analytic primitive.

**The variational bridge is load-bearing.** Energy is *not* length-squared. For a graph `G` with `b₁(G)` independent cycles and the standard inner product on edge cochains, the energy of a winding class `k ∈ ℤ^{b₁}` is the **minimum squared-norm representative** within that class:

```
E(k) = min over ω with winding k of ‖ω‖²
```

For the cycle graph `C_n`, this gives `E(k) = k²/n` (uniform-flow harmonic representative). Combinatorial geodesic length is a *separate* Lawvere-subadditive invariant; for `C_n` the canonical 1-cycle has geodesic length `n`, harmonic action `1/n`, and the product `n · (1/n) = 1` is the geodesic/harmonic duality.

Matter is recast as **nontrivial sector homology with positive minimum action**: a nonzero class in `H₁(C; ℤ)` whose harmonic representative has positive energy. This is ordinary cellular/group homology plus the Phase 5 variational theorem. Magnitude homology is *not* in this plan — Meno's existing matter content is `H₁` plus the harmonic-minimum theorem, and replacing `H₁` with magnitude homology would require a separate theorem the plan does not promise.

Time is recast as **information cost of fiber selection**. A many-to-one morphism collapses fibers; reconstructing which preimage produced a given image requires description length proportional to `log |fiber|`. The Landauer ratchet is a theorem about this fiber-information cost, *not* about morphism energies (which preserve identities and cannot generate the asymmetry on their own). The existing `TransitionComplexity` class is replaced by the theorem-level statement.

Gravity is recast as **kernel factorization through a shared object**: the existing pullback bound becomes an identity on partition functions over fiber products. The type-level hierarchy in `Basic.lean` is a particular sector theory — the discrete-enrichment `TypeKernel` where types are objects, functions are morphisms, and energy is cardinality-derived — and the existing refactoring-bound and gravity theorems are kernel identities in this special case.

When the plan is finished, the dependency graph is acyclic and flows: `SectorAction → QuadraticAction → LoopKernelObj → Geodesic → HarmonicForm → SectorPresentation → MatterHomology → InfoRatchet → HomKernelCat → Simplicial → Groupoid → Duality → Hodge → Zeta → Basic`. `Simplicial.lean` and `Groupoid.lean` move upstream as sector-origin files. `Basic.lean` moves downstream as the realization on discrete-enrichment kernels. Zero `sorry`. Zero new axioms. Zero "future work."

## Preamble (Technical)

**Analytic primitive.** Let `Λ` be a type (typically a commutative monoid). A **sector action** is `(Λ, E, summable)` where `E : Λ → ℝ`, `E` attains zero on some element of `Λ`, `E` is nonneg, and `∑' k, exp(-E k)` is summable. From this: partition function `Z := ∑' k, exp(-E k)`, complexity `K := log Z`, Gibbs mass `μ(k) := exp(-E k) / Z`, expectation `⟨f⟩ := ∑' k, f k · μ(k)`, variance `Var(f) := ⟨f²⟩ − ⟨f⟩²`. All defined at this level.

**Quadratic specialization.** Let `r : ℕ` and `Q : Matrix (Fin r) (Fin r) ℝ` symmetric positive-definite. A **quadratic action** is `(r, Q)` with sector lattice `Fin r → ℤ` and energy `E_Q(k) := kᵀ Q k`. Positive-definiteness gives an eigenvalue lower bound `λ_min > 0`, hence Gaussian decay and summability. The dual is `(r, π² · Q⁻¹)`. The **Siegel–Poisson duality**:

```
Z(π²·Q⁻¹) = √(det Q / π^r) · Z(Q)         (as complex equality)
```

is the load-bearing analytic theorem. The scalar case `r = 1`, `Q = !![α]`, recovers `Z(π²/α) = √(α/π) · Z(α)`.

**Categorical presentation.** A `LoopKernelObj` is `(C, [Category C], base, energy, energy_id, energy_nonneg, summable)`. Its `toSectorAction` is a forgetful projection: the categorical structure is discarded for the analytic content. A `SectorPresentation` is a pair `(coord : End base ≃* (Fin r → ℤ), Q : Matrix r r ℝ)` exhibiting the loop kernel's sector action as a quadratic action. The `MulEquiv` requirement is load-bearing: bare set equivalence suffices for the analytic identity (re-indexing), but structural duality requires composition correspond to addition.

**Origins.**
- **(O1) Groupoid endomorphism monoids.** For a groupoid with object `X`, `End X` is a group; when `End X ≃* ℤ^r`, this is the sector lattice. Cycle groupoids supply the `r = 1` case via winding equivalence.
- **(O2) Cellular/group homology.** For a finite 2-complex `C`, `H₁(C; ℤ)` is a free abelian group of rank `b₁(C)`. Each integer class is a sector; matter sectors live here.
- **(O3) Hodge harmonic minimization.** For a finite graph `G`, the harmonic 1-cochain in winding class `k ∈ ℤ^{b₁}` is the unique energy minimizer in the inner product on edge cochains. The Gram form `Q` is `Q_{ij} := ⟨ω_{e_i}, ω_{e_j}⟩`. The harmonic action equals the variational minimum `E(k) = min over ω with winding k of ‖ω‖²`. For `C_n`: `b₁ = 1`, `Q = !![1/n]`, `E(k) = k²/n`.

**Matter.** A matter sector is `(c ∈ H₁(C; ℤ), c ≠ 0, E_min(c) > 0)` where `E_min` is the harmonic minimum action. `cycleGraph_canonical_is_matter` follows from `cycleGraph_not_contractible` and `harmonic_energy_min`. `binding_releases_mass` is the statement that killing `c` in a union complex releases `E_min(c)`.

**Time.** A many-to-one functor `F : C ⥤ D` carries a **fiber information cost** `∑_d log |F⁻¹(d)|`. The ratchet theorem says: any section `s` of `F` requires description length at least this fiber-information cost beyond `F`'s own description. Crucially, this is *not* a statement about `s.map` on morphisms (which would collapse to `0 > 0` via `s.map (𝟙 d) = 𝟙 (s.obj d)` and `energy_id = 0`); it is a statement about the description cost of the *choice function* underlying `s.obj`.

**Gravity.** The existing pullback bound and gravity theorem are restated as identities on partition functions of `TypeKernel.atBase (Pullback f g)`. The `AdditiveComplexityOn` class is the underlying monoid homomorphism `(Type, ×) → (ℝ, +)`.

## Goals

When this plan is complete:

1. `Meno/SectorAction.lean` exists. `SectorAction`, `partFn`, `complexity`, `gibbsMass`, `gibbsExpect`, `gibbsVariance` defined and proved.
2. `Meno/QuadraticAction.lean` exists. Scalar `IntQuadraticAction := QuadraticAction 1`, matrix `QuadraticAction r`, dual construction, **scalar T-duality (relocated)**, **matrix Siegel–Poisson duality (newly proved)**, scalar as definitional rank-1 reduction.
3. `Meno/LoopKernel.lean` exists. `LoopKernelObj`, `toSectorAction`, bridge from `GroupoidObj`.
4. `Meno/Geodesic.lean` exists. Lawvere-subadditive `Geodesic` class. Simplicial walk-length instance.
5. `Meno/HarmonicForm.lean` exists. Hodge variational identity `E_min(k) = min over ω with winding k of ‖ω‖²` proved. `harmonicGramForm` for any finite graph.
6. `Meno/SectorPresentation.lean` exists. `SectorPresentation` uses `MulEquiv`. Cycle groupoid carries canonical instance. Duality transport theorem.
7. `Meno/MatterHomology.lean` exists. `MatterSector` defined as `(c ∈ H₁, c ≠ 0, E_min(c) > 0)`. Matter and binding theorems restated.
8. `Meno/InfoRatchet.lean` exists. `fiberInfoCost`, ratchet theorem (about section description length, not identity-energy). Landauer instance realized.
9. `Meno/HomKernel.lean` exists. `HomKernelCat`, per-cell partition functions, magnitude `1ᵀ Z⁻¹ 1`, base-slice projection to `LoopKernelObj`.
10. `Meno/Duality.lean`, `Meno/Hodge.lean`, `Meno/Zeta.lean` rewritten to import only the new analytic primitives. `Zeta.lean` depends on `QuadraticAction`, not on `Groupoid.lean`.
11. `Meno/Basic.lean` rewritten so `ComplexityMeasure`, `SigmaComplexity`, `AdditiveComplexity` are derived from `TypeKernel : HomKernelCat`. `TransitionComplexity` becomes a derived definition from `InfoRatchet`. Pullback gravity is a kernel identity.
12. `Meno.lean` import graph is acyclic and flows as in the preamble.
13. Zero `sorry`. Zero new `axiom`. No phase is "optional" or "future work."

---

## Phase 1 — Sector Action Foundation

**File**: `Meno/SectorAction.lean`

Define:

```lean
structure SectorAction where
  Λ : Type u
  E : Λ → ℝ
  E_zero : ∃ z : Λ, E z = 0
  E_nonneg : ∀ k, 0 ≤ E k
  summable : Summable (fun k => Real.exp (-E k))
```

Define `weight k := Real.exp (-E k)`, `partFn := ∑' k, weight k`, `complexity := Real.log partFn`, `gibbsMass k := weight k / partFn`, `gibbsExpect (f : Λ → ℝ) := ∑' k, f k * gibbsMass k`, `gibbsVariance f := gibbsExpect (fun k => f k * f k) - gibbsExpect f * gibbsExpect f`.

Prove:
- `partFn_pos`
- `partFn_ge_one` (from `E_zero`)
- `complexity_nonneg`
- `gibbsMass_nonneg`
- `summable_gibbsMass`
- `tsum_gibbsMass_eq_one`
- `gibbsExpect_one`
- `gibbsVariance_nonneg`

Define product `(A B : SectorAction) → SectorAction` with `Λ := A.Λ × B.Λ`, `E := fun (a, b) => A.E a + B.E b`. Prove `partFn (A.prod B) = A.partFn * B.partFn` and `complexity (A.prod B) = A.complexity + B.complexity`.

Define disjoint sum `(A B : SectorAction) → SectorAction` analogously. Prove `partFn (A.sum B) = A.partFn + B.partFn`.

**Acceptance**: every analytic lemma currently proved in `Duality.lean` about `GroupoidObj.partFn`, `complexity`, `gibbsMass`, `gibbsExpect`, `gibbsVariance` has a counterpart at the `SectorAction` level. After Phase 3, the `GroupoidObj` proofs reduce to one-line forwarding.

---

## Phase 2 — Quadratic Action and Siegel–Poisson Duality

**File**: `Meno/QuadraticAction.lean`

Define:

```lean
structure QuadraticAction (r : ℕ) where
  Q : Matrix (Fin r) (Fin r) ℝ
  Q_symm : Q.IsSymm
  Q_posDef : Q.PosDef
```

Define `QuadraticAction.energy (A : QuadraticAction r) (k : Fin r → ℤ) : ℝ := ∑ i, ∑ j, A.Q i j * (k i : ℝ) * (k j : ℝ)`.

Prove `QuadraticAction.summable` via positive-definiteness:
- Extract `λ_min > 0` from `Q.PosDef` (Mathlib: `Matrix.PosDef.eigenvalues_pos`).
- Bound `E_Q(k) ≥ λ_min · ‖k‖²` (term-wise).
- Conclude summability of `exp(-λ_min · ‖k‖²)` over `ℤ^r` via standard Gaussian tail bounds.

Define `QuadraticAction.toSectorAction (A : QuadraticAction r) : SectorAction` packaging `(Fin r → ℤ, energy, summable)`. The `E_zero` witness is `0` (energy zero at zero vector). Nonnegativity is from `Q.PosDef.posSemidef`.

Define `IntQuadraticAction := QuadraticAction 1`. Prove `(Fin 1 → ℤ) ≃ ℤ` canonical and the rank-1 reduction:

```lean
theorem IntQuadraticAction.partFn_eq (A : IntQuadraticAction) :
    A.toSectorAction.partFn = ∑' k : ℤ, Real.exp (-(A.Q 0 0) * (k : ℝ)^2)
```

Define the dual:

```lean
def QuadraticAction.dual {r} (A : QuadraticAction r) : QuadraticAction r :=
  { Q := (Real.pi : ℝ)^2 • A.Q⁻¹
    Q_symm := by
      -- inverse of symm is symm; smul preserves symm
    Q_posDef := by
      -- inverse of posDef is posDef; positive-scalar smul preserves posDef
  }
```

Prove `dual_dual : A.dual.dual = A` via `(c · M)⁻¹ = (1/c) · M⁻¹` for `c ≠ 0` and `(M⁻¹)⁻¹ = M` for invertible `M`. Specifically: `(π² · Q⁻¹)⁻¹ = (1/π²) · Q`, so `dual(dual A).Q = π² · (1/π²) · Q = Q`.

Prove the **scalar Siegel–Poisson duality** (rank 1) by relocating the existing `Duality.quadraticPartFn_duality`:

```lean
theorem IntQuadraticAction.duality (A : IntQuadraticAction) :
    (↑A.dual.toSectorAction.partFn : ℂ) =
      (A.Q 0 0 / Real.pi : ℝ) ^ ((1 : ℂ) / 2) * ↑A.toSectorAction.partFn
```

The existing proof goes through `jacobiTheta` and `ModularGroup.S`; relocate verbatim, replacing `quadraticPartFn α` with `(IntQuadraticAction.mk !![α] _ _).toSectorAction.partFn`.

Prove the **matrix Siegel–Poisson duality** (general rank):

```lean
theorem QuadraticAction.duality {r} (A : QuadraticAction r) :
    (↑A.dual.toSectorAction.partFn : ℂ) =
      (A.Q.det / Real.pi^r : ℝ) ^ ((1 : ℂ) / 2) * ↑A.toSectorAction.partFn
```

**Proof strategy.** Multidimensional Poisson summation `∑_{k ∈ ℤ^r} f(k) = ∑_{k ∈ ℤ^r} f̂(k)` applied to the Gaussian `f(x) := exp(-π · xᵀ M x)` with `M := A.Q / π`. The Fourier transform of this Gaussian is `f̂(ξ) = (det M)^{-1/2} · exp(-π · ξᵀ M⁻¹ ξ)`. Substituting and rearranging:

```
Z(A.Q) = ∑_k exp(-kᵀ A.Q k) = ∑_k f(k) = ∑_k f̂(k)
       = (det(A.Q/π))^{-1/2} · ∑_k exp(-π · kᵀ (A.Q/π)⁻¹ k)
       = (π^r / det A.Q)^{1/2} · ∑_k exp(-kᵀ · π² A.Q⁻¹ · k)
       = (π^r / det A.Q)^{1/2} · Z(π² A.Q⁻¹)
       = (π^r / det A.Q)^{1/2} · Z(A.dual.Q)
```

Rearranging: `Z(A.dual.Q) = (det A.Q / π^r)^{1/2} · Z(A.Q)`. The required Mathlib infrastructure:

- `Real.tsum_eq_tsum_fourierIntegral_of_summable` (multidimensional Poisson summation) — in `Mathlib.Analysis.Fourier.PoissonSummation`.
- Multidimensional Gaussian Fourier transform — derived from `Real.fourierIntegral_gaussian` (scalar) by tensor-product through spectral diagonalization of `Q`, or directly from `MeasureTheory.integral_gaussian_pi` extended to matrix exponents using `Matrix.IsHermitian.spectralTheorem`.

If the multivariate Gaussian Fourier identity is not directly in Mathlib, this phase produces it. It is a formal consequence of the scalar identity and the spectral theorem; both are present. No deferral.

Prove `IntQuadraticAction.duality` is the `r = 1` specialization of `QuadraticAction.duality`:
- `Matrix.det !![α] = α` (via `Matrix.det_fin_one`).
- `(α/π)^{1/2} = (det Q / π^1)^{1/2}` when `Q = !![α]`.
- Sector equivalence `(Fin 1 → ℤ) ≃ ℤ` transports the partition functions.

Define `QuadraticAction.selfDual (A : QuadraticAction r) : Prop := A.dual.Q = A.Q`. Prove `selfDual_iff : A.selfDual ↔ A.Q * A.Q = (π : ℝ)^2 • 1`. For `r = 1`: `selfDual ↔ A.Q 0 0 = Real.pi`.

Define `QuadraticAction.dualityFlow (A : QuadraticAction r) : ℝ := A.toSectorAction.complexity - A.dual.toSectorAction.complexity`. Prove `dualityFlow_antisymmetric`, `dualityFlow_zero_iff_selfDual`.

**Acceptance**: `Zeta.lean` migrated to import `QuadraticAction` only (no transitive dependence on `Groupoid.lean`). The Mellin transform restated as integral over `IntQuadraticAction`. Riemann functional equation and Apéry integral reproved through `IntQuadraticAction.duality`. `Hodge.lean`'s `graphPartitionFn` rewrites as a thin wrapper around `QuadraticAction.toSectorAction.partFn` (formalized in Phase 5).

---

## Phase 3 — Loop Kernel as Categorical Presentation

**File**: `Meno/LoopKernel.lean`

Define:

```lean
structure LoopKernelObj where
  C : Type u
  [cat : Category.{v} C]
  base : C
  energy : End base → ℝ
  energy_id : energy (𝟙 base) = 0
  energy_nonneg : ∀ g, 0 ≤ energy g
  summable : Summable (fun g => Real.exp (-energy g))
```

Define `LoopKernelObj.toSectorAction (L : LoopKernelObj) : SectorAction`:

```lean
{ Λ := End L.base
  E := L.energy
  E_zero := ⟨𝟙 L.base, L.energy_id⟩
  E_nonneg := L.energy_nonneg
  summable := L.summable }
```

Forward every `SectorAction` quantity:

```lean
def LoopKernelObj.partFn (L : LoopKernelObj) : ℝ := L.toSectorAction.partFn
def LoopKernelObj.complexity (L : LoopKernelObj) : ℝ := L.toSectorAction.complexity
def LoopKernelObj.gibbsMass (L : LoopKernelObj) (g : End L.base) : ℝ :=
  L.toSectorAction.gibbsMass g
def LoopKernelObj.gibbsExpect (L : LoopKernelObj) (f : End L.base → ℝ) : ℝ :=
  L.toSectorAction.gibbsExpect f
def LoopKernelObj.gibbsVariance (L : LoopKernelObj) (f : End L.base → ℝ) : ℝ :=
  L.toSectorAction.gibbsVariance f
```

**Update `GroupoidObj`** to add `energy_id` and `energy_nonneg` fields. Every existing instance (cycle graphs, abstract `quadraticObj`) trivially satisfies both; the field addition is a no-op for the codebase.

Define the bridge:

```lean
def GroupoidObj.toLoopKernelObj (E : GroupoidObj) : LoopKernelObj :=
{ C := E.G
  base := E.base
  energy := E.energy
  energy_id := E.energy_id
  energy_nonneg := E.energy_nonneg
  summable := E.summable }
```

Prove the bridge lemmas:

```lean
GroupoidObj.partFn E           = LoopKernelObj.partFn E.toLoopKernelObj
GroupoidObj.complexity E       = LoopKernelObj.complexity E.toLoopKernelObj
GroupoidObj.gibbsMass E g      = LoopKernelObj.gibbsMass E.toLoopKernelObj g
GroupoidObj.gibbsExpect E f    = LoopKernelObj.gibbsExpect E.toLoopKernelObj f
GroupoidObj.gibbsVariance E f  = LoopKernelObj.gibbsVariance E.toLoopKernelObj f
```

Each by `rfl` or `unfold; rfl`.

**Acceptance**: `Duality.lean`'s `GroupoidObj.gibbsMass`, `gibbsExpect`, `gibbsVariance` definitions deleted; replaced by `LoopKernelObj` wrappers. `GroupoidObj.partFn_pos`, `summable_gibbsMass`, `gibbsMass_nonneg`, `tsum_gibbsMass` reduced to single-line applications.

---

## Phase 4 — Combinatorial Geodesic Length

**File**: `Meno/Geodesic.lean`

Define:

```lean
class Geodesic (C : Type u) [Category C] where
  length : {X Y : C} → (X ⟶ Y) → ℝ
  length_nonneg : ∀ {X Y} (f : X ⟶ Y), 0 ≤ length f
  length_id : ∀ X, length (𝟙 X) = 0
  length_comp_le : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z),
      length (f ≫ g) ≤ length f + length g
```

This is the Lawvere/metric layer. **Critical separation**: `Geodesic.length` is *not* the source of the analytic quadratic action. For `C_n`, the canonical winding-1 cycle has `length = n` (or in homotopy: sector `k` has geodesic length `n · |k|` since the cycle has no fillable face). The harmonic action of the same sector is `k²/n`, which is **not** the square of the geodesic length. The two are independent invariants connected by a geodesic/harmonic duality (Phase 5).

Provide the canonical simplicial-walk `Geodesic` instance for `Simplicial.SimplicialGroupoid C`:

```lean
instance simplicialGeodesic (C : Complex V) (hsym : C.toGraph.Symmetric) :
    Geodesic (SimplicialGroupoid C) where
  length [p] := ⨅ q ∈ HomotopyClass₂ C u v with [q] = [p], q.length
  ...
```

with the homotopy-invariance proof: face reductions never increase length, so the infimum is the minimum length representative within the homotopy class.

Prove `Simplicial.cycleGraph_geodesic_eq_n` as the `Geodesic` instance lemma:

```lean
theorem cycleGraph_canonical_length (n : ℕ) (hn : n ≥ 3) :
    Geodesic.length (canonicalCycleMorphism n hn) = n
```

Define `Geodesic.geodesicMass [Category C] [Geodesic C] (X : C) : ℝ` as the length of a chosen nontrivial endomorphism witness.

**Acceptance**: `Simplicial.cycleGraph_geodesic_eq_n` and related geodesic statements restated as `Geodesic` instance lemmas. The combinatorial mass `n` for `C_n` is exhibited at the `Geodesic` layer with no analytic content involved.

---

## Phase 5 — Harmonic Form and the Variational Identity

**File**: `Meno/HarmonicForm.lean`

For a finite graph `G` with edge cochains `EC1 G`, restate and extend the existing Hodge content of `Simplicial.lean` and `Hodge.lean`:

- The inner product on `EC1 G`: `⟨σ, τ⟩ := (1/2) · ∑_{i,j} σ(i,j) · τ(i,j)`.
- The boundary `∂ : EC1 G → V → ℝ` summing oriented contributions.
- The harmonic subspace `Harm G := ker ∂`.
- The cycle subspace `Cyc G ⊆ EC1 G` and the boundary subspace `Bdy G ⊆ Cyc G`.
- The first homology `H₁ G := Cyc G / Bdy G ≅ ℤ^{b₁(G)}`.

For each integer winding class `k ∈ Fin (b₁ G) → ℤ`, define `harmonicRep G k : EC1 G` as the unique harmonic 1-cochain whose winding-coordinates equal `k`. Existence and uniqueness follow from the Hodge orthogonal decomposition `EC1 G = Harm G ⊕ image(d)`.

Prove the **variational identity** (load-bearing theorem):

```lean
theorem harmonic_energy_min {G : Graph V} [Fintype V] [DecidableEq V]
    (k : Fin (b₁ G) → ℤ) :
    EC1.energy (harmonicRep G k) =
      ⨅ ω : { ω : EC1 G // winding ω = k }, EC1.energy ω.val
```

**Proof.** Orthogonal decomposition gives `ω = harmonicRep G k + δ` with `δ ∈ image(d)`. Then `‖ω‖² = ‖harmonicRep G k‖² + ‖δ‖²` (Pythagoras), so `‖ω‖² ≥ ‖harmonicRep G k‖²` with equality iff `δ = 0`. The infimum is attained at the harmonic representative.

Define the **harmonic Gram form**:

```lean
def harmonicGramForm (G : Graph V) [Fintype V] [DecidableEq V] :
    Matrix (Fin (b₁ G)) (Fin (b₁ G)) ℝ :=
  fun i j => ⟨harmonicRep G (Pi.single i 1), harmonicRep G (Pi.single j 1)⟩
```

Prove `harmonicGramForm G` is symmetric and positive-definite, and:

```lean
theorem energy_eq_gram (k : Fin (b₁ G) → ℤ) :
    EC1.energy (harmonicRep G k) =
      ∑ i, ∑ j, harmonicGramForm G i j * (k i : ℝ) * (k j : ℝ)
```

For `C_n` (cycle graph): prove `b₁(cycleGraph n) = 1` and `harmonicGramForm (cycleGraph n) = !![1/n]`. The uniform-flow harmonic 1-cochain assigns `k/n` to each of `n` edges; energy is `(1/2) · ∑ (k/n)² · 2 = k²/n` (the factor of 2 accounts for the symmetric inner product convention). The Gram form's single entry is `1/n`.

Define **graph-to-quadratic-action**:

```lean
def Graph.toQuadraticAction (G : Graph V) [Fintype V] [DecidableEq V] :
    QuadraticAction (b₁ G) :=
{ Q := harmonicGramForm G
  Q_symm := harmonic_gram_symm G
  Q_posDef := harmonic_gram_posDef G }
```

For `C_n`: `(cycleGraph n).toQuadraticAction = ⟨!![1/n], _, _⟩`, definitionally `IntQuadraticAction`.

Prove the **partition-function-matches-existing-graph-partFn** theorem:

```lean
theorem Graph.partFn_eq_existing (G : Graph V) [Fintype V] [DecidableEq V]
    (hsum : ...) :
    G.toQuadraticAction.toSectorAction.partFn = Hodge.graphPartitionFn (b₁ G) ... hsum
```

**Acceptance**: `Hodge.graphPartitionFn` rewrites as `Graph.toQuadraticAction.toSectorAction.partFn`. The harmonic-mass identity `1/n` is `Q.det` for the cycle graph. The variational identity is proved without depending on `LoopKernelObj` or `Duality.lean`.

---

## Phase 6 — Sector Presentations

**File**: `Meno/SectorPresentation.lean`

Define:

```lean
structure SectorPresentation (L : LoopKernelObj) (r : ℕ) where
  coord : (End L.base) ≃* (Fin r → ℤ)
  Q : Matrix (Fin r) (Fin r) ℝ
  Q_symm : Q.IsSymm
  Q_posDef : Q.PosDef
  energy_eq : ∀ g, L.energy g =
    ∑ i, ∑ j, Q i j * (coord g i : ℝ) * (coord g j : ℝ)
```

The `coord` field is `MulEquiv`: monoid composition in `End L.base` corresponds to addition in the lattice. Bare `Equiv` is insufficient because the structural duality requires composition-respect.

Prove the partition-function transport:

```lean
theorem SectorPresentation.partFn_eq {L r} (P : SectorPresentation L r) :
    L.toSectorAction.partFn =
      (QuadraticAction.mk P.Q P.Q_symm P.Q_posDef).toSectorAction.partFn
```

via re-indexing along `P.coord`.

Construct the **cycle-graph presentation**: for `Groupoid.cycleCanonicalObj n hn`, exhibit `End base ≃* ℤ` (winding equivalence from `Simplicial.lean`) and the canonical embedding `ℤ ≃* (Fin 1 → ℤ)`, with `Q := !![1/n]`. The energy equation `(1/n) · k² = k²/n` matches the existing cycle energy. This presentation realizes the cycle groupoid as a rank-1 quadratic action.

Construct the **abstract-quadratic-object presentation**: for `Duality.quadraticObj α hα`, exhibit the equivalent presentation with `Q := !![α]`.

Define the **categorical dual via presentation**:

```lean
def LoopKernelObj.dualVia {L r} (P : SectorPresentation L r) : LoopKernelObj :=
  -- transport (QuadraticAction.dual ⟨P.Q, _, _⟩) back through P.coord
  { C := L.C
    base := L.base
    energy := fun g =>
      ∑ i, ∑ j, (Real.pi^2 • P.Q⁻¹) i j * (P.coord g i : ℝ) * (P.coord g j : ℝ)
    energy_id := by simp [P.coord.map_one]
    energy_nonneg := by ...
    summable := ... }
```

Prove the **categorical duality theorem**:

```lean
theorem LoopKernelObj.dualVia_partFn {L r} (P : SectorPresentation L r) :
    (↑(L.dualVia P).toSectorAction.partFn : ℂ) =
      (P.Q.det / Real.pi^r : ℝ) ^ ((1 : ℂ) / 2) *
      ↑L.toSectorAction.partFn
```

via Phase 2's `QuadraticAction.duality` and the partition-function transport.

**Acceptance**: `Duality.lean`'s `GroupoidObj.dual`, `dual_partFn`, `quadraticObj_dual_equiv`, `dual_dual_equiv` all rewrite to dispatch through `SectorPresentation`. Each is at most three lines after the dispatch.

---

## Phase 7 — Matter as Sector Homology with Positive Minimum Action

**File**: `Meno/MatterHomology.lean`

For a 2-complex `C` (using existing `Simplicial.Complex` infrastructure), define **sector homology**:

```lean
def SectorHomology₁ (C : Complex V) [Fintype V] [DecidableEq V] :
    AddCommGroup :=
  -- ℤ-module quotient: 1-cycles in the graph C.toGraph
  -- modulo 1-boundaries from filled faces
  Cyc (C.toGraph) ⧸ Bdy_through_faces C
```

This is ordinary cellular `H₁` adapted to the 2-complex structure. Reuse the existing winding-number infrastructure from `Simplicial.lean`.

For each class `c ∈ SectorHomology₁ C`, define the **minimum harmonic action**:

```lean
def minimumAction (C : Complex V) [Fintype V] [DecidableEq V]
    (c : SectorHomology₁ C) : ℝ :=
  ⨅ ω : { ω : EC1 C.toGraph // [ω] = c }, EC1.energy ω.val
```

By Phase 5's `harmonic_energy_min`, the infimum is attained by the harmonic representative.

Define a **matter sector**:

```lean
structure MatterSector (C : Complex V) [Fintype V] [DecidableEq V] where
  cls : SectorHomology₁ C
  nontrivial : cls ≠ 0
  positive_action : 0 < minimumAction C cls
```

Prove `cycleGraph_canonical_is_matter`:

```lean
theorem cycleGraph_canonical_is_matter (n : ℕ) (hn : n ≥ 3) :
    Nonempty (MatterSector (CycleComplex n hn)) := by
  -- nontrivial follows from cycleGraph_not_contractible
  -- positive_action follows from minimumAction = 1/n > 0
  ...
```

Prove **`binding_kills_matter`** (the existing `binding_releases_mass`, restated):

```lean
theorem binding_kills_matter (C₁ C₂ : Complex V)
    (c : SectorHomology₁ C₁) (hc : c ≠ 0)
    (h_killed : SectorHomology₁.map (Complex.unionLeft C₁ C₂) c = 0) :
    bindingEnergy C₁ C₂ c = minimumAction C₁ c
```

When a homology class survives in `C₁` but is killed by new faces in `C₁ ∪ C₂`, the binding energy released equals the harmonic minimum action of `c` in `C₁`.

Prove the **equivalence with existing simplicial proofs**:

```lean
theorem matter_simplicial_eq_homological (n : ℕ) (hn : n ≥ 3) :
    Simplicial.canonicalCycleMass n hn =
      minimumAction (CycleComplex n hn)
        (cycleGraph_canonical_class n hn)
```

Both views are theorems. The simplicial proof remains; the homological proof is added.

**Magnitude homology is not defined in this file or anywhere in the plan.** Meno's matter content is `H₁` plus the Phase 5 harmonic minimum theorem; magnitude homology would require a separate theorem identifying these with magnitude-homology classes and is not promised.

**Acceptance**: `Simplicial.matter_noncontractible` and `Simplicial.binding_releases_mass` have homological reproofs through `MatterSector`. The two formulations are proved equal.

---

## Phase 8 — Fiber Information Cost and the Ratchet

**File**: `Meno/InfoRatchet.lean`

Define **fiber information cost** for a function:

```lean
def fiberInfoCost {A B : Type u} [Fintype A] [Fintype B] (f : A → B) : ℝ :=
  ∑ b : B, Real.log (Nat.card (f ⁻¹' {b}) : ℝ).toNNReal.toReal
```

(Singleton fibers contribute `log 1 = 0`; empty fibers do not occur in the image.)

Prove `fiberInfoCost_zero_iff : fiberInfoCost f = 0 ↔ Function.Injective f`.

Define **description cost** of a function `f : A → B` as the description length of the choice table:

```lean
def descriptionCost {A B : Type u} [Fintype A] [Fintype B] (f : A → B) : ℝ :=
  (Fintype.card A : ℝ) * Real.log (Fintype.card B : ℝ)
```

(One out of `|B|^|A|` total functions; each requires `|A| · log |B|` bits.)

Define **section description cost** of a section `s : B → A` of a many-to-one `f`:

```lean
def sectionCost {A B : Type u} [Fintype A] [Fintype B]
    (f : A → B) (s : B → A) (hs : ∀ b, f (s b) = b) : ℝ :=
  descriptionCost s + 0  -- the section table itself
```

Prove the **fiber-information lower bound on the gap**:

```lean
theorem section_cost_gap_ge_fiberInfo
    {A B : Type u} [Fintype A] [Fintype B] (f : A → B)
    (s : B → A) (hs : ∀ b, f (s b) = b) :
    sectionCost f s hs - descriptionCost f ≥ fiberInfoCost f
```

The proof: any section is a choice function over fibers; the minimum description length for specifying such a choice is `∑_b log |fiber(b)|`.

**The Ratchet Theorem**:

```lean
theorem ratchet_theorem {A B : Type u} [Fintype A] [Fintype B] (f : A → B)
    (hf : ¬ Function.Injective f)
    (s : B → A) (hs : ∀ b, f (s b) = b) :
    sectionCost f s hs > descriptionCost f
```

Proof: by `fiberInfoCost_zero_iff` and `hf`, `fiberInfoCost f > 0`. By `section_cost_gap_ge_fiberInfo`, the gap is at least this positive amount.

**Note on categorical generalization**: the ratchet is *not* a statement about morphism energies under a functor's section, because functors preserve identities and identity energy is zero (Phase 3's `energy_id`). The asymmetry lives in the *description cost of the section's choice function*, which is independent of the morphism-energy data. This corrects a category mistake that would otherwise yield `0 > 0`.

Reconstruct the existing `SGD.TransitionComplexity` Landauer instance:

```lean
noncomputable instance Landauer.fromRatchet : SGD.TransitionComplexity where
  transitionCost f :=
    -- value chosen to match the existing convention:
    --   injective: 2 (preserves all distinctions; full description)
    --   non-injective: 1 (collapses; reduced description)
    if Function.Injective f then 2 else 1
  transitionCost_pos := by intros; split <;> omega
  ratchet f r hfr hni := by
    have hr_inj : Function.Injective r := ...
    have : ¬ Function.Injective f := hni
    -- The cost asymmetry (2 vs 1) is a special case of the
    -- fiberInfoCost gap; the existing instance value is one
    -- convention consistent with the ratchet theorem.
    show (if Function.Injective r then 2 else 1) >
         (if Function.Injective f then 2 else 1)
    rw [if_pos hr_inj, if_neg hni]; norm_num
  injective_reversible f r hfr hfi := ...
```

The existing Landauer instance is **propositionally** the same as this reconstruction. The structural claim is that the existing axiom `ratchet` is now a *consequence* of the fiber-information-cost framework, applied with one specific cost convention.

Delete `Basic.lean`'s `TransitionComplexity` *class declaration*. Replace with:

```lean
/-- TransitionComplexity is now derived from InfoRatchet.fiberInfoCost. -/
def SGD.TransitionComplexity := InfoRatchet.RatchetCostModel
```

(See Phase 10 for the full restructuring.)

**Acceptance**: `Basic.lean`'s `TransitionComplexity` class is removed; the Landauer instance is reconstructed as a `RatchetCostModel` from `InfoRatchet`. The existing `ratchet` axiom is proved as `ratchet_theorem` specialized to the chosen cost convention.

---

## Phase 9 — Hom-Kernel Category and Magnitude

**File**: `Meno/HomKernel.lean`

Define the cleanroom generalization where every Hom-cell carries a sector action:

```lean
structure HomKernelCat where
  C : Type u
  [cat : Category.{v} C]
  homAction : ∀ X Y : C, SectorAction
  homAction_lattice_eq : ∀ X Y, (homAction X Y).Λ = (X ⟶ Y)
  energy_id : ∀ X, (homAction X X).E (cast (homAction_lattice_eq X X).symm (𝟙 X)) = 0
```

The `homAction_lattice_eq` field is typically `rfl` by construction.

Define **per-cell partition function** `Z X Y := (homAction X Y).partFn` and, for finite `C`, the **kernel matrix** `Z : Matrix C C ℝ := fun X Y => K.Z X Y`.

Define **magnitude** (Leinster):

```lean
def HomKernelCat.magnitude [Fintype C] (K : HomKernelCat)
    (h : K.kernelMatrix.Invertible) : ℝ :=
  ∑ X, ∑ Y, (K.kernelMatrix⁻¹) X Y
```

Equivalently `1ᵀ Z⁻¹ 1`.

Prove **inclusion-exclusion**: for a coproduct of `HomKernelCat`s with no inter-component morphisms, magnitudes add.

Define the **base slice**:

```lean
def HomKernelCat.atBase (K : HomKernelCat) (X : K.C) : LoopKernelObj :=
{ C := K.C
  base := X
  energy := fun g => (K.homAction X X).E (cast (K.homAction_lattice_eq X X).symm g)
  energy_id := K.energy_id X
  energy_nonneg := ...
  summable := ... }
```

Prove `(K.atBase X).toSectorAction = K.homAction X X` definitionally.

Construct the **simplicial HomKernelCat**: for a 2-complex `C` with harmonic energy on each Hom-cell, exhibit a `HomKernelCat` whose `homAction X Y` is the SectorAction on homotopy classes from `X` to `Y` with harmonic-minimum energy on each class.

**Note on architecture**: `HomKernelCat` is *not* the foundation of the project — `SectorAction` is. `HomKernelCat` is the generalization required to define magnitude (a global readout that needs all Hom-cells). For the Meno content covered by `Duality.lean`, `Hodge.lean`, and `Zeta.lean`, the single-base-slice `LoopKernelObj` is enough; `HomKernelCat` exists for the magnitude readout and for forward-compatibility with global invariants.

**Acceptance**: `LoopKernelObj` is recovered as `HomKernelCat.atBase`. Magnitude is defined and computed for the cycle complex via inclusion-exclusion.

---

## Phase 10 — Basic.lean Reorganization

**Files**: restructured `Meno/Basic.lean`, restructured `Meno.lean`

**Rewrite `Basic.lean`.**

Define the **discrete-enrichment kernel** on types:

```lean
def TypeKernel : HomKernelCat :=
{ C := Type u
  cat := Type.typeCategory       -- discrete? actually small functions; see below
  homAction := fun A B => discreteFunctionSectorAction A B
  ...
}
```

where `discreteFunctionSectorAction A B` has `Λ = A → B` and energy `E f := Real.log (Nat.card (Set.image f Set.univ) : ℝ)` (or another cardinality-derived energy that recovers `C(A) = log |A|`).

Replace the `ComplexityMeasure`, `SigmaComplexity`, `AdditiveComplexity` *classes* with theorems on `TypeKernel`:

```lean
theorem typeComplexity_subadditive_prod (A B : Type u) :
    TypeKernel.atBase (A × B) .toSectorAction.complexity ≤
      TypeKernel.atBase A .toSectorAction.complexity +
      TypeKernel.atBase B .toSectorAction.complexity

theorem typeComplexity_additive_prod (A B : Type u) :
    TypeKernel.atBase (A × B) .toSectorAction.complexity =
      TypeKernel.atBase A .toSectorAction.complexity +
      TypeKernel.atBase B .toSectorAction.complexity
```

Restate the **refactoring bound** and **gravity** as kernel identities:

```lean
theorem refactoring_bound_kernel
    {A B D : Type u} (f : A → D) (g : B → D)
    [Nonempty D] [BddAbove ...] :
    TypeKernel.atBase (Pullback f g) .toSectorAction.complexity ≤
      TypeKernel.atBase D .toSectorAction.complexity +
      (⨆ d, TypeKernel.atBase (Fiber f d) .toSectorAction.complexity +
            TypeKernel.atBase (Fiber g d) .toSectorAction.complexity)

theorem gravity_kernel {A B D F G : Type u} (f : A → D) (g : B → D)
    (ef : ∀ d, Fiber f d ≃ F) (eg : ∀ d, Fiber g d ≃ G) :
    TypeKernel.atBase (Pullback f g) .toSectorAction.complexity +
      TypeKernel.atBase D .toSectorAction.complexity =
    TypeKernel.atBase A .toSectorAction.complexity +
      TypeKernel.atBase B .toSectorAction.complexity
```

The original `refactoring_bound` and `gravity` are direct corollaries.

Preserve `AdditiveComplexityOn` as a derived structure: it is the monoid homomorphism `(Type, ×, PUnit) → (ℝ, +, 0)` underlying `TypeKernel`. `algebraic_gravity` is a consequence of `gravity_kernel`.

Realize `TransitionComplexity` as a `RatchetCostModel` from Phase 8.

**Rewrite `Meno.lean`** with the import order:

```lean
import Meno.SectorAction
import Meno.QuadraticAction
import Meno.LoopKernel
import Meno.Geodesic
import Meno.HarmonicForm
import Meno.SectorPresentation
import Meno.MatterHomology
import Meno.InfoRatchet
import Meno.HomKernel
import Meno.Simplicial            -- now upstream of LoopKernel-using files, downstream of foundational primitives
import Meno.Groupoid              -- now provides SectorPresentation instances
import Meno.Duality               -- now reads off SectorPresentation duality
import Meno.Hodge                 -- now reads off HarmonicForm
import Meno.Zeta                  -- depends only on QuadraticAction
import Meno.Basic                 -- now the discrete-enrichment realization
import Meno.Instances
```

No file imports `Basic.lean` upstream of `Simplicial.lean`. The dependency graph is acyclic. Analytic primitives are defined before any specific instance.

**Acceptance**: `lake build` succeeds with no `sorry`, no new `axiom` beyond Mathlib classics, no import cycles. The 13 Goals are all realized.

---

## Falsification

The plan fails — and only fails — if any of:

1. **Phase 1**: `SectorAction` cannot package `GroupoidObj`'s analytic content without extra hypotheses. (It can: `GroupoidObj`'s fields map directly to `SectorAction`'s, with `energy_id` and `energy_nonneg` added to `GroupoidObj` as a no-op enrichment.)

2. **Phase 2 (scalar)**: `IntQuadraticAction.duality` cannot be obtained by relocating the existing `quadraticPartFn_duality` proof. (It can: the existing proof uses `jacobiTheta` and `ModularGroup.S`, both Mathlib facts independent of groupoid structure.)

3. **Phase 2 (matrix)**: `QuadraticAction.duality` proof requires Mathlib infrastructure beyond what `Mathlib.Analysis.Fourier.PoissonSummation` plus `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral` plus `Matrix.IsHermitian.spectralTheorem` provide. If such infrastructure is needed, this phase delivers it as part of the plan rather than as a precondition.

4. **Phase 3**: Bridge lemmas from `GroupoidObj` to `LoopKernelObj` are not `rfl` or near-`rfl`. This would mean `GroupoidObj` and `LoopKernelObj` carry different content; the abstraction is wrong.

5. **Phase 5**: `harmonic_energy_min` fails for the standard inner product on `EC1`. This would contradict the Hodge orthogonal decomposition.

6. **Phase 6**: The cycle-graph `SectorPresentation` does not satisfy `energy_eq` with `Q = !![1/n]`. This would mean cycle-graph energy is not `kᵀ Q k` for `Q = (1/n)`.

7. **Phase 7**: `cycleGraph_canonical_is_matter` cannot be proved from existing `cycleGraph_not_contractible` plus `harmonic_energy_min` plus the harmonic value `1/n > 0`. This would mean the homological reformulation of matter is incompatible with the existing simplicial obstruction.

8. **Phase 8**: `ratchet_theorem` does not specialize to the existing Landauer instance under the chosen cost convention. This would mean fiber-information cost is not the right reframing of `TransitionComplexity`.

9. **Phase 10**: `refactoring_bound_kernel` and `gravity_kernel` cannot be proved on `TypeKernel`. This would mean the discrete-enrichment kernel is not the correct sector-action realization of the type-level hierarchy.

Each failure mode is a single-theorem check. Every signature above is realized in the final repository. Every proof is complete. No phase is optional. No phase has a "later." No phase is "future work."

---

**End of plan.**

---

## Implementation Summary (Session 1, 2026-06-08)

A first pass at this plan was executed in a single session, producing 9 new
Lean files (~1100 LOC) that compile clean with **zero `sorry` and zero new
axioms**, alongside the existing 8 files which remain untouched. The full
project builds (`lake build Meno` → 3311 jobs, success). The summary below
records what landed, what was deferred and why, and the architectural
decisions made along the way.

### Status of each phase

| Phase | File | LOC | Status |
|------:|:-----|----:|:-------|
| 1 | `Meno/SectorAction.lean` | 239 | **Complete.** All 8 plan-mandated lemmas proved; product and disjoint-sum combinators with factorization/additivity proved. |
| 2 | `Meno/QuadraticAction.lean` | 221 | **Partial.** Structure + `ofScalar` + `scalarPartFn` + scalar T-duality fully proved. Matrix Siegel–Poisson duality **not** proved (gap below). |
| 3 | `Meno/LoopKernel.lean` | 95 | **Complete.** `LoopKernelObj`, `toSectorAction`, all forwarded lemmas. `GroupoidObj.toLoopKernelObj` bridge deferred. |
| 4 | `Meno/Geodesic.lean` | 62 | **Interface only.** Class declaration + `selfMass` + `length_comp_three`. Simplicial-walk instance and `cycleGraph_canonical_length` deferred. |
| 5 | `Meno/HarmonicForm.lean` | 72 | **Interface only.** `HarmonicGramData` structure + `toQuadraticAction` builder. Variational identity `harmonic_energy_min` and concrete cycle-graph Gram form deferred. |
| 6 | `Meno/SectorPresentation.lean` | 96 | **Complete (abstract).** `SectorPresentation` structure with `coord_one` / `coord_comp` + `partFn_eq` + `complexity_eq` + summability transport. Concrete cycle and `quadraticObj` presentations deferred. Categorical dual via presentation deferred. |
| 7 | `Meno/MatterHomology.lean` | 89 | **Interface only.** `MatterSector` over abstract `HarmonicGramData` + `ofNonzero` constructor + `exists_matter` for rank ≥ 1. Concrete `cycleGraph_canonical_is_matter` and `binding_kills_matter` deferred. |
| 8 | `Meno/InfoRatchet.lean` | 93 | **Complete (clean form).** `fiberInfoCost` + `descriptionCost` + `sectionCost` + ratchet identity. Landauer instance reconstruction in `SGD.TransitionComplexity` deferred (orientation of inequality is incompatible — see notes below). |
| 9 | `Meno/HomKernel.lean` | 70 | **Partial.** `HomKernelCat` + `atBase` + `homPartFn`. Magnitude `1ᵀ Z⁻¹ 1` and inclusion-exclusion deferred. |
| 10 | `Meno.lean` | 12 | **Partial.** Import graph updated to put new analytic primitives upstream of legacy layers. **`Meno/Basic.lean` rewrite not done** — see notes. |

### Architectural decisions worth recording

**1. `summable` is a field of `QuadraticAction`, not a derived theorem.**
The plan calls for `QuadraticAction.summable` to be derived from `Q.PosDef`
via the eigenvalue lower bound `kᵀQk ≥ λ_min ‖k‖²` and standard Gaussian
tail bounds. The derivation works mathematically but in Lean requires
either:
- an induction on `r` factoring `Fin r → ℤ` as `ℤ × (Fin (r-1) → ℤ)` and
  using `Summable.mul_of_nonneg` from `Mathlib.Analysis.Normed.Ring.InfiniteSum`,
  or
- a multidim Gaussian-tail summability lemma that does not exist in
  Mathlib at that name.

Both routes are tractable but each takes substantial effort to get right
under universe and pi-type bookkeeping. The pragmatic call was to mirror
`GroupoidObj`'s existing field-based summability and defer the derivation.
A constructor `QuadraticAction.of_posDef` proving summability from PosDef is
a natural follow-up.

**2. `GroupoidObj` was not modified.** The plan asks for adding
`energy_id` and `energy_nonneg` fields to `GroupoidObj` and claims this
is a "no-op" for existing instances. It is not: `GroupoidObj.dual` and
`quadraticObj` take a bare `Equiv` `End ≃ ℤ` that does not a priori send
identity to 0, so the field addition needs each call site to supply a
proof (5 sites). The cleaner interim is to leave `GroupoidObj` alone,
introduce `LoopKernelObj` as the genuine upstream primitive carrying
the two extra fields, and defer the bridge until Phase 6's `MulEquiv`-style
`coord` ships in the legacy layer.

**3. The matrix Siegel–Poisson duality is the largest deferred theorem.**
Mathlib has scalar Poisson summation (`SchwartzMap.tsum_eq_tsum_fourier`)
and the multivariate Gaussian Fourier transform
(`fourier_gaussian_innerProductSpace`), but does **not** have a
multidimensional Poisson summation formula over an integer lattice in
`EuclideanSpace ℝ (Fin r)`. Spectral diagonalisation of `Q` does not
rescue us: orthogonal transformations of `ℝ^r` do not preserve `ℤ^r`,
so the lattice is not invariant under the change of basis that
diagonalises `Q`. The honest paths forward are:
- **(a)** Build multidim Poisson summation in Mathlib via Schwartz
  theory on `EuclideanSpace` together with `ZLattice` (substantial,
  multi-week effort but a worthwhile Mathlib contribution).
- **(b)** Restrict the theorem to **diagonal** `Q`, where the lattice
  factorises as `∏ᵢ ℤ` and the duality reduces to a product of scalar
  dualities. This handles graphs whose harmonic Gram form is diagonal
  (rare in the wild) and provides a useful checkpoint.
- **(c)** Generalise the sector lattice from `ℤ^r` to an arbitrary
  rank-`r` `ZLattice` in `EuclideanSpace`, restate the duality, and
  prove multidim Poisson summation at that level. This is essentially
  (a) with extra plumbing.

The scalar T-duality (rank 1) is fully proved and is sufficient to drive
Zeta / Duality / Hodge in the legacy layer at their current ambition.

**4. The `InfoRatchet` / Landauer reconciliation has a sign issue in the
plan.** The plan asks to reconstruct the existing
`SGD.TransitionComplexity` Landauer instance (`cost(injective) = 2`,
`cost(non-injective) = 1`) so that its `ratchet` axiom becomes a
*consequence* of the fiber-information framework "with one specific cost
convention." This does not work in the obvious way:

- The Landauer convention gives `cost(right-inverse r) > cost(non-injective f)`
  (2 > 1).
- The fiber-info framework, in the form `cost g := descriptionCost g
  + fiberInfoCost g`, gives `cost(f) > cost(r)` (because `fiberInfoCost
  f > 0 = fiberInfoCost r`).

These inequalities point in *opposite* directions. Both are physically
meaningful in their own context — Landauer is about computational
irreversibility of the *map*; fiber-info is about information needed to
*reconstruct* the pre-image. Forcing one to be a special case of the
other requires either (i) reinterpreting the Landauer convention so the
"cost" is actually the *section description cost minus the map description
cost*, or (ii) a custom cost convention that's neither standard Landauer
nor pure fiber-info.

The implementation took option (iii): write the fiber-info framework
cleanly with the standard identity `sectionCost − descriptionCost
= fiberInfoCost`, and leave the `TransitionComplexity` class untouched.
A reconciliation (under any of the readings above) is a separate
conceptual exercise the plan should resolve before being literally
implemented.

**5. Phase 5 and 7 are interface-only because the variational and
homological content is graph-specific.** Proving
`harmonic_energy_min : EC1.energy (harmonicRep G k) = ⨅ ω with winding ω
= k, EC1.energy ω.val` requires committing to a specific definition of
`EC1 G`, `harmonicRep`, the winding map, the inner product, and the
boundary operator — none of which are in Mathlib at this name and all of
which would commit `HarmonicForm.lean` to one graph encoding. The
`HarmonicGramData` interface is the smallest piece that downstream code
(`SectorPresentation`, `MatterHomology`) genuinely needs: the Gram form
plus its analytic properties. Concrete graph instances (cycle, complete,
arbitrary finite) supply the Gram form and prove the variational identity
at their own level. The cycle-graph case in particular only needs:
`b₁(cycleGraph n) = 1`, `Q = !![1/n]`, and summability — straightforward
once integrated with `Simplicial.lean`.

### Mathlib quirks discovered

These cost real time during the session and are worth noting for follow-up:

- **`tsum_add` / `tsum_sub` are methods on `Summable`, not standalone
  lemmas.** Current Mathlib uses `(hf : Summable f).tsum_add (hg
  : Summable g)` rather than `tsum_add hf hg`. The old name no longer
  resolves.
- **`Matrix.PosSemidef` is defined over `Finsupp` (`n →₀ R`) by default,
  not `n → R`.** For finite index types, you have to detour through
  `posSemidef_iff_dotProduct_mulVec` or `Matrix.PosSemidef.dotProduct_mulVec_nonneg`
  to get the natural `n → R` form. Same for `PosDef`.
- **`Equiv.summable_iff` orientation.** Given `e : α ≃ β` and a function
  `f : β → M`, `e.summable_iff.mpr` produces `Summable (f ∘ e) : α →
  M`. Going the other direction requires `e.symm.summable_iff.mpr`.
- **`Nat.card_le_one_iff_subsingleton` is in namespace `ENat`, not
  `Nat`.** The namespace structure in `Mathlib.SetTheory.Cardinal.Finite`
  is non-obvious; the right idiom for empty/singleton fibers is
  `by_cases hne : Nonempty _; · use Nat.card_unique; · use Nat.card_eq_zero.mpr`.
- **Class declarations referencing their own fields need explicit type
  annotations.** A class field `length_nonneg : ∀ {X Y} (f : X ⟶ Y), 0
  ≤ length f` failed to elaborate without `(0 : ℝ)`; the references to
  `length` and `length_id` from inside the class body produced unknown-identifier
  errors. Working around: refer to the namespaced `Geodesic.length` from
  *outside* the class block, in subsequent lemmas, and accept that
  in-class self-references have caveats.
- **`linarith` requires `import Mathlib.Tactic.Linarith` explicitly.**
  It is not pulled in transitively by `Mathlib.Data.Real.Basic`.

### Concrete next steps (ordered by leverage)

1. **Integrate `Simplicial.lean`'s cycle-graph machinery with
   `HarmonicForm.lean`.** This produces a concrete
   `cycleHarmonicGramData (n : ℕ) (hn : n ≥ 3) : HarmonicGramData
   (Fin n)` with `Q = !![1/n]`. Validates the abstract interface and
   immediately yields `MatterSector` instances for `C_n` via
   `MatterSector.ofNonzero`. ETA: 1–2 sessions.
2. **Provide `GroupoidObj.toLoopKernelObj` in a bridge file.** Takes
   `energy_id` and `energy_nonneg` as explicit hypotheses; each of the
   5 existing `GroupoidObj` instances supplies them in 1–3 lines.
   Lets `Duality.lean`'s analytic lemmas reduce to
   `LoopKernelObj` applications. ETA: 1 session.
3. **Construct `SectorPresentation (quadraticObj α hα) 1`** with `Q =
   !![α]` and the canonical winding. Validates the `coord_one` /
   `coord_comp` structural piece on a concrete case. ETA: 1 session.
4. **Build the matrix Siegel–Poisson duality for diagonal `Q` only.**
   Reduces to a product of scalar dualities via `prod` of `IntQuadraticAction`s.
   Useful intermediate even before full multidim Poisson lands. ETA:
   2–3 sessions.
5. **Migrate `Basic.lean`'s `ComplexityMeasure` / `SigmaComplexity`
   / `AdditiveComplexity` classes onto `TypeKernel : HomKernelCat`.**
   The discrete-enrichment kernel was sketched in the plan but no
   construction was attempted; this is non-trivial because the energy
   on `Type → Type` morphisms needs a cardinality-derived definition that
   recovers `C(A) = log |A|` on objects. ETA: 2–4 sessions.
6. **Build multidim Poisson summation in Mathlib.** This is a major
   contribution but unlocks the matrix Siegel–Poisson duality at its
   intended generality. Requires Schwartz theory on `EuclideanSpace ℝ
   (Fin r)` and the `ZLattice` machinery already in
   `Mathlib.Algebra.Module.ZLattice`. ETA: multi-week, possibly
   collaborative.

### Falsification audit (plan §Falsification)

| # | Claim | Status |
|--:|:------|:-------|
| 1 | `SectorAction` packages `GroupoidObj`'s analytic content without extra hypotheses. | **Validated** — `LoopKernelObj` (the upstream of `GroupoidObj`) projects to `SectorAction` rfl-cleanly. The two extra fields needed for `GroupoidObj` to project directly are the same two that make `LoopKernelObj` work. |
| 2 | Scalar `IntQuadraticAction.duality` relocates verbatim. | **Validated** — `scalarPartFn_duality` is the relocated proof; no Mathlib facts needed beyond what was already used. |
| 3 | Matrix `QuadraticAction.duality` proof requires only Poisson + Gaussian Fourier + spectral theorem. | **Falsified in the strict reading** — Mathlib does not have multidim Poisson summation over `ℤ^r` in `EuclideanSpace`, and spectral diagonalisation does not preserve the integer lattice. The proof requires a genuine new Mathlib component, not just composition. |
| 4 | `GroupoidObj` → `LoopKernelObj` bridge is `rfl`. | **Validated structurally** — once `energy_id` and `energy_nonneg` are supplied (as extra hypotheses in the deferred bridge), the conversion is one line each. |
| 5 | `harmonic_energy_min` holds for standard `EC1` inner product. | **Not tested in code** — the abstract `HarmonicGramData` interface presupposes the variational identity rather than proving it. Concrete graph instantiation will test this. |
| 6 | Cycle-graph `SectorPresentation` has `Q = !![1/n]`. | **Not tested in code** — deferred to the concrete cycle instance. |
| 7 | `cycleGraph_canonical_is_matter` from `cycleGraph_not_contractible` + `harmonic_energy_min` + harmonic value `1/n > 0`. | **Architecturally validated** — `MatterSector.ofNonzero` provides the bridge once the cycle Gram data is in place. |
| 8 | `ratchet_theorem` specialises to the existing Landauer instance. | **Falsified in the strict reading** — inequality directions are incompatible (see decision note 4 above). The fiber-info ratchet is mathematically clean; the Landauer 2/1 convention is a separate cost model. |
| 9 | `refactoring_bound_kernel` and `gravity_kernel` provable on `TypeKernel`. | **Not tested in code** — `TypeKernel` was not constructed; the discrete-enrichment energy needs a concrete definition. |

### Zero-sorry compliance

```
$ grep -n "sorry\|axiom" Meno/SectorAction.lean Meno/QuadraticAction.lean \
    Meno/LoopKernel.lean Meno/Geodesic.lean Meno/HarmonicForm.lean \
    Meno/SectorPresentation.lean Meno/MatterHomology.lean \
    Meno/InfoRatchet.lean Meno/HomKernel.lean
(no output)
```

Every new file builds without `sorry` or new `axiom`. Deferrals are
honest: theorems are not stated until they can be proved. Where a theorem
is asserted (e.g. variational identity in `HarmonicForm`), it is asserted
as a *field* of an abstract data structure that downstream consumers must
construct with a real proof — no axiomatic shortcuts.

### Build verification

```
$ lake build Meno
…
✔ [3301/3311] Built Meno.Geodesic (955ms)
✔ [3302/3311] Built Meno.InfoRatchet (1.4s)
✔ [3303/3311] Built Meno.SectorAction (4.7s)
✔ [3304/3311] Built Meno.LoopKernel (1.3s)
✔ [3305/3311] Built Meno.QuadraticAction (1.0s)
✔ [3306/3311] Built Meno.HomKernel (1.3s)
✔ [3307/3311] Built Meno.HarmonicForm (1.6s)
✔ [3308/3311] Built Meno.SectorPresentation (1.7s)
✔ [3309/3311] Built Meno.MatterHomology (1.6s)
✔ [3310/3311] Built Meno (2.0s)
Build completed successfully (3311 jobs).
```

All 9 new files plus the updated top-level `Meno.lean` build clean
alongside the unchanged legacy 8-file codebase.

**End of implementation summary.**

---

## Addendum: Phase 11 — Strict Ratchet & Flagship Spine Integration

Closing the two gaps identified in external review of the Phase 1–10 work.

### Strict InfoRatchet (closes Phase 8 tautology)

`Meno/InfoRatchet.lean` (+30 LOC):

- `fiberInfoCost_pos_of_not_injective` — for `f : A → B` non-injective,
  `0 < fiberInfoCost f`. Proof: `Function.not_injective_iff` gives the
  collision pair `a₁ ≠ a₂` with `f a₁ = f a₂`; embed `{a₁, a₂} ⊆ f ⁻¹' {f a₁}`
  to lower-bound `Nat.card` by 2 (via `Set.ncard_pair` +
  `Set.ncard_le_ncard` + `Nat.card_coe_set_eq`); `Real.log 2 > 0`;
  `Finset.sum_pos'` closes.
- `sectionCost_gt_descriptionCost_of_not_injective` — direct corollary via
  the section/description identity. This is the actual **ratchet
  inequality**: non-injective `f` forces strict
  `descriptionCost < sectionCost`.

The file was previously a tautology — it only proved the "easy direction"
(injective ⇒ zero cost). It now proves the load-bearing converse and the
section-cost inequality. The Landauer reconciliation remains skipped (the
existing `SGD.TransitionComplexity` 2/1 convention has opposite inequality
direction, documented in §Architectural Decisions).

### Flagship spine integration (closes "beside vs underneath" gap)

`Meno/CycleHarmonic.lean` (+155 LOC, new file):

The full chain from concrete graph → spine → duality:

```
    cycleGraph_harmonicEnergy_k          (Simplicial.lean, k²/n)
              │
              ▼
    cycleHarmonicGramData n hn           (HarmonicGramData (Fin n), rank 1, Q = !![1/n])
              │
              ▼ toQuadraticAction
    QuadraticAction 1                    (matches QuadraticAction.ofScalar (1/n))
              │
              ▼ partFn_eq_of_Q_eq (new helper in QuadraticAction.lean)
    QuadraticAction.scalarPartFn (1/n)
              │
              ▼ scalarPartFn_one_div_n_eq_partitionFn (this file)
    partitionFn n hn                     (Simplicial.lean)
              │
              ▼ scalarPartFn_duality (QuadraticAction.lean)
    (↑(scalarPartFn (π²·n)) : ℂ)
       = ↑((1/n)/π)^(1/2) · ↑(partitionFn n hn)
```

Theorems landed:

1. `cycleHarmonicGramData n hn : HarmonicGramData (Fin n)` — the rank-1
   Hodge Gram data of the n-cycle. Concrete instance of the abstract
   interface.
2. `cycleHarmonicGramData_energy_eq_harmonicEnergy_k` — the **variational
   identity** at this graph: the Gram-form energy at winding `k` equals
   the harmonic minimum action over the winding-`k` class. Proved by
   `cycleGraph_harmonicEnergy_k`.
3. `cycleHarmonicGramData_toQuadraticAction_Q` — Gram-matrix-level
   identification with `QuadraticAction.ofScalar (1/n)`. Definitional
   (`rfl`).
4. `cycleHarmonicGramData_partFn_eq_scalar` — partition function transit
   through the spine equals scalar partition function at α = 1/n.
5. `scalarPartFn_one_div_n_eq_partitionFn` — definitional matching with
   legacy `partitionFn`.
6. `cycleHarmonicGramData_partFn_eq_partitionFn` — composed: spine-side
   partition function equals legacy `partitionFn n hn`. The new layer is
   not new analytic content; it factors the existing object.
7. **`partitionFn_T_duality_via_spine`** — THE FLAGSHIP. The existing
   cycle-graph T-duality `Z(π²·n) = √((1/n)/π) · Z(n-cycle)` is a
   three-line consequence of `QuadraticAction.scalarPartFn_duality`. The
   categorical groupoid wrapper from `Duality.lean` is no longer
   load-bearing for this correspondence.

### Architectural payoff

Before Phase 11: the spine *could* express the analytic primitive but
had not absorbed any existing flagship theorem. Reviewer verdict was
"vocabulary, not compression."

After Phase 11: at least one flagship — the scalar Jacobi-theta
T-duality on cycle graphs — is now a corollary of the spine. The chain
has no bespoke analytic content; every step is either definitional, a
Q-matrix-level identity, or a direct invocation of
`scalarPartFn_duality`. The abstraction stack passes its first
falsifiability test: the proof of `partitionFn_T_duality_via_spine` is
three `rw` calls.

Helper added to `Meno/QuadraticAction.lean` (+7 LOC):

- `partFn_eq_of_Q_eq` — two quadratic actions with equal Gram matrices
  have equal partition functions. General-purpose, used for the
  scalar-action identification.

### Verification

```
$ lake build Meno
✔ [3308/3312] Built Meno.InfoRatchet (1.5s)
✔ [3309/3312] Built Meno.SectorPresentation (1.7s)
✔ [3310/3312] Built Meno.MatterHomology (1.7s)
✔ [3311/3312] Built Meno (1.5s)
Build completed successfully (3312 jobs).
```

`rg "sorry|axiom " Meno/InfoRatchet.lean Meno/CycleHarmonic.lean Meno/QuadraticAction.lean`
returns zero matches. File totals across the four affected files: 588 LOC
(133 InfoRatchet + 155 CycleHarmonic + 228 QuadraticAction + 72
HarmonicForm).

### What this validates and what remains

**Validated.**

- Falsification criterion #1: scalar duality reduces to
  `scalarPartFn_duality` through the new spine. Confirmed.
- §Architectural Decision 5: "interface-only" status of `HarmonicForm` is
  actually fine — the concrete instance lives in a dedicated bridge file
  and supplies the variational identity downstream. The interface
  factoring works.
- Reviewer verdict reversal: the spine now compresses (not merely names)
  the cycle-graph T-duality content.

**Still open.**

- `Duality.lean` and `Zeta.lean` themselves have *not* been migrated.
  Their internal proofs still go through `quadraticPartFn` /
  `groupoidPartitionFn` rather than `cycleHarmonicGramData`. The flagship
  shows the migration is possible; the migration itself is one more
  session.
- Matrix Siegel–Poisson (rank ≥ 2) still gapped — needs multidim Poisson
  summation in Mathlib.
- `GroupoidObj → LoopKernelObj` bridge still pending.
- Geodesic instantiation from `Simplicial.lean` walks still pending.

The strict ratchet and the cycle-graph flagship were the two
highest-leverage outstanding items. Both are now closed.

**End of Phase 11 addendum.**

---

## Addendum: Phase 12 — Groupoid Migration (2026-06-10, session A)

The reviewer's "collapse the parallel roads" directive, part one: the
groupoid layer now factors through the spine.

### What landed

- `Simplicial.lean`: `Walk.loopWinding_nil`, `Walk.loopWinding_append`
  (winding sector is a monoid morphism on loops; exactness of the
  integer division via `windingCount_dvd_card`).
- `Groupoid.lean` **now imports the spine** (`Meno.SectorPresentation`,
  `Meno.CycleHarmonic`) — the legacy origin file depends on the new
  analytic layer, which is the plan's end-state direction. Added:
  - ground lemmas `cycleCanonicalWinding_id/_comp`,
    `cycleCanonicalEnergy_id/_nonneg`;
  - `GroupoidObj.toLoopKernelObj` (bridge; ground conditions as
    arguments since `GroupoidObj` lacks the fields);
  - `GroupoidObj.toLoopKernelObj_partFn` — proved by **literal `rfl`**,
    satisfying falsification clause #4 exactly;
  - `cycleCanonicalObj` + partFn theorem (relocated upstream from
    `Duality.lean`; references unchanged);
  - `cycleLoopKernel` (the bridge applied to the canonical object);
  - `cycleSectorPresentation : SectorPresentation (cycleLoopKernel n hn) 1`
    — `coord_comp` is winding additivity through the `Quot.lift`
    computation rule; **`Q_symm`/`Q_posDef` are reused from
    `cycleHarmonicGramData`**, so the groupoid and Hodge origins feed
    literally the same Gram object;
  - `cycleLoopKernel_partFn_eq_partitionFn` (groupoid partition function
    through the spine), `cycleSectorPresentation_partFn_eq_gramData`
    (two origins, one analytic object),
    `cycleCanonicalObj_T_duality` (cycle groupoid T-duality as a 2-line
    corollary of the spine flagship — `GroupoidObj.dual` machinery not
    involved).

All defeq-heavy proofs (`coord_one`, `coord_comp`, the `rfl` bridge,
`energy_eq`) went through on first attempt; the only fixes were a
nonexistent lemma name (`Quot.inductionOn₂` is `Quotient`-only) and a
declaration-order slip.

---

## Addendum: Phase 13 — One Analytic Source of Truth (2026-06-10, session B)

Directive: no deferral gestures; everything known becomes session work.
Queue executed: duplicate-proof collapse, Theta absorption, Zeta
re-pointing, diagonal rank-2 Siegel–Poisson, rank-2 matter.

### The collapse

The modular S-transformation proof existed in **three** copies
(`QuadraticAction.lean`, `Duality.lean` privates, `Theta.lean`
specialized at τ = i/(πn)). Now in **one**:

- `Duality.lean`: private modular block (~50 LOC) deleted.
  `quadraticPartFn_eq_scalarPartFn : quadraticPartFn = scalarPartFn`
  is `rfl` (character-identical definitions). `quadraticPartFn_duality`,
  `quadraticPartFn_gt_one`, `quadraticPartFn_duality_real` are now
  one-line forwards to spine theorems. The 20+ internal consumers and
  the entire `GroupoidObj.dual` interpretation layer flow unchanged —
  wrappers stay, analytic authority moves.
- `Theta.lean`: **deleted** (zero consumers — verified by grep before
  removal). Its two public statements survive as spine corollaries in
  `CycleHarmonic.lean`: `partitionFn_eq_jacobiTheta`,
  `partitionFn_T_duality_theta`.
- `Simplicial.lean`: duplicate `summable_quadraticPartFn` (+ private
  helper) deleted; 15 call sites across `Duality`/`Hodge`/`Zeta`
  redirected to `QuadraticAction.summable_scalarPartFn`. `Hodge.lean`
  now imports the spine.
- `QuadraticAction.lean`: theta identification made public API
  (`quadTau`, `scalarPartFn_eq_jacobiTheta`); added
  `scalarPartFn_gt_one`, `scalarPartFn_duality_real`.

### Zeta re-pointed (plan goal #10 fulfilled)

`Zeta.lean` imports **only** `Meno.QuadraticAction` (plus Mathlib),
namespace moved `Simplicial → Meno`, all `quadraticPartFn` names →
`scalarPartFn`. Build evidence of the cut: `lake build Meno.Zeta` is
2934 jobs vs 3262 with the old import — the Riemann functional equation
machinery no longer touches the simplicial/groupoid layers at all. The
Mellin → ζ chain sits directly on the analytic primitive, exactly the
reviewer's target shape.

### Diagonal rank-2 Siegel–Poisson duality (falsification #3, diagonal case)

`QuadraticAction.lean` rank-2 block:

- `ofDiagonal₂ α β : QuadraticAction 2` with `Q = diag(α, β)`;
- `ofDiagonal₂_partFn : Z(diag(α,β)) = Z(α) · Z(β)` (lattice decoupling
  via a Cauchy-product lemma);
- `ofDiagonal₂_det`, `ofDiagonal₂_dual_Q` — the dual coupling matrix
  **is** `π² • Q⁻¹` (exact, via `Matrix.inv_eq_right_inv`);
- `ofDiagonal₂_duality` / `_det_form` —
  `Z(π²·Q⁻¹) = √(det Q / π²) · Z(Q)`, two scalar S-transformations and
  `Complex.mul_cpow_ofReal_nonneg`. **No multidimensional Poisson
  summation needed.** The general non-diagonal case remains gated on
  Mathlib.

### Rank-2 matter (the "not secretly rank-1" test)

`CycleHarmonic.lean`: `wedgeHarmonicGramData n₁ n₂ : HarmonicGramData
(Fin n₁ ⊕ Fin n₂)` — rank 2, Gram `diag(1/n₁, 1/n₂)`, all proof fields
inherited from `ofDiagonal₂` by defeq. `wedgeMatter₁` (explicit `(1,0)`
sector), `wedge_exists_matter`, and the energy computation
`energy (1,0) = 1/n₁`. Honest scope note **in the docstring**: the
wedge *complex* does not exist in `Simplicial.lean`, so the graph-level
variational derivation of this Gram form is not formalized — the Gram
data is asserted as the wedge's on the (true, unformalized) ground that
wedge harmonics have disjoint edge supports.

### Engineering lessons (cost: ~5 build cycles)

1. **HO-unification blow-ups in tsum transport.** `piFinTwoEquiv`'s
   coercion and `tsum_prod'`-against-β-redexes both exceeded 1.6M
   heartbeats. Diagnosis by a 4-theorem `sorry` test battery in one
   build. Fix: hand-rolled `finTwoPair` equiv (one-β `toFun`) +
   `tsum_mul_tsum_of_summable_norm` with named `f`, `g` — every
   unification first-order. Raising heartbeats was useless (loop, not
   slowness); bisection was the move.
2. **Pin structure projections near heavy proof terms.**
   `ofDiagonal₂_Q … = !![α,0;0,β] := rfl` + `simp_rw` keeps later
   goals from delta-unfolding a structure whose `PosDef` field carries
   `nlinarith` certificates.
3. **`field_simp` strands `ring`** — three more occurrences this
   session ("No goals to be solved"). Reflex: drop the `ring` first.

### Findings for the deferral ledger (decisions are the user's, not encoded gaps)

1. **Rank-r diagonal duality is unblocked.** `Hodge.lean` already has
   the rank-r diagonal *factorization* machinery
   (`tsum_finPi_factor`, `summable_graphPartitionFn_diagonal`,
   Hodge.lean ~322–347). Combining it with per-coordinate
   `scalarPartFn_duality` and an induction on the cpow product
   prefactor gives `Z(π²·Q⁻¹) = √(det Q / π^r) · Z(Q)` for any diagonal
   `Q` — est. ~80 LOC, nothing gated on Mathlib. The rank-2 version
   landed this session is the base case.
2. **Hodge.lean's diagonal constructors could unify with a generalized
   `ofDiagonal (α : Fin r → ℝ)`.** Hodge now imports the spine, so the
   direction is open.
3. **`GroupoidObj.dual` retained deliberately** as interpretation layer
   (reviewer's verdict); its analytic content is fully forwarded. A
   future strip would change the statement inventory, which is a taste
   call.
4. **The wedge complex** (graph-level Hodge for `C_{n₁} ∨ C_{n₂}`) is
   the missing piece between `wedgeHarmonicGramData` and a *derived*
   rank-2 variational identity. Large (cycle-graph machinery was
   ~2500 LOC); the abstract layer no longer waits on it.

### Verification

- `lake build Meno`: 3311 jobs, success (note: −1 module net — Theta
  deleted, nothing added at top level).
- `lake build Meno.Zeta` alone: 2934 jobs (spine-only cone).
- Zero `sorry` (diagnostic test battery removed before final build);
  zero axiom declarations.

**End of Phase 12/13 addendum.**
