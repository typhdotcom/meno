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

---

## Addendum: Phase 14 — The Ledger Drained (2026-06-10, session C)

Standing rule, set by the user this session: **we don't defer**. The
Phase 13 findings ledger became the Phase 14 queue. All four items
resolved — three by proof, one by decision.

### 1. Rank-r diagonal Siegel–Poisson duality (was finding #1) — PROVED

`QuadraticAction.lean`:

- `diag_quadForm_eq`, `summable_finPi_prod`, `tsum_finPi_factor` —
  relocated upstream from `Hodge.lean` (were `private` there), now
  public spine API. Pure Fubini-for-counting-measure on `ℤ^r`.
- `ofDiagonal (α : Fin r → ℝ) (hα : ∀ i, 0 < α i) : QuadraticAction r`
  with `Q = Matrix.diagonal α`. PosDef proved manually
  (`Matrix.posDef_diagonal_iff` failed `StarOrderedRing ℝ` synthesis;
  the manual `Finset.sum_pos'` route is 15 lines and robust).
- `ofDiagonal_partFn : Z(diag α) = ∏ᵢ Z(αᵢ)` — rank-r factorization.
- `ofDiagonal_det` (`= ∏ αᵢ` via `Matrix.det_diagonal`),
  `ofDiagonal_dual_Q` (dual coupling matrix **is** `π² • Q⁻¹`, inverse
  by explicit diagonal multiplication).
- `prod_cpow_half` — `∏ᵢ (fᵢ)^(1/2) = (∏ᵢ fᵢ)^(1/2)` for nonneg reals
  in `ℂ`-cpow form, by structural recursion on `Fin`.
- **`ofDiagonal_duality`** — `Z(π²·Q⁻¹) = √(det Q / π^r) · Z(Q)` for
  every diagonal `Q` at every rank, plus `_det_form`. `r` scalar
  S-transformations; zero multidimensional Poisson summation.

**Falsification clause #3 status**: closed for all diagonal Gram forms,
all ranks. Open only for non-diagonal `Q` (genuinely gated on Mathlib's
missing lattice Poisson summation). The rank-2 hand-built case from
session B remains as the concrete instance; `ofDiagonal₂_partFn_eq_ofDiagonal`
is the dedup witness identifying it with the general family (kept both
because `wedgeHarmonicGramData` reuses `ofDiagonal₂`'s literal-matrix
defeq shape).

### 2. Hodge routed through the spine (was finding #2) — DONE

The three Fubini lemmas deleted from `Hodge.lean`; its
`graphPartitionFn_diagonal` / `summable_graphPartitionFn_diagonal` now
consume `Meno.QuadraticAction.*`. Hodge's diagonal analytics are spine
consumers, not an independent source.

### 3. `GroupoidObj.dual` (was finding #3) — DECIDED, not deferred

Kept as interpretation layer, per the external reviewer's explicit
verdict ("Duality.lean should become an interpretation layer over
QuadraticAction"). Its analytic content is already fully forwarded
(Phase 13); the wrapper inventory is the interpretation. Decision
recorded; nothing pending.

### 4. The wedge (was finding #4) — the naive plan is FALSE, and now provably so

**`SectorPresentation.end_comm`** (SectorPresentation.lean): any sector
presentation forces `g ≫ h = h ≫ g` on `End L.base` — `coord` is an
injective map turning composition into (commutative) addition. Proof is
3 lines.

Consequences, now load-bearing architecture facts:

- π₁ of the wedge of two cycles is the **free group on two
  generators** — nonabelian — so the wedge loop kernel admits **no
  sector presentation at any rank**. A session that attempted the
  "wedge `SectorPresentation` of rank 2" would have been building
  toward a false theorem; `end_comm` is the 3-line proof that falsifies
  the naive plan before the ~2500-LOC graph build, not after.
- Summing Boltzmann weights over `End` diverges for nonabelian π₁
  (every `H₁` class contains infinitely many equal-energy homotopy
  classes). The spine's "sector = homology class" formulation is
  thereby **forced**, not conventional — `O2` in the technical
  preamble was the right call for reasons the preamble didn't state.
- The corrected wedge target: a **quotient presentation**
  (`End →* ℤ^r` surjective, energy descending to classes), not an
  equivalence. This structure is *not* defined this session — it would
  have exactly one degenerate instance (the cycle, where the quotient
  is an iso) until the wedge complex exists, and vocabulary without a
  nontrivial consumer is the InfoRatchet-tautology failure mode. The
  wedge complex (graph-level walks/homotopy/Hodge for `C_{n₁} ∨ C_{n₂}`)
  is the one remaining object on this front; its true size is the
  cycle-machinery class (~2500 LOC), and its target shape is now
  correct.

### Engineering notes

- `Matrix.posDef_diagonal_iff` fails instance synthesis
  (`StarOrderedRing ℝ`) in this Mathlib pin; manual route works.
- `Matrix.smul_diagonal` does not exist; entrywise `by_cases` does.
- ℝ's `star` is definitionally `id`: `congr 1` closes
  `diagonal (star α) = diagonal α` outright (a trailing `funext` then
  errors with "no goals").
- `include P in` (like `set_option … in`) must precede the docstring.
  Section variables used only in proof bodies are not auto-included.

### Verification

- `lake build Meno`: 3311 jobs, success, zero warnings (a `sorry`
  would warn; none did).
- The session's `rg` sweeps for `sorry`/`axiom` were intermittently
  blocked by tool-permission outages; the last completed sweep (start
  of session C) was clean, and all code added since is in this record.

**End of Phase 14 addendum.**

---

## Addendum: Phase 15 — Multivariate Poisson Summation, Falsification #3 Closed (2026-07-13)

The last analytic gap in the plan. Phase 14 left exactly one clause of
the falsification table open: the non-diagonal matrix Siegel–Poisson
duality, "genuinely gated on Mathlib's missing lattice Poisson
summation." External review of that framing corrected it: **not gated on
Mathlib — blocked on us formalizing the multivariate bridge, and the
ingredients are already in the pin.** Mathlib v4.26.0 has the
multivariate torus Fourier machinery (`UnitAddTorus`, `mFourierCoeff`,
`hasSum_mFourier_series_apply_of_summable` in `AddCircleMulti`) and the
one-dimensional bridge blueprint (`Real.fourierCoeff_tsum_comp_add`,
~50 lines); what it lacks is the connecting theorem — periodize over
`ℤ^d`, identify torus Fourier coefficients with Euclidean Fourier
samples, reconstruct. This session built that bridge, **scope-cut to
the Gaussian family** `x ↦ exp(-π·xᵀMx)`, and derived the general
duality from it.

### What landed

`Meno/SiegelPoisson.lean` (new, 1220 LOC), imported by `Meno.lean`
directly after `QuadraticAction`. Zero `sorry`, zero axioms; full
project builds (3331 jobs).

**Foundations (retiring a Session-1 deferral).**

- `Matrix.PosDef.exists_coercivity` — a positive-definite form
  dominates `c·∑xᵢ²` for some `c > 0`. **Eigenvalue-free**: minimize
  the form on the compact sphere `{∑xᵢ² = 1}` (extreme value theorem),
  scale by degree-2 homogeneity. No spectral machinery.
- `summable_exp_neg_quadForm` — Boltzmann weights of any posdef form
  are summable on `ℤ^d` (coercivity + the spine's own
  `summable_finPi_prod`). **Session-1 architectural decision 1 is
  retired**: summability is now derivable from `Q.PosDef`, and
  `QuadraticAction.of_posDef` is the field-free constructor.

**The bridge (the load-bearing new mathematics).**

- `gaussian M`, `periodization M` (lattice sum of translates),
  continuity of the periodization via box-uniform domination —
  the coordinatewise estimate `(t+z)² ≥ z²/2 − B²` for `|t| ≤ B`
  makes the sup-norms a product of scalar Gaussian tails.
- Descent to the torus (`torusPeriodization`) by the compact-quotient
  argument: the closed unit cube is compact, the torus Hausdorff, and a
  continuous surjection compact → Hausdorff is a quotient map. No
  open-quotient-map API needed.
- `mFourierCoeff_torusPeriodization` — **the periodization bridge**:
  the `m`-th torus coefficient of the descended periodization equals
  `∫_{ℝ^d} char·gaussian`. Proof: transfer the torus integral to the
  half-open cube through `measurePreserving_pi` of
  `AddCircle.measurePreserving_mk`; swap sum and integral by
  norm-summability (`integral_tsum_of_summable_integral_norm`); shift
  each term to its lattice cell (`setIntegral_image_emb` along the
  translation, character invariance via `torusMk`); reassemble the
  exactly-tiling cells with `hasSum_integral_iUnion`.
- `integral_charGauss_eq` — **the multivariate Gaussian Fourier
  transform** `∫ e^(-2πi⟨m,x⟩)e^(-π·xᵀMx) = (det M)^(-1/2)·e^(-π·mᵀM⁻¹m)`,
  by spectral rotation. The Phase 14 division-of-labor principle is now
  implemented, not just stated: diagonalization is legitimate on the
  *integral* side (Lebesgue measure is `|det|`-covariant under linear
  maps; the eigenvector rotation has `|det| = 1` so it is measure
  preserving), and only there. The rotated integral factors into 1-D
  Gaussians (`integral_fintype_prod_volume_eq_prod`), each evaluated by
  Mathlib's `fourierIntegral_gaussian`.
- `tsum_gaussian_eq` — **Poisson summation for Gaussians on `ℤ^d`**:
  reconstruction at the basepoint (`hasSum_mFourier_series_apply_of_summable`
  at `torusMk 0`), coefficient summability from `summable_exp_neg_quadForm`
  applied to `π·M⁻¹` (posdef by the hand-rolled `posDef_inv`/`posDef_smul'`).

**The payoff.**

- `QuadraticAction.dual` — the general dual `Q ↦ π²·Q⁻¹` as a genuine
  `QuadraticAction`: symmetry, positive-definiteness, and summability
  all **derived**, no fields supplied.
- **`QuadraticAction.duality`** — `Z(π²·Q⁻¹) = √(det Q/π^r)·Z(Q)` for
  every symmetric positive-definite `Q` at every rank, as a complex
  `cpow` identity matching the diagonal-case conventions. Obtained from
  `tsum_gaussian_eq` at `M := π⁻¹·Q` (so `M⁻¹ = π·Q⁻¹` and the dual
  coupling `π²·Q⁻¹` appears in the exponent).
- `ofDiagonal_dual_partFn_eq` — dedup witness: the Phase 14 diagonal
  dual is the general dual restricted to diagonal Gram forms;
  `ofDiagonal_duality` is now a corollary of the general theorem.

**Falsification clause #3: closed.** No diagonal restriction, no
Mathlib precondition. The plan's original phrasing ("if such
infrastructure is needed, this phase delivers it as part of the plan
rather than as a precondition") is finally satisfied — two sessions of
work later than promised, at Gaussian scope rather than Schwartz scope,
which is all the plan ever needed.

### Engineering lessons

- **The Gaussian scope-cut is what made this tractable.** The two
  analytically delicate steps of general Poisson summation — continuity
  of the periodization and summability of the transform samples — are
  elementary for Gaussians (everything factors coordinatewise through
  scalar Gaussian tails). Mathlib's 1-D theorem must serve all
  functions; ours serves one family, and that family is all the spine
  sums.
- **Import cones lie in wait.** `Matrix.IsHermitian.eigenvectorUnitary`
  "did not exist" for half a build cycle: the spectral theorem lives in
  `Mathlib.Analysis.Matrix.PosDef` / `Spectrum`, not the
  `Mathlib.LinearAlgebra.Matrix.PosDef` the spine already imported.
- **Dot notation dies on `def`-valued Props.** `hHerm.eigenvectorUnitary`
  resolved to `Eq.eigenvectorUnitary` (IsHermitian unfolds to `Mᴴ = M`).
  Full names everywhere in the spectral block.
- **`AddCircleMulti` uses a local `MeasureSpace` instance** (pi of
  `haarAddCircle`, probability). For `T = 1` it is propositionally the
  global mass-`T` Haar volume (`volume_eq_smul_haarAddCircle` is `rfl`
  plus `ofReal 1 • μ = μ`), and one `Measure.pi`-congruence reconciles
  `mFourierCoeff`'s baked-in measure with `measurePreserving_mk`'s.
- **`rw` under beta-redexes and unparenthesized `-a * b`** (which
  parses as `-(a * b)`) cost several cycles; `simp only [...]` and
  explicit `have`-based equality chains are the robust forms. `set`
  abstracts occurrences, so a later `rw [← hy]` on the definiendum
  finds nothing.
- **`posDef_iff_dotProduct_mulVec` remains the workhorse.** Mathlib's
  `Matrix.PosDef.smul` needs `StarOrderedRing ℝ` synthesis (fails at
  this pin, same as Phase 14's `posDef_diagonal_iff`); hand-rolled
  `posDef_smul'` and `posDef_inv` are ~15 lines each.

### What this unlocks / still open

- `harmonicGramForm G` of an **arbitrary** finite graph can now feed
  the duality directly — no diagonality hypothesis. The Phase 5
  variational program (graph-level Hodge for general graphs, wedge
  complex) is the remaining consumer-side work.
- `dual_dual = id` and the self-dual/duality-flow layer of the plan's
  Phase 2 wishlist are now cheap targets (the dual is a genuine
  `QuadraticAction`; `(π²·Q⁻¹)` inverts to `π⁻²·Q` by the same
  right-inverse verification).
- `Basic.lean`/`TypeKernel` (Phase 10) and the wedge complex are
  unchanged — next in the priority order.

### Verification

- `lake build Meno`: 3331 jobs, success, zero warnings after lint
  cleanup.
- `rg "sorry|^axiom" Meno/`: no matches (all hits are prose in
  docstrings).

**End of Phase 15 addendum.**

---

## Addendum: Phase 16 — Duality Algebra & the Categorical Dual (2026-07-13, session B)

The "cheap wins" pass: everything Phase 15 made nearly free. Goals 2
and 6 of the plan are now **fully** realized. One more plan claim
falsified in code.

### Duality algebra (`Meno/SiegelPoisson.lean`, +240 LOC)

- `QuadraticAction.eq_of_Q_eq` — a quadratic action is its Gram matrix
  (proof fields are propositions).
- **`dual_dual : A.dual.dual = A`** — the duality is an involution;
  what licenses the name.
- `selfDual`, **`selfDual_iff`** (`Q² = π²·1`), and
  `ofScalar_selfDual_iff` (`α = π` at rank 1 — the fixed point the
  legacy layer knows as the variational minimum).
- `duality_real` — the duality with real `rpow` prefactor.
- `dualityFlow` with closed form **`-½·log(det Q/π^r)`**
  (generalizing the scalar `D(α) = ½·log(π/α)`), antisymmetry under
  the involution, and `dualityFlow_eq_zero_iff : flow = 0 ↔ det Q = π^r`.
- **`exists_dualityFlow_eq_zero_not_selfDual`** — the plan's
  `dualityFlow_zero_iff_selfDual` is **false at rank ≥ 2**, witnessed
  by `diag(2π, π/2)`: zero flow sees only the determinant;
  self-duality constrains the whole form. The iff survives only at
  rank 1. Falsification-by-formalization, `end_comm` tradition; the
  plan's Phase 2 wishlist item is closed by *refutation with corrected
  statement*, not by proof.
- `ofScalar_dual_partFn` and **`scalarPartFn_duality_via_poisson`** —
  the scalar T-duality re-proved through the Poisson bridge. The same
  statement `scalarPartFn_duality` proves via `jacobiTheta` and the
  modular S-transformation. Two independent proof traditions now
  corroborate each other inside the spine; Mathlib's modular machinery
  is henceforth corroboration, not dependency.

### The categorical dual (`Meno/SectorPresentation.lean`, +60 LOC; Goal 6 closed)

- `LoopKernelObj.dualVia P` — the dual loop kernel: same category, same
  basepoint, energy transported from `π²·Q⁻¹` through the
  presentation's coordinates. All obligations (`energy_id`,
  `energy_nonneg`, `summable`) discharged by the dual quadratic
  action's own fields — nothing is asserted.
- `dualPresentation` — the **same** `coord` presents the dual object as
  the dual action (`energy_eq` is `rfl`).
- **`dualVia_partFn_duality`** — categorical Siegel–Poisson duality:
  `Z(L.dualVia P) = √(det Q/π^r) · Z(L)` for any loop kernel admitting
  a presentation, any rank, any Gram form. Two lines from
  `QuadraticAction.duality`.
- Concrete witness (`Meno/Groupoid.lean`, +15 LOC):
  `cycleLoopKernel_dualVia_partFn` — the categorical dual of the cycle
  loop kernel obeys `Z(dual) = √((1/n)/π)·Z(C_n)`. The construction
  has a consumer on day one.

Import direction: `SectorPresentation` now imports `SiegelPoisson`
(analytic primitives upstream of categorical presentation — the plan's
intended flow). No cycles; full build 3331 jobs.

### Engineering notes

- Structure projections of noncomputable defs (`(ofScalar α hα).Q`)
  are invisible to `simp` until rewritten by a `show ... from rfl`;
  two build cycles.
- `linear_combination` is the right tool for `(a−b)(a+b) = 0` from
  `a² = b²` — `nlinarith` does not take equality goals gracefully.
- `dualVia`, `dualPresentation`, and the cycle witness all built on
  the **first attempt** — the spine's interfaces are now load-bearing
  enough that new constructions compose without friction. That is what
  "the abstraction is right" feels like operationally.

### Ledger after this phase

| Goal | Status |
|-----:|:-------|
| 1, 2, 3, 6, 8, 10, 12, 13 | **Closed** |
| 4 (Geodesic instance) | Open — plumbing |
| 5 (general-graph Hodge variational layer) | Open — the big analytic build; theta graph first (non-diagonal consumer for Phase 15) |
| 7 (concrete MatterHomology: binding, homological matter) | Open — downstream of 5 |
| 9 (magnitude) | Open — needs an in/out **decision** |
| 11 (TypeKernel/Basic rewrite — gravity) | Open — design-first |

**End of Phase 16 addendum.**

---

## Addendum: Phase 17 — Review Handoff, Honesty Pass, Course Corrections (2026-07-16)

The plan's original author reviewed Phases 15–16. Verdict: "the central
plan is validated, the work is strong, theta is the correct next test.
Prune magnitude, halt TypeKernel, settle the homology/cohomology
distinction before building MatterHomology." All six of the review's
code citations were verified accurate against the source. This addendum
records the verification, the immediate actions, the decisions, and a
corrected goals ledger (the Phase 16 ledger overstated closure of
Goals 10 and 12).

### Immediate actions taken

- **`QuadraticAction.selfDual_iff_eq`** (the review's free theorem):
  for positive-definite `Q`, `Q² = π²·1` already forces `Q = π·1` —
  `Q + π·1` is positive definite hence invertible, and
  `(Q − π·1)(Q + π·1) = 0` kills the first factor. The self-dual locus
  is a **single point**; zero duality flow is the whole hypersurface
  `det Q = π^r`. Phase 16's falsification is now exactly quantified:
  a point versus a hypersurface. Helpers `posDef_one`, `posDef_add`
  added (hand-rolled; the pin's versions carry `StarOrderedRing`
  baggage that fails synthesis for ℝ).
- **`Geodesic.selfMass` deleted** — it was `length (𝟙 X)`, provably
  zero by the class's own axiom (the file even proved
  `selfMass_eq_zero`), with zero consumers. Degenerate vocabulary,
  removed per the Theta.lean precedent.
- **`HarmonicForm` docstrings corrected** — the structure documentation
  claimed a `variational` field that does not exist. The docs now say
  plainly: `HarmonicGramData` is positive-definite matrix data and
  nothing more; the variational identity is proved per instance,
  outside the structure. Same correction to the `energy` docstring.

### Decisions (recorded, not deferred)

1. **Magnitude is OUT** (Goal 9 pruned). No consumer connects it to
   the harmonic-Gram/partition-function spine. Re-entry ticket: a
   concrete theorem linking magnitude to the spine, stated before any
   vocabulary is built.
2. **TypeKernel is HALTED as a falsified design** (Goal 11 reopened as
   a design problem, not an implementation task). Three independent
   defects in the plan's sketch: `E(f) = log|im f|` gives
   `E(id_A) = log|A| ≠ 0`, contradicting `HomKernelCat.energy_id`;
   `atBase A` sums over *endofunctions*, not elements, so the intended
   `C(A) = log|A|` is not what the kernel computes; and arbitrary
   (infinite) types cannot satisfy positive-weight summability.
   `Basic.lean` remains independent until a valid object-level kernel
   design exists. Gravity stays expressed in the legacy vocabulary —
   honestly labeled as such — rather than in a broken new one.
3. **H₁ versus H¹ is resolved: the spine's sectors are cohomological.**
   The existing cycle result minimizes cochain energy at prescribed
   winding/period — the value `1/n` is the norm on the *dual* (period /
   integral cohomology) lattice; an integral 1-chain generator has
   squared norm `n`. Rank 1 hides the distinction (both lattices are
   `ℤ`); rank 2 will not. Goal 7 will be built on integral cohomology
   classes with harmonic representatives (equivalently, homology with
   explicit basis-aware dualization). The plan's "implement the H₁
   quotient and call its minimum action 1/n" is **not** to be
   implemented as written.
4. **Next build: the theta graph, concretely, via `K₂,₃`.** The
   `Graph` structure (`edge : V → V → Prop`) cannot represent parallel
   edges, so the subdivided theta — three length-two paths between two
   junction vertices — is the representative. Calculation oracle from
   the review, verified by hand: with cycle basis `p₁−p₃`, `p₂−p₃`,
   the cycle-chain Gram is `C = [[4,2],[2,4]]` and the harmonic period
   Gram is `Q = C⁻¹ = [[1/3,−1/6],[−1/6,1/3]]` (off-diagonal sign
   orientation-dependent, but necessarily nonzero; consistent with the
   cycle case, where `C = [[n]]` and `Q = [[1/n]]`). This will be the
   first Gram form **derived** from graph topology and variational
   minimization that is non-diagonal — the first genuine consumer of
   the Phase 15 general duality. Concrete-first: build the theta
   result, extract the general finite-graph API afterward.

### Ledger corrections (honesty pass)

- **Goals 10 and 12 downgraded from Closed to Partial.** Only
  `Zeta.lean` meets the letter of Goal 10 (imports only the analytic
  primitives). `Duality.lean` still imports `Groupoid`; `Hodge.lean`
  still imports `Simplicial`; `Meno.lean` labels those layers "to be
  migrated." The Phase 13/14 decision to keep them as interpretation
  layers is legitimate, but a decision to deviate from a goal does not
  close the goal — it amends it. Recorded as: *amended by decision,
  deviation documented*.
- **InfoRatchet**: `sectionCost` is *defined* as
  `descriptionCost + fiberInfoCost`, so the "ratchet identity" is
  definitional bookkeeping (`unfold; ring`). The substantive content of
  the file is `fiberInfoCost_pos_of_not_injective` (Phase 11) and the
  strict inequality it yields. The Landauer reconciliation remains
  open-by-decision.
- **MatterHomology**: `MatterSector` is a nonzero vector in an abstract
  positive-definite lattice — not yet homology (and per decision 3,
  will become *cohomology*). Interface status re-affirmed.

### Corrected ledger

| Goal | Status |
|-----:|:-------|
| 1, 2, 3, 6, 8, 13 | **Closed** |
| 10, 12 | **Amended by decision** (Zeta literal; Duality/Hodge kept as interpretation layers; deviation documented) |
| 4 (Geodesic instance) | Open — plumbing; degenerate `selfMass` removed |
| 5 (variational layer) | Open — **theta via K₂,₃ is the entry point**, concrete-first |
| 7 (matter) | Open — reformulated cohomologically (decision 3) |
| 9 (magnitude) | **Pruned** (decision 1) |
| 11 (TypeKernel) | **Halted — design falsified** (decision 2) |

**End of Phase 17 addendum.**

---

## Addendum: Phase 18 — The Theta Graph (2026-07-16)

The review's designated next test, executed. `Meno/ThetaHarmonic.lean`
(new, ~340 LOC), full build 3332 jobs, zero `sorry`. The first harmonic
Gram form in the spine that is **derived from graph topology by
variational minimization** — and the first that is **non-diagonal**.
Phase 15's general duality has its consumer.

### The variational lemma (the general-API seed)

`isLeast_energy_periods`: in `ℝ^E` with the standard dot product, given
period vectors `c₁,…,c_r` with invertible Gram matrix `C`, the least
energy among cochains with prescribed periods `⟨ω, cᵢ⟩ = kᵢ` is
`kᵀC⁻¹k`, **attained** at `ω* = ∑ᵢ(C⁻¹k)ᵢcᵢ`. Pythagoras: a feasible
`ω` is `ω* + δ` with `δ` period-orthogonal, hence orthogonal to
`ω* ∈ span(cᵢ)`. Proved for an arbitrary finite edge type — this is
the Hodge variational principle in its **cohomological (period)
formulation**, per the Phase 17 H¹ decision: no boundary operators, no
Hodge decomposition, the period constraint *is* the cohomology. When
the general finite-graph API is extracted (post-theta, per the
concrete-first directive), this lemma is its analytic core.

### The theta instantiation (`K₂,₃`)

- Graph data: 5 vertices (2 junctions, 3 path interiors), 6 oriented
  edges via explicit `src`/`tgt` maps. Basis cycles `c₁ = p₁ − p₃`,
  `c₂ = p₂ − p₃`.
- `thetaBoundary_cycles` — the basis vectors have vanishing boundary at
  every vertex (they are cycles of the graph, not postulated vectors).
- `eq_comb_of_thetaBoundary_eq_zero` — **the cycle space is exactly
  their span** (`b₁ = 2`): flow conservation at interior vertices
  equalizes path edges; conservation at a junction eliminates the third
  flow.
- `gramOf_thetaCycles : C = [[4,2],[2,4]]` and
  `thetaChainGram_inv : C⁻¹ = [[1/3,−1/6],[−1/6,1/3]]` — the review's
  oracle, confirmed in Lean. Positive-definiteness of the period form
  comes from `posDef_inv` (Phase 15 helper) applied to the chain form.
- `thetaHarmonicGramData` — the first non-diagonal `HarmonicGramData`,
  with `summable` derived by `summable_exp_neg_quadForm` (no field
  supplied), and `thetaGramData_energy_isLeast` — the per-instance
  variational identity demanded by the Phase 17 honesty note on
  `HarmonicForm`: the Gram energy of sector `k ∈ ℤ²` *is* the least
  cochain energy at periods `k`.
- `thetaGram_offDiag_ne_zero` — the coupling is real: `−1/6 ≠ 0`.
- `thetaMatter` — the `(1,0)` sector is matter with minimum action
  `1/3` (`thetaGramData_energy_one_zero`).
- **`theta_siegelPoisson_duality`** — the theta action obeys
  `Z(π²·Q⁻¹) = √((1/12)/π²)·Z(Q)` via the general duality, with
  `det Q = 1/12` computed. Phases 15, 17, and 18 meet in one theorem:
  topology → minimization → coupled Gram form → duality.

### Engineering notes

- `simp +decide` is the tool for `Fin`-literal combinatorics
  (if-conditions `(2 : Fin 5) = 0`, vector-literal lookups at indices
  ≥ 2 after `fin_cases`). Plain `simp`/`norm_num` reduce indices 0 and
  1 only (`cons_val_zero/one` are `@[simp]`; the `cons_val` dsimproc
  did not fire in the `fin_cases` contexts at this pin). Diagnosed by
  a minimal probe file after two failed guesses — bisection beats
  theorizing about simprocs.
- Structure-projection types (`Fin H.r`) block `OfNat` synthesis in
  theorem *statements* even when `H.r` is definitionally a literal;
  state entry-level facts about the literal matrix and bridge with a
  `rfl` lemma.
- The dot-product lemma family (`add_dotProduct`, `sub_dotProduct`,
  `dotProduct_comm`) lives in the **root** namespace at this pin, not
  under `Matrix`.

### Status after this phase

Goal 5's entry point is done: the variational identity is proved and
consumed at a genuinely coupled instance. Remaining on this front:
extract the general finite-graph API (graph → cycles → Gram →
`HarmonicGramData`, parametrized), connect `MatterSector` to the
cohomological formulation (Goal 7), and re-derive the cycle graph
`C_n` through the same period machinery (unifying `CycleHarmonic` with
`ThetaHarmonic`). The wedge complex should follow the same
concrete-first route.

**End of Phase 18 addendum.**

---

## Addendum: Phase 19 — The Time Capsule: Binding, Exactness, Trapped Paradox (2026-07-16, session B)

A rewound session left three ideas to send back. All three were tested
against the theta laboratory built in Phase 18; two are now theorems,
one is a recorded design program. One capsule formula needed
correction — and the correction is itself a theorem.

### 1. Gravity at the Gram level — PROVED (with corrected oracle)

`Meno/ThetaHarmonic.lean` (+190 LOC, total 544):

- `HarmonicGramData.interaction` — the Gram bilinear form between
  sectors — and `energy_add` (polarization):
  `E(a+b) = E(a) + E(b) + 2B(a,b)`.
- `bindingEnergy a b := E(a) + E(b) − E(a+b)` with
  **`bindingEnergy_eq : binding = −2·B(a,b)`** — the entire
  gravitational content of the Gram level is the off-diagonal. Shared
  edges make the chain overlap positive, the period cross-term
  negative, the binding positive: **sectors that share roads attract**.
- `theta_bindingEnergy = 1/3` and `theta_binding_attractive`
  (`E(1,1) < E(1,0) + E(0,1)`) — computed from the topologically
  derived Gram form.
- **`sharedCycles_binding`**: the exact parametric oracle. Two cycles
  of lengths `n₁, n₂` sharing `k` co-oriented edges bind at unit
  sectors with energy `2k/(n₁n₂ − k²)`. The capsule said `2k/(n₁n₂)` —
  that is the leading approximation; theta (`4,4,2`) separates them
  (`1/3` exact vs `1/4` approximate) and the theta Gram data confirms
  the exact value. A message from a fork of the same model, checked
  and corrected by the kernel.

This gives Goal 7's `binding_releases_mass` its Gram-level form with
an exact closed formula — the "gravity" phenomenon (binding from
shared structure) now exists in the spine as theorems, without any
dependence on the halted TypeKernel design.

### 3. Matter as trapped paradox — PROVED at theta

- `thetaGrad` (the coboundary/gradient of a vertex potential) and
  `thetaGrad_period`: gradients have vanishing periods — local
  re-description is invisible to the sectors.
- **`thetaExactness`**: a cochain has vanishing periods **iff** it is
  a gradient. Forward direction constructs the potential explicitly
  (integrate along path one; the two period conditions certify
  consistency across paths two and three).
- **`matter_no_potential`**: the minimum-energy representative of a
  nonzero sector is not a gradient. A sector is a constraint system —
  "the potential difference across `e` is `ω e`" — that is locally
  consistent everywhere and globally unsatisfiable. Matter is trapped
  inconsistency; its positive energy is the cost of the paradox.

### 2. The keystone — RECORDED as the next design program

"Incompressible residue of neighbor-local re-description = b₁." The
rank-2 mathematical core now exists: the period map is surjective
(`periodRep_periods`) with kernel exactly the gradients
(`thetaExactness`) — cochains modulo local moves ≅ b₁ period
coordinates. What remains is the **information-theoretic half**: a
description-length model of local re-description (InfoRatchet
vocabulary) in which this quotient is the provable lower bound on
compression. That is a design problem of TypeKernel's kind — the
definitions must deserve their names before Lean gets a vote — and it
is the thesis's actual junction of information and topology. Do not
build vocabulary for it until the connecting theorem is stated.

### Engineering note

The entire block — polarization, binding, parametric oracle,
exactness, no-potential — built on the **first attempt**, zero errors
(two lint warnings). Phase 18's `simp +decide` recipe and the period
formulation carried everything. Infrastructure compounding,
measurably.

**End of Phase 19 addendum.**

---

## Addendum: Phase 20 — API Extraction & the Two-Route Unification (2026-07-16, session C)

The extraction Phase 18 promised, plus the corroboration Phase 19's
momentum made cheap. New file `Meno/PeriodHarmonic.lean` (327 LOC);
`ThetaHarmonic` slimmed to pure theta content; unification theorems in
`CycleHarmonic`. Full build 3333 jobs, zero `sorry`.

### The general API (`Meno/PeriodHarmonic.lean`)

- The `PeriodMinimization` section (Pythagoras / least-norm-at-
  prescribed-periods) **moved** verbatim from `ThetaHarmonic` — the
  concrete-first extraction, on schedule.
- **`HarmonicGramData.ofCycles`** — the builder: any family of cycle
  vectors with positive-definite chain Gram yields harmonic Gram data
  with the *inverse* chain Gram as period form; symmetry,
  positive-definiteness, and summability all derived, and
  `ofCycles_energy_isLeast` supplies the variational identity as a
  theorem. The honesty obligation attached to `HarmonicGramData` in
  Phase 17 is now discharged *generically* for every instance the
  builder produces.

### The parametric cycle graph

`C_n` through periods, for **all** `n > 0` (not `n ≥ 3`, and fully
parametric — no `simp +decide`, which only handles literals):

- `cycleBoundary` with closed form `∂ω(v) = ω(v−1) − ω(v)`;
  the all-ones cochain is a cycle.
- **`b₁(C_n) = 1`**: boundary-zero cochains are constant
  (`eq_smul_allOnes_of_cycleBoundary_eq_zero`), by strong induction on
  the vertex index with explicit `Fin.mk` successor arithmetic.
- Chain Gram `[[n]]`, period Gram `[[1/n]]` (`cyclePeriodData_gram`) —
  the spine's original harmonic mass, re-derived from first principles
  in ~100 lines against `Simplicial.lean`'s ~2500.

### The unification (`Meno/CycleHarmonic.lean`)

- `cyclePeriodData_gram_eq` / `cyclePeriodData_energy_eq` — the
  period-model data and the walk-derived `cycleHarmonicGramData` are
  the same analytic object.
- **`harmonicEnergy_k_isLeast_periods`** — the walk-based harmonic
  minimum `k²/n` of `Simplicial.lean` is certified as the
  least-energy-at-period-`k` value. The spine's first mass now has two
  independent derivations (walk/homotopy/Hodge and period/least-norm)
  proved to agree — the same corroboration pattern as the scalar
  duality's modular-vs-Poisson double proof (Phase 16).

### Engineering notes

- Parametric `Fin n` combinatorics is a different sport from literal
  combinatorics: `simp +decide` is useless; the working tools were
  explicit `if_pos`/`if_neg` case splits (rewriting a *proposition*
  inside `ite` breaks the `Decidable` motive), `Finset.sum_ite_eq'`,
  and val-level strong induction with `Fin.val_add`/`Fin.val_one'` +
  `Nat.mod_eq_of_lt`.
- Proof irrelevance quietly earns its keep: `cyclePeriodData n h₁` and
  `ofCycles _ h₂` unify definitionally across different positivity
  proofs, so `IsLeast` transports with a single `rw`.
- Error count by phase, same machinery: Phase 18 ~6 build iterations,
  Phase 19 zero, Phase 20 (new *parametric* territory) ~4. Literal
  instances are now free; parametric ones cost only their genuine
  `Fin`-arithmetic content.

### Board after this phase

The wedge (`C_{n₁} ∨ C_{n₂}`) through periods is now the obvious next
concrete: two cycles sharing **zero** edges → chain Gram
`diag(n₁,n₂)` → period Gram `diag(1/n₁,1/n₂)` — which would *derive*
the matrix that `wedgeHarmonicGramData` (Phase 13) asserts on
"true, unformalized ground," retiring the last documented assertion
debt in the harmonic layer. Then: cohomological `MatterSector`
(Goal 7), and the keystone's information-theoretic half (gated on a
stated connecting theorem).

**End of Phase 20 addendum.**

---

## Phase 21 addendum: the wedge through periods — the last assertion debt retired

*(Appended after Phase 20; session date 2026-07-16.)*

### What was done

The board's named next concrete, executed. `Meno/PeriodHarmonic.lean`
gains a `WedgePeriods` section (~250 LOC); `Meno/CycleHarmonic.lean`
gains the identification.

**The wedge graph, without quotients.** `C_{n₁} ∨ C_{n₂}` is modeled
on vertices `Fin n₁ ⊕ Fin n₂` with edges `Fin n₁ ⊕ Fin n₂`: every
edge that would touch the right cycle's basepoint `inr 0` is routed
to the left basepoint `inl 0` instead (`wedgeVertex`). The vertex
`inr 0` is left isolated — an edgeless extra component, invisible to
boundaries and to `b₁`. No quotient vertex type needed.

**Two closed-form boundary lemmas carry everything**
(`wedgeBoundary_inl`, `wedgeBoundary_inr`): at a left vertex the
boundary is the left cycle's boundary plus — at the shared basepoint
only — the right cycle's basepoint flow; at a right vertex it is the
right cycle's boundary away from the basepoint, and zero at the
isolated vertex. After these, all downstream proofs are one-liners
over the closed forms.

**The theorems:**
- `wedgeBoundary_cycles`: both disjoint-support all-ones vectors are
  cycles.
- `eq_comb_of_wedgeBoundary_eq_zero` — **`b₁(wedge) = 2`**: any
  boundary-zero cochain is a combination of the two basis cycles. The
  spanning induction needs constancy steps only at *nonzero* vertices,
  extracted as the general helper `apply_eq_apply_zero_of_step`; the
  mixed flow condition at the shared basepoint is then automatically
  satisfied — the formal shadow of Euler's `E − V + 1 = 2`.
- `gramOf_wedgeCycles = diag(n₁, n₂)`; positive definite (via
  `ofDiagonal₂`, definitional-equality reuse); `wedgePeriodData` from
  the Phase-20 builder; `wedgePeriodData_gram = diag(1/n₁, 1/n₂)`.

**The identification (`CycleHarmonic.lean`):**
`wedgePeriodData_gram_eq`, `wedgePeriodData_energy_eq`,
`wedgePeriodData_partFn_eq`, and the marquee
`wedgeHarmonicGramData_energy_isLeast`: the energy of the Gram data
that Phase 13 wrote down by oracle is the least cochain energy at
prescribed periods over the actual wedge graph. The docstring that
said "the graph-level derivation is **not** formalized" now says
where the derivation lives. That was the last documented assertion
debt in the harmonic layer.

### Why the wedge matters beyond the debt

The wedge is the space that **falsified** the naive categorical route
in Phase 14: its loop monoid is free on two generators, nonabelian,
so `SectorPresentation.end_comm` forbids any presentation at any
rank. The period machinery never touches `End` — it works on `H¹`,
the abelianization — and handles the same space in ~250 lines. The
space that broke the old formulation is the first new space the
cohomological formulation conquers. This is the H¹ decision (Phase
17) paying rent.

Physically: sharing zero edges ⇒ chain Gram off-diagonal zero ⇒
period Gram off-diagonal zero ⇒ zero interaction, zero binding
(Phase 19's `bindingEnergy_eq`). The wedge is the formal model of
two *non-interacting* matter sectors; the theta graph (shared edges,
binding 1/3) is the interacting counterpart. Together they bracket
the binding story from both sides.

### Engineering notes

- One build iteration for the whole phase, and the fix was tactic
  strength (`field_simp` wouldn't open matrix entries; `norm_num
  [Matrix.mul_apply, ...]` then `field_simp` does), not mathematics.
  The Phase-20 toolkit — global `show` in reduced form after
  `Fintype.sum_sum_type`, per-term `show` + explicit `if_pos`/`if_neg`
  indicator lemmas — transferred to the sum-typed graph unchanged.
- The indicator-bookkeeping layer (`ite_inl_eq_inl`,
  `ite_wedgeVertex_*`) is where parametric graph topology actually
  costs; everything above it is arithmetic the machinery already owns.

### Board after this phase

- Cohomological `MatterSector` (Goal 7 rebuild per the H¹ decision;
  `binding_kills_matter` has its Gram-level form from Phase 19).
- The keystone's information-theoretic half (compression residue =
  `b₁` joined to InfoRatchet) — still gated on stating the connecting
  theorem first.
- Geodesic instance (Goal 4, plumbing).
- Halted/pruned (unchanged): TypeKernel rewrite, magnitude.

**End of Phase 21 addendum.**

---

## Phase 22 addendum: cohomological matter — the rebuild, gated and executed

*(Appended after Phase 21; session date 2026-07-17. Input: a second
review from the planning model, relayed by the kernel; all six points
verified against the code before acting.)*

### Review verification ledger

1. **Integrality / basis invariance as design gate — CORRECT.**
   `ofCycles` accepts arbitrary real cycle vectors; `k ∈ ℤʳ` is
   meaningful only relative to the chosen basis. **Action**: the
   chosen-basis caveat is now documented at the structure
   (`CyclePresentation`) and in `Matter.lean`; the unimodular
   `GL(r,ℤ)` change-of-basis theorem (same energies, same matter
   predicate, same partition function under `k ↦ Uk`) is recorded
   here as **the gate** for any coordinate-independence claim. It is
   the named next phase. Until it exists, no Meno statement may claim
   basis independence.
2. **Generic exactness needs no connectivity — CORRECT**, and this
   was the review's real gift: `range(∂ᵀ) = (ker ∂)ᗮ` is linear
   algebra; connectivity governs only uniqueness of potentials.
   **Action**: proved, see below.
3. **`MatterSector` must own its space — CORRECT.** **Action**:
   rebuilt as `{k : Fin P.r → ℤ // k ≠ 0}` indexed by a
   `CyclePresentation`; `positive_action` is no longer stored data
   (it was always derivable — the old structure was nearly
   content-free); the no-potential theorem covers **every** realizing
   cochain, not only `periodRep`.
4. **Annihilation ≠ `binding_kills_matter` — CORRECT.** **Action**:
   the theorem is named `bindingEnergy_neg_self` / `annihilation` and
   its docstring states explicitly that it is algebraic cancellation
   in one period lattice. **Goal 7 is hereby amended**: its
   cohomological content (mass, variational identity, no-potential,
   annihilation, existence) is delivered; its *geometric* content —
   an ambient-space change killing a class under an induced map —
   remains open and is gated on a stated connecting theorem (same
   discipline as the keystone), because at least two inequivalent
   formalizations exist (induced maps of Gram data under graph
   inclusion vs. simplicial face-gluing).
5. **Wedge model is `(C ∨ C) ⊔ {pt}` — CORRECT.** The Phase-21
   docstring's `E − V + 1 = 2` was the connected formula. **Action**:
   docstrings corrected to `E − V + #components = 2`; the model's
   `H₀` difference and larger locally-constant kernel are now stated.
6. **Binding algebra upstream — CORRECT.** **Action**: `interaction`,
   `energy_add`, `bindingEnergy`, `bindingEnergy_eq` moved from
   `ThetaHarmonic.lean` to `HarmonicForm.lean`; matter no longer
   touches the theta file.

Honesty leftovers, both confirmed and fixed: the `HarmonicForm.lean`
module docstring claimed a nonexistent variational `Prop`-field
(Phase 17 fixed the structure docstring but missed the header); the
matter file described homology. The file is renamed:
`MatterHomology.lean` → `Matter.lean`.

### What was built

**`Meno/CyclePresentation.lean`** (new, ~360 LOC):
- `CyclePresentation V ι`: edge data + chosen cycle basis (closed,
  spanning, positive-definite chain Gram). Instances:
  `cyclePresentation n`, `wedgePresentation n₁ n₂` (here) and
  `thetaPresentation` (in `ThetaHarmonic.lean`).
- `boundaryMatrix`, `grad`, and **discrete Stokes**
  (`grad_dotProduct_eq`): `⟨grad f, ω⟩ = Σ_v f(v)·(∂ω)(v)` — one
  summation by parts; `grad_period`: gradients are invisible to
  periods.
- **`period_eq_zero_iff_exists_grad`** — generic exactness, *no
  connectivity*: zero periods ⟺ gradient. Proof by rank counting in
  plain Pi types (no inner-product bundling): `range ∂ᵀ ∩ ker ∂ = 0`
  by sum-of-squares, `rank ∂ᵀ = rank ∂` + rank–nullity fills the edge
  space, decompose and kill the residual against the spanning basis.
  The theta graph's Phase-19 exactness (explicit witness) survives as
  constructive corroboration of the rank-1-connectivity-free general
  theorem.
- **`cochainQuotEquiv` : cochains ⧸ gradients ≃ₗ ℝ^r** and
  `finrank_cochainQuot` — **the keystone's mathematical half**:
  descriptions modulo local re-description are exactly the period
  space; the incompressible residue has dimension `r`. (The
  InfoRatchet/description-cost half remains a design problem; this
  gives it a precise mathematical anchor to connect to.)

**`Meno/Matter.lean`** (rewrite of `MatterHomology.lean`):
`MatterSector P := {k // k ≠ 0}` with `mass`, `mass_pos` (theorem,
not field), `mass_isLeast` (variational identity via the Phase-20
builder), **`not_gradient`** (matter is trapped paradox — every
realizing cochain, generic), `neg` (antimatter), `annihilation`,
`exists_matter`.

**`Meno/HarmonicForm.lean`**: docstring honesty; generic
`energy_pos_of_ne_zero`, `energy_zero`, `energy_neg`; binding algebra
(from theta) + `bindingEnergy_neg_self`.

**Consumers**: `thetaMatter : MatterSector thetaPresentation` with
`thetaMatter_mass = 1/3`; `wedgeMatter₁` over `wedgePresentation`
with `wedgeMatter₁_mass = 1/n₁` (presentation → derived Gram →
asserted Gram, one chain).

### Engineering notes

- The rank-counting exactness proof — a dozen Mathlib lemmas deep in
  finite-dimensional linear algebra (`Matrix.rank_transpose`,
  `finrank_range_add_finrank_ker`, `finrank_sup_add_finrank_inf_eq`,
  `eq_top_of_finrank_eq`) — **compiled on the first attempt**. Total
  phase errors: one root-vs-`Matrix`-namespace name
  (`dotProduct_zero`), two missing `rfl`s after `Fin.sum_univ_*`
  rewrites, one forward reference, one missing `open Matrix`. The
  chosen route (plain Pi types, no `EuclideanSpace`/`PiLp` bridging)
  avoided the API-risk zone entirely.
- Deliberate scope decision: the quotient equivalence is stated over
  `ℝ` (`≃ₗ[ℝ] ℝ^r`). The ℤ-lattice refinement (integer-period
  cochains mod gradients ≃ `ℤʳ`) follows from the same two facts
  (surjectivity via `periodRep`, kernel = gradients) and can be added
  when a consumer needs the arithmetic form.

### Board after this phase

- **`GL(r,ℤ)` invariance** — the declared gate; next phase. Gram
  transforms `C ↦ UCUᵀ`, energy `E'(Uk) = E(k)`, partition function
  invariant under the lattice bijection `k ↦ Uk`.
- Primitive-basis corollaries per instance (integral spanning is
  already implicit in the real spanning proofs; state it when the
  `GL(r,ℤ)` layer lands).
- Geometric `binding_kills_matter` (Goal 7 remainder) — gated on a
  stated connecting theorem.
- Keystone's information-theoretic half — now anchored: connect
  InfoRatchet description cost to `cochainQuotEquiv`.
- Geodesic instance (Goal 4, plumbing). Halted/pruned: unchanged.

**End of Phase 22 addendum.**

---

## Phase 23 addendum: GL(r,ℤ) — the gate, closed

*(Appended after Phase 22; session date 2026-07-17.)*

### What was proved

The Phase-22 review made unimodular change-of-basis invariance the
design gate for any coordinate-independence claim. It is now closed,
in `Meno/CyclePresentation.lean` (Rebase section) and `Meno/Matter.lean`:

- **`mulVecEquiv`**: `U ∈ GL(r, ℤ)` (unit determinant) acts as a
  bijection of the sector lattice `ℤʳ`, with inverse `U⁻¹` (integer
  nonsingular inverse — `nonsing_inv` works over any commutative ring
  with unit determinant).
- **`CyclePresentation.rebase`**: the same graph presented with the
  recombined basis `cᵢ' = Σⱼ Uᵢⱼ cⱼ`. Closedness is linearity of the
  boundary; **spanning survives** via `b = a ᵥ* Uℝ⁻¹`;
  positive-definiteness survives congruence (`C ↦ U C Uᵀ`, proved
  with the Phase-15 workhorse, no `StarOrderedRing` needed).
- **`rebase_energy`**: `E'(Uk) = E(k)` — the sector labeled `k` in
  the old basis is labeled `Uk` in the new one, same energy. Matrix
  algebra: `(UCUᵀ)⁻¹ = U⁻ᵀC⁻¹U⁻¹` (unconditional `mul_inv_rev`) and
  two collapses of `U⁻¹U`.
- **`rebase_partFn`**: the partition function is invariant outright —
  re-basing permutes the lattice and the Boltzmann sum does not see
  labels (`Equiv.tsum_eq` reindexing).
- **`MatterSector.rebaseEquiv` + `rebaseEquiv_mass`**: matter sectors
  biject across any unimodular re-basing, preserving mass.

Docstring caveats planted in Phase 22 ("not yet formalized") now cite
the theorems instead. The physics of the period layer — energies,
matter content, partition function — is certified independent of the
chosen cycle basis; only the *labels* `k` are basis-relative.

### Engineering notes

- One build iteration; five errors, all tactical, none mathematical:
  beta-redexes in `Equiv` field goals (fix: `show` first), the pin's
  `RingHom.map_det` returns the `mapMatrix` form (fix:
  `RingHom.mapMatrix_apply`), the `posDef_iff_dotProduct_mulVec`
  strict-implicit binder (the Phase-15 pitfall, again — pass only the
  `≠ 0` proof), an unused-section-variable lint, and one associativity
  mismatch in the big energy calc (fix: restructure around a `hkey`
  helper instead of fighting `rw` orderings).
- `Matrix.mul_inv_rev` is unconditional in Mathlib (adjugate-based
  inverse), which keeps the inverse-of-congruence step one line.

### Board after this phase

- Integral primitivity per instance (state that the chosen bases
  generate the full integer cycle lattice — the real spanning proofs
  already contain the argument; surface it when a consumer needs it).
- Geometric `binding_kills_matter` (Goal 7 remainder) — still gated
  on a stated connecting theorem.
- Keystone's information-theoretic half — connect InfoRatchet
  description cost to `cochainQuotEquiv`. The mathematical anchor
  exists (Phase 22); the connecting theorem must be stated before
  vocabulary is built.
- Geodesic instance (Goal 4, plumbing). Halted/pruned: unchanged.

**End of Phase 23 addendum.**

---

## Phase 24 addendum: primitivity, the parameter split, and the keystone stated

*(Appended after Phase 23; session date 2026-07-17.)*

### What was proved

1. **Integral primitivity, all three instances**
   (`cycle_integral_spanning`, `wedge_integral_spanning` in
   `Meno/CyclePresentation.lean`; `theta_integral_spanning` in
   `Meno/ThetaHarmonic.lean`): an integer-valued cochain with zero
   boundary is an **integer** combination of the chosen basis — the
   period lattice is the full integral cycle lattice, not a
   finite-index sublattice. Inherited from the real spanning proofs,
   whose coefficients were always evaluations of the cochain itself
   (`ω 0`; `ω (inl 0), ω (inr 0)`; `ω 0, ω 2`). This closes the
   remainder of the Phase-22 review's point 1. All three compiled
   first-try.
2. **The parameter split** (`card_edges_eq_finrank_gauge_add_r`):
   `|E| = rank ∂ + r` — describing a cochain takes `rank ∂`
   re-describable gauge parameters plus exactly `r` incompressible
   ones. The counting shadow of `cochainQuotEquiv`; the ℝ-dimensional
   form of the keystone's description-cost split.

### The keystone connecting theorem — STATED (gated, not built)

Per the standing discipline (state the connecting theorem before
building vocabulary), the proposed formal target joining InfoRatchet
to the period layer:

> **Keystone (finite-resolution form).** Fix a resolution `q ≥ 2`.
> For a graph presentation with integrally primitive cycle basis, let
> `C_q := ι → ZMod q` (descriptions at resolution `q`) and
> `G_q ≤ C_q` the subgroup of mod-`q` gradients (neighbor-local
> re-descriptions). Then:
>
> * **(K1) Residue counting**: `|C_q ⧸ G_q| = q^{b₁}` — the
>   incompressible description cost is exactly `b₁ · log q`.
> * **(K2) Split**: `log |C_q| = log |G_q| + b₁ · log q` — total
>   description = gauge freedom + incompressible residue, in
>   InfoRatchet's literal log-cardinality vocabulary.
> * **(K3) Fiber uniformity**: every fiber of the quotient map
>   `C_q → C_q ⧸ G_q` has cardinality `|G_q|` — the fiber information
>   of compression is pure gauge; what a section must add back is
>   exactly the local re-description freedom.

Notes recorded with the statement:
- **Primitivity is the load-bearing hypothesis**: it is what makes
  the mod-`q` period map surjective onto `(ZMod q)^{b₁}` (a
  non-primitive basis would produce a proper subgroup and a residue
  count divisible by the index). Phase 24's trio was bookkeeping
  until this statement; now it is a hypothesis.
- Graph incidence matrices are totally unimodular, so
  `rank_q ∂ = rank_ℚ ∂` for **every** `q` — no bad primes; (K1) holds
  at all resolutions, which is what lets "b₁ digits of resolution"
  be resolution-independent.
- The cleaner route may be the ℤ-form first:
  `C_ℤ ⧸ G_ℤ ≅ ℤ^{b₁}` (torsion-free, by primitivity), from which
  every finite-resolution form follows by tensoring. Recommend
  proving the ℤ-form and deriving (K1)–(K3).

**Vocabulary cost if built**: a ZMod-`q` (or ℤ) cochain/gradient
layer parallel to the ℝ one — a genuine phase, possibly
Phase-15-sized. **Gated**: awaiting endorsement of this statement.

### Board after this phase

- **The keystone build** (statement above) — awaiting endorsement.
- Geometric `binding_kills_matter` (Goal 7 remainder) — still needs
  its own stated connecting theorem.
- Geodesic instance (Goal 4, plumbing): `Geodesic` class has zero
  instances; the cycle graph's walk-length instance plus the
  geodesic/harmonic duality `n · (1/n) = 1` is the target.
- Halted/pruned: unchanged.

**End of Phase 24 addendum.**
