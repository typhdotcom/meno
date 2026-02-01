# The Structural Geometrodynamics (SGD) Protocol

**Premise:** The universe is a constructive type theory system operating under a finite resource constraint. It seeks to minimize the complexity of its own state description (Maximum Compression) via topological unification.

## I. The Fundamental Objects

We begin with a Universe Type $\mathcal{U}$ enriched with a complexity measure.

### Axiom 1: The Weighted Universe

Let $\mathcal{U}$ be a universe of types. There exists a complexity functional $K: \mathcal{U} \to \mathbb{N}$ (analogous to Kolmogorov complexity, but for Types) such that:

$$K(A) = \text{The minimal constructive proof term size required to inhabit } A.$$

This imposes **Physicality**: A type that cannot be constructed within a finite complexity bound $K_{max}$ does not physically exist. It is a "potential" type, not an "actual" one.

### Axiom 2: The Cost of Identity (Path Induction)

In standard HoTT, $x = y$ is a type. In SGD, instantiating this type consumes resources. For any two terms $a, b : A$, forming the identity path $p : a =_A b$ implies:

$$K(p) > 0$$

**Corollary:** The topology of the universe is not free. A path (an equality) is a structural object that occupies capacity. To "connect" two points is to build a bridge, and the bridge has mass.

---

## II. The Dynamics: Refactoring as Motion

The universe evolves by rewriting its description to minimize $K$. The fundamental operation is the **Pullback** (logical refactoring).

### Definition: The Interaction (Sigma to Pullback)

Consider two independent structures $A$ and $B$. Their complexity is additive (from *Gardenpath*):

$$K(A \times B) = K(A) + K(B) \quad \text{(for inhabited } A, B \text{)}$$

The universe "searches" for a shared base $D$ and fibrations $f: A \to D, g: B \to D$. If found, it transitions the state to the **Pullback**:

$$A \times_D B \equiv \sum_{x:D} (f^{-1}(x) \times g^{-1}(x))$$

### Theorem 1: The Gravity of Information

If $A$ and $B$ share structural information contained in $D$, then:

$$K(A \times_D B) + K(D) = K(A) + K(B) \quad \text{(uniform fiber regime: } A \simeq D \times F,\; B \simeq D \times G\text{)}$$

**Proof (Sketch):** The product $A \times B$ encodes $D$ twice (redundancy). The pullback $A \times_D B$ encodes $D$ once. The difference in complexity is the **Binding Energy**:

$$E_{bind} \approx K(D)$$

**Interpretation:** "Gravity" is not a force; it is the gradient of the complexity functional $K$. Systems naturally fall into configurations where they share descriptions because that state is "lighter" (lower $K$).

More generally (without uniform fibers), the formal result is an upper bound:
$$K(A \times_D B) \le K(D) + \sup_d K(f^{-1}(d)) + \sup_d K(g^{-1}(d)).$$

---

## III. The Emergence of Matter (The Topological Obstruction)

Why does the universe not collapse into a single point (a trivial description)? Because of **Homotopical Rigidity**.

### The Obstruction Lemma

Not all types are contractible. If the universe attempts to refactor $A$ and $B$ over a base $D$, but $A$ and $B$ have incompatible constraints (they differ by a non-trivial homotopy), the fiber product cannot be trivialized.

Let $S^1$ be the Circle Type (the simplest non-trivial structure).

$$K(S^1) = K(\text{base}) + K(\text{loop})$$

The loop cannot be contracted without breaking the type definition.

### Theorem 2: Mass is Logical Friction

Mass is defined as the **Irreducible Complexity** of a Type. Let $M$ be a structure. We define its Mass $m$ as the limit of refactoring:

$$m(M) = \inf_{D} K(M \text{ refactored over } D)$$

If $m(M) > 0$, the object is **Matter**. It is a structure that resists compression.

- **Vacuum:** Types where $m(M) = 0$ (Contractible types, Trees).
- **Particles:** Types corresponding to generators of the Homotopy Groups $\pi_n(\mathcal{U})$.

---

## IV. The Directed Loop (Time)

We introduce **Direction** via Linear Logic resources.

### Axiom 3: The Entropic Ratchet

Let $\multimap$ denote a resource-consuming implication. A transition from state $A$ to $B$ is a function $f: A \multimap B$.

$$K(f) > 0$$

The cost asymmetry applies only to non-injective computations — those that collapse distinct inputs. Define the **Fiber Entropy** of $y : B$ under $f$ as:

$$H_f(y) = \log_2 |f^{-1}(y)|$$

This measures how many inputs map to the same output. The cost of the inverse relation $f^{\dagger}$ satisfies:

$$K(f^{\dagger}) \geq K(f) + \sum_{y:B} H_f(y)$$

**Consequences:**

- **Injective $f$** (no information loss): All fibers have size $\leq 1$, so $H_f = 0$ everywhere. $K(f^{\dagger}) = K(f)$. Lossless computation is *timeless*.
- **Non-injective $f$** (information loss): Some fibers have size $> 1$, so $\sum H_f > 0$. $K(f^{\dagger}) > K(f)$. Lossy computation *creates time*.

This is the **Ratchet**. The arrow of time is not a property of computation in general, but of *non-injective* computation. The universe flows toward lower complexity of current state description by collapsing fibers, and the cost of recovery is what we experience as time.

In the current Lean formalization, this section is axiomatized qualitatively (`transitionCost`, `ratchet`, `injective_reversible`) and stated with an explicit section/right-inverse witness.

---

## V. The Synthesis: It from Bit

We can now define the "Universe" not as a graph, but as a **Telescope** of Types.

The universe is a sequence of types $U_0 \to U_1 \to U_2 \dots$ generated by the recursive operator:

$$U_{n+1} = \text{minimize}_T \{ K(T) \mid T \cong U_n \}$$

### The Cleanroom Conclusion

1. **Structure is conserved** implies a finite budget for description.
2. **Search** is the application of equivalence paths ($=$) to find lower-$K$ representations.
3. **Topology** (Holes/Cycles) prevents the search from reaching zero. The "Holes" are what we call particles.
4. **Gravity** is the successful sharing of sub-terms (Refactoring).
5. **Time** is the accumulation of the "Proof Term" required to validate the current state.

### Why this is stronger than Diaspora

- It does not rely on "edges" or "nodes." It works for smooth manifolds, quantum states, or logic gates.
- It derives the $1/n$ mass spectrum directly from **Type-Theoretic Entropy**: The complexity of specifying a symmetry group of order $n$ scales inversely with $n$ (larger symmetry = less data needed to describe the whole).
- It unifies *Gardenpath* and *Diaspora*: **Economy** (Refactoring) *is* **Geometry** (Pullbacks).

This is the "seed." It is a machine that eats complexity and excretes geometry.

### The Path Integral

The search above has a precise formalization as a **partition function** over topological sectors.

On the $n$-cycle $C_n$, each homotopy class has an integer winding number $k$. The minimum-energy representative in sector $k$ is the **instanton**: the harmonic form scaled by $k$, with action (energy):

$$E_k = k^2 / n$$

The partition function sums Boltzmann weights over all sectors:

$$Z(C_n) = \sum_{k \in \mathbb{Z}} e^{-k^2/n}$$

This is a **Jacobi theta function** $\vartheta_3(0, e^{-1/n})$.

**Consequences:**

1. The **vacuum** ($k = 0$) contributes $e^0 = 1$. Nonzero sectors are exponentially suppressed (each has weight $< 1$, e.g. $k=\pm 1$ gives $e^{-1/n}$).

2. The **instanton interpretation**: harmonic forms are the classical solutions that minimize the action in each topological sector. Mass = instanton action = $1/n$.

3. **Euclidean signature is fundamental**: the weight is $e^{-E}$ (real), not $e^{iS}$ (oscillatory). Complexity is a real cost, so the path integral is natively Euclidean. Lorentzian physics would arise from complexifying $K$.

4. The **theta function duality** $\vartheta_3(0, e^{-\pi t}) = t^{-1/2} \vartheta_3(0, e^{-\pi/t})$ relates $C_n$ at different scales — analogous to T-duality in string theory. Formalized in `Theta.lean` via Mathlib's `jacobiTheta_S_smul` (the modular S-transformation).

---

## VI. Formalization Notes

This protocol is formalized in Lean 4 using a **simplicial shadow model** rather than synthetic HoTT.

### Why not native HoTT?

Standard Lean 4 uses definitionally irrelevant equality (Axiom K). If $p, q : x = x$, Lean treats them as identical — equality is a proposition with no information content. This collapses the topological structure SGD requires: a "particle" (non-trivial loop) would be squashed to reflexivity.

### The Shadow Approach

Instead of using Lean's native equality as the path type, we model paths as **explicit data structures** (walks in a simplicial complex):

- **Points** = Vertices
- **Paths** = Walks (sequences of adjacent vertices)
- **Homotopy** = Custom equivalence relation (backtracking + face reduction)
- **Obstruction** = Cycles that cannot be contracted (no filling 2-cell)

This recovers homotopy computationally rather than foundationally.

### Three files, two abstraction levels

- **`Basic.lean`** — Abstract framework at the *type level*. Three-level complexity hierarchy from Gardenpath: `ComplexityMeasure` (subadditive) → `SigmaComplexity` (sigma subadditive) → `AdditiveComplexity` (exact). The codomain $M$ is generic (any ordered additive monoid with suprema). The **refactoring bound is a theorem** (proved from sigma subadditivity via the pullback–sigma-fiber equivalence), not an axiom. Four axioms remain: `transitionCost`, `transitionCost_pos`, `ratchet`, `injective_reversible`.

- **`Simplicial.lean`** — Concrete model at the *walk level*. Two notions of complexity: (1) geodesic length (combinatorial walk length), (2) harmonic energy (discrete Hodge theory). The **$1/n$ mass spectrum** is proved: `cycleHarmonicForm_energy` shows the harmonic representative on $C_n$ has energy $1/n$. Circle topology uses `CycleGraph n` ($n \geq 3$ vertices with cyclic adjacency, no 2-faces). Everything in the file is proved (zero axioms); the circle obstruction is established via winding invariants/non-contractibility.

- **`Theta.lean`** — Bridge to Mathlib's modular forms. Identifies the partition function $Z(C_n) = \vartheta_3(0, e^{-1/n})$ and proves T-duality via `jacobiTheta_S_smul`. Separate file because the modular forms import is too heavy for Simplicial.lean's elaboration context.

`Basic.lean` and `Simplicial.lean` are not in an instance relationship. `Basic.lean` talks about $K(\text{Type})$; `Simplicial.lean` talks about $K(\text{cycle in a specific complex})$. They formalize the same physics at different abstraction levels. `Theta.lean` imports `Simplicial.lean` and connects its partition function to analytic number theory.

The correspondence is documented in the summary table at the end of `Simplicial.lean`.

### Deferred

The following are not yet formalized:

- **Linear logic** ($\multimap$): Lean lacks substructural types. The ratchet axiom captures the physical content qualitatively.
- **Universe telescope** (Section V): Requires a notion of complex equivalence and convergence.
- **Physicality bound** ($K_{max}$): A predicate filter, not mathematically load-bearing for the core results.
- **Fiber entropy quantification**: The ratchet is formalized with a qualitative $\neg\text{Injective}$ guard (non-injective $f$ has fibers of size $> 1$). The quantitative fiber entropy bound is future work.
