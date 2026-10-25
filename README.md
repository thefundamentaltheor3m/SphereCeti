# SphereCeti

A TauCeti-style roadmap for a unified Lean development of sphere packing in dimensions 8 and 24,
starting from the existing `Sphere-Packing-Lean` definitions and culminating in optimality and
uniqueness among periodic packings for the E8 and Leech configurations.

This repository is a **roadmap together with precise target statements that Lean type-checks,
with the proofs omitted**; it is not a competing production formalization.  The intended
production home remains
[`thefundamentaltheor3m/Sphere-Packing-Lean`](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean),
with generic mathematics upstreamed to Mathlib or TauCeti as appropriate.

`README.md` is definitive.  [`SphereCetiRoadmap/Suggested.lean`](SphereCetiRoadmap/Suggested.lean) records
suggested formal statements of the key definitions and theorems, but it is deliberately
nonexhaustive and may be adjusted when implementation reveals a form closer to Mathlib's
conventions.

## Reading this roadmap

Readers who do not use Lean may find the following conventions helpful.

- **Mathlib, TauCeti, Sphere-Packing-Lean.**  Mathlib is Lean's general mathematics library;
  TauCeti is a library built on Mathlib and developed from coordinated roadmaps like this one;
  Sphere-Packing-Lean is the existing project formalizing the dimension-8 proof, called the
  *production* repository because the mathematics of this roadmap is to be implemented there.
- **Upstream.**  Mathlib and TauCeti, the libraries this project builds on.  A result goes
  upstream when it is contributed there; [`UPSTREAM.md`](UPSTREAM.md) lists the candidates.
- **Layers, phases, and PRs.**  The roadmap is organized in *layers*, stages of the mathematics,
  each building on the earlier ones.  [`MIGRATION.md`](MIGRATION.md) divides the implementation
  into *phases* of planned *pull requests* (PRs), each a single reviewed contribution of code.
- **Targets and `sorry`.**  A target is a definition or theorem the roadmap asks to be formalized.
  In `Suggested.lean` each target is stated precisely and its proof, or the body of a definition, is
  usually `sorry`, Lean's placeholder for missing work.  Lean checks that each statement is
  well-formed and type-correct, not that it is true or that it is the intended one; that is for
  human review.  A proof that relies on other targets is complete only once those are proved.  A
  definition whose body is `sorry` unfolds only to that placeholder, so it determines nothing, and
  any property it must have is stated as a separate theorem.
- **Assumed theorem.**  An unproved roadmap target on which another proof relies, such as the
  classification of even unimodular lattices of rank 8.  It is a statement still to be proved,
  here or in the library named as its intended home; it is never introduced as a named axiom, and
  until it is proved, `#print axioms` and the compiled audit list `sorryAx` among the axioms of
  every proof depending on it.
- **`#check` lines.**  A `#check` line makes the build fail unless the named declaration exists,
  and displays its type for comparison with the intended statement.
- **Fixed ("pinned") versions.**  The Lean toolchain, TauCeti, and the Mathlib commit TauCeti
  resolves to are fixed at the versions listed below, so that every statement is checked against
  exactly the same libraries.  The Sphere-Packing-Lean baseline is likewise a fixed commit, whose
  definitions `Pinned.lean` restates.
- **Structures, fields, constructors.**  A *structure* bundles data with required properties; its
  components are called *fields* (unrelated to algebraic fields), and a *constructor* builds an
  element of the structure: the basic one from the fields themselves, and derived constructors,
  such as `Certificate.ofRadial`, from other data.
- **Cohn–Elkies certificate.**  `CohnElkies.Certificate d r` consists of a Schwartz function `f`
  on `ℝ^d` together with the properties the Cohn–Elkies bound requires of it: `r > 0`; `f` and its
  Fourier transform `f̂` are real-valued; `f(x) ≤ 0` whenever `‖x‖ ≥ r`; `f̂ ≥ 0` everywhere; and
  `f̂(0) > 0`.  The Fourier transform is normalized with the kernel `exp(-2πi⟨x, ξ⟩)`.
- **Direct side, Fourier side, shells.**  Statements about `f` are on the *direct side* and
  statements about `f̂` on the *Fourier side*.  A *shell* of a lattice is the set of its vectors of
  a given squared norm; for E8 and Leech the nonzero shells have squared norms `2n`.
- **Kernels.**  Besides the Fourier kernel, *kernel* refers to the expressions `g`, built from
  quasimodular and weakly holomorphic modular forms, in the contour integrals
  `∫ g(z) exp(πi‖x‖²z) dz` defining the magic functions.
- **Chosen representatives.**  Where an argument needs one center from each orbit of the period
  lattice, it uses a chosen representative.  The quotient of the centers by the period lattice is
  the canonical object, and every stated result is independent of the choice.
- **Values outside the domain.**  Lean's functions are defined everywhere: division by zero, the
  integral of a non-integrable function, and the derivative at a point of non-differentiability
  are given conventional values (usually `0`).  Statements therefore carry explicit integrability
  and differentiability hypotheses, so that they do not become true, or false, merely because of
  these conventions.
- **Automation attributes.**  `@[simp]`, `@[grind]` and `@[fun_prop]` register a lemma with Lean's
  automatic rewriting and proof-search tools.  They change how proofs are found, not what is true.
- **Coercions and `ℝ≥0∞`.**  A coercion is an implicit map, such as `ℕ → ℝ` or the inclusion of a
  lattice into its ambient space.  `ℝ≥0∞` denotes the extended nonnegative reals `[0, ∞]`, where
  densities take their values.

## The two deliberate differences from TauCetiRoadmap

SphereCeti follows TauCetiRoadmap's mathematical and library-design discipline, with two explicit
changes.

1. **SphereCeti depends on a fixed version of TauCeti.**  TauCeti is not merely a cited source or
   an informal destination: it is a Lake dependency fixed at a specific commit, so the TauCeti
   results imported by `Suggested.lean`, and the checks of required declarations, are
   reproducible.
2. **Candidates for Mathlib and TauCeti are listed in one file.**  There is no parallel directory
   tree of proposed Mathlib or TauCeti roadmaps.  [`UPSTREAM.md`](UPSTREAM.md) lists the
   declarations and larger topics whose intended home is Mathlib or an appropriate TauCeti
   roadmap, each described so that it can be filed as an issue.  It records intended homes only:
   acceptance upstream is never a prerequisite for any SphereCeti target.

## Exact dependency snapshot

| Component | Pin |
|---|---|
| Lean toolchain line | `leanprover/lean4:v4.36.0-rc1` |
| TauCeti | `271e1af4dd54c50b9192cf3e213b7686843a0b3a` |
| Exact Mathlib commit resolved by that TauCeti snapshot | `2cabef97b63d3275776b8b060d802de6a6fa1055` |
| Sphere-Packing semantic baseline | `bad3de916074748eb88b7d1ee6dbf9494361ad17` |

Here “the 4.36.0-rc1 Mathlib pin” means the **Lean/Mathlib release line** selected by the toolchain,
while source reproducibility is supplied by the exact Mathlib commit in `lake-manifest.json`.  We do
not add an independent floating Mathlib requirement beside TauCeti: SphereCeti must use the same
resolved Mathlib graph as its pinned TauCeti dependency.

The TauCeti dependency is the complete repository snapshot at the SHA above, not a
contour-specific release.

The pinned Sphere-Packing baseline uses Lean/Mathlib `v4.32.0`, which is incompatible with this
package's dependency graph.  [`SphereCetiRoadmap/Pinned.lean`](SphereCetiRoadmap/Pinned.lean) therefore models the
public structures and semantic normalizations at that exact production commit.  Layer 0 upgrades
production to the shared dependency line; PR A2 then deletes the compatibility model and replaces
it with direct imports.  The compatibility model is not permitted to become a second
implementation.

The committed `lake-manifest.json` records the entire resolved dependency graph from the TauCeti
snapshot, not merely the user-facing TauCeti SHA.

## Main theorems

The density statements are:

```lean
theorem spherePackingConstant_eight :
    SpherePackingConstant 8 = ENNReal.ofReal (Real.pi ^ 4 / 384)

theorem spherePackingConstant_twentyFour :
    SpherePackingConstant 24 =
      ENNReal.ofReal (Real.pi ^ 12 / Nat.factorial 12)
```

The dimension-specific optimality statements are:

```lean
theorem E8.isOptimal :
    SpherePackingConstant 8 = E8.packing.density

theorem Leech.isOptimal :
    SpherePackingConstant 24 = Leech.packing.density
```

The uniqueness statements are deliberately restricted to periodic packings:

```lean
theorem E8.uniqueOptimalPeriodic (P : PeriodicSpherePacking 8)
    (hopt : P.density = SpherePackingConstant 8) :
    P.toSpherePacking.IsSimilar E8.packing.toSpherePacking

theorem Leech.uniqueOptimalPeriodic (P : PeriodicSpherePacking 24)
    (hopt : P.density = SpherePackingConstant 24) :
    P.toSpherePacking.IsSimilar Leech.packing.toSpherePacking
```

This is the correct scope.  With upper density defined by a limsup, deleting or changing finitely
many spheres does not change density, so uniqueness among **all** packings is false without a much
stronger equivalence relation.  Viazovska's paper states that the E8 packing is the unique periodic
packing of maximal density, and the 24-dimensional paper proves the analogous result for Leech.
The 2023 quantitative stability paper restates both exact periodic uniqueness theorems before
proving near-equality results.

The roadmap also supplies lattice-packing uniqueness as a corollary.  Quantitative stability,
universal optimality, and interpolation formulas are related but larger projects; they are listed
in `UPSTREAM.md` as candidate TauCeti roadmaps rather than silently folded into this one.

## Where the uniqueness work belongs

The equality case naturally splits across repositories.

| Result | Natural home | Reason |
|---|---|---|
| Equality in the periodic Cohn–Elkies sum forces all pairwise differences onto the magic-function zero shells | Sphere-Packing/SphereCeti | It depends on packing density, finite periodic patterns, and the specific certificate |
| The translated center set generates a full even integral lattice, and optimal density forces the packing to equal one coset of it | Sphere-Packing/SphereCeti | This is the geometric rigidity step from a packing to a lattice |
| Every positive-definite even unimodular rank-eight integral lattice is isometric to E8 | TauCeti IntegralLattices extension | Pure integral-lattice classification, independent of sphere packing |
| Every rootless positive-definite even unimodular rank-24 integral lattice is isometric to Leech | TauCeti IntegralLattices/Niemeier extension | Niemeier classification, with Leech isolated as the unique empty-root case |
| Universal optimality, Fourier interpolation, and quantitative stability | Separate TauCeti roadmaps | They require energy, interpolation, and quantitative metric infrastructure beyond packing density |

The most economical exact-uniqueness route is the one isolated by Cohn–Elkies, Section 8.  It
does **not** require a full abstract classification of equality cases for arbitrary linear-programming
bounds.  In dimensions 8 and 24, strict direct-side signs put every nonzero center difference at a
squared norm occurring in the candidate even unimodular lattice.  After translating one center to
zero, polarization makes the subgroup generated by all centers an even integral full-rank lattice
`L`.

The decisive step is a **covolume/index squeeze**, not the unsupported assertion that evenness alone
makes `L` a valid superpacking at the Leech separation.  The original period lattice lies in `L`,
and its finite center pattern injects into the quotient by the period lattice.  On the other hand,
the Gram determinant of a full integral lattice is a nonzero integer, so `covolume L ≥ 1`.  At the
canonical E8 and Leech normalizations the optimal periodic packing has one center per unit volume.
The quotient count and covolume inequalities therefore become equalities: `covolume L = 1`, every
coset of the period lattice in `L` is occupied, and the periodic center set is exactly one translate
of `L`.  Only then does the original packing separation imply minimum squared norm `2` in dimension
8 or `4` in dimension 24.  The remaining statement is precisely the algebraic E8 or rootless-Leech
classification above.

Fourier structure factors remain part of the general equality theory and are useful checks, but
Cohn–Elkies explicitly note that the uniqueness deduction needs only the exact direct-side root
set, not restrictions on the roots of the Fourier transform.

## Governing principles

1. **Preserve the existing packing semantics.**  The pinned `SpherePacking`,
   `PeriodicSpherePacking`, `balls`, `finiteDensity`, `density`, and packing constants are the
   starting definitions.
2. **Build one common 8+24 library, not two copied proofs.**  Common structure includes lattices,
   Poisson summation, Cohn–Elkies certificates, theta series, radial Schwartz Fourier eigenspaces,
   equality conditions, and periodic rigidity.
3. **Do not force unlike dimension-specific modular formulas into a typeclass.**  Explicit data
   records passed to common constructors are acceptable; a global `MagicDimension` instance is
   not.
4. **Use TauCeti's lattice layers rather than creating duplicate predicates.**  TauCeti supplies
   both the rational integral-lattice theory and the real `ZLattice` duality, integrality, and
   shell theory; SphereCeti develops only the comparison of its explicit presentations with them.
5. **Pin every hidden normalization.**  Fourier sign, Haar measure, theta exponent, q parameter,
   separation versus sphere radius, covolume, and modular slash conventions are permanent API
   decisions.
6. **Separate inequality from equality.**  An optimal density theorem needs weak sign conditions;
   periodic uniqueness additionally needs exact zero sets and a termwise equality analysis of the
   Poisson bound.
7. **Keep geometric density in `ℝ≥0∞`.**  Add coercion lemmas for finite expressions rather than
   replacing the measure-theoretic definition by a real-valued surrogate.
8. **Every production PR starts from current `main`.**  The historical `gauss2` branch and PR #420
   are sources of proofs to adapt, not branch bases or architectural specifications.
9. **Automation attributes are part of the public API.**  `@[simp]`, `@[grind]`, and `@[fun_prop]`
   additions require small `example`s that check the intended behavior.
10. **Generic local work is stated in the form intended for upstream from the beginning.**  The
    issue-ready destination is recorded in `UPSTREAM.md`, even when waiting would block SphereCeti
    and a local proof is temporarily necessary.

## Existing material to preserve and use

### From Sphere-Packing-Lean `main`

Migrate the following mathematics without gratuitous rewrites.

- The basic packing structures and limsup density definitions.
- Positive scaling and scale-invariance of density.
- The periodic packing action, orbit representatives, covolume density calculation, and periodic
  approximation theorem.
- The coordinate and matrix descriptions of E8, its integral/even structure, minimum norm,
  Euclidean lattice instances, basis, packing, and density.
- `Function.IsRadial` and `RadialSchwartzMap`, including the restricted Fourier transform,
  involution, and self/skew-adjoint decomposition.
- The Jacobi theta, Eisenstein, discriminant, q-expansion, Serre derivative, and imaginary-axis
  developments.
- The explicit E8 auxiliary functions `a`, `b`, and `g`, contour transformations, decay estimates,
  special values, and sign proofs.

Required cleanup:

- separate test imports from the public root aggregator;
- consolidate `numReps`/`numReps'` into one orbit-count definition with its lemmas;
- remove global heterogeneous `NNReal`/`ENNReal` arithmetic instances;
- remove `@[simp]` from the large basis-free periodic density expansion;
- replace duplicate Fourier involution arguments in `a/Eigenfunction` and `b/Eigenfunction` by the
  radial Schwartz lemmas;
- retire the temporary Cohn–Elkies prerequisites file once its uses rely on TauCeti's Poisson
  summation;
- extract generic q-series and analytic lemmas from the E8-specific files.

### From the `gauss2` branch

Adapt proofs from this branch, with exact source attribution:

- the completed E8 main theorem;
- the final normalization of the magic function;
- real-valuedness and Fourier-eigenfunction assembly;
- exact sign and zero deductions;
- the contour argument in the wedge under the inversion `z ↦ -1/z`;
- the more developed Fourier permutation proof for the integral pieces.

Do not wholesale merge or rebase the branch.  Port one coherent theorem or body of supporting
lemmas at a time onto the upgraded production `main`.

### From PR #420

TauCeti now supplies Schwartz lattice summability, dual lattices, Poisson summation, and the
basis-independent covolume statements, so those parts of this PR are not ported.  Adapt from it
only the general periodic Cohn–Elkies counting.

### From the pinned TauCeti snapshot

SphereCeti must directly import and use the following coherent bodies of definitions and lemmas.

#### Integral lattices

- `TauCeti.IntegralLattice` and Gram-matrix constructors;
- integral norm and form;
- evenness and basis/Gram criteria;
- dual carriers and discriminant groups;
- unimodularity and determinant criteria;
- isometries and signature/positive-definiteness;
- standard-coordinate Gram-lattice formulas.

TauCeti's integral lattice lives in a finite-dimensional rational ambient vector space.  The
existing Sphere-Packing lattice lives as a discrete full-rank `ℤ`-submodule of a real Euclidean
space.  SphereCeti therefore introduces an explicit `IntegralPresentation` consisting of a
`ℤ`-basis and integer Gram matrix.  It produces a TauCeti integral lattice while recording the
comparison with the real lattice.  This bridge is central; defining another unrelated notion of
“integral real lattice” would create two permanently incompatible notions.

#### Real lattices, Poisson summation, and theta series

TauCeti also develops the real side, in the `ZLattice` namespace, and SphereCeti uses it rather
than a local copy:

- the inner-product dual `ZLattice.dual`, identified with Mathlib's
  `LinearMap.BilinForm.dualSubmodule` by `ZLattice.dual_def`, with its discreteness and full-rank
  instances, `ZLattice.dual_dual`, and `ZLattice.covolume_dual`;
- the predicates `ZLattice.IsIntegral`, `ZLattice.IsEven`, and `ZLattice.IsUnimodular`, the
  determinant `ZLattice.det`, `ZLattice.covolume_sq_eq_det_gram`, and
  `ZLattice.IsIntegral.isUnimodular_iff_covolume_eq_one`;
- shells `ZLattice.shell`, their finiteness `ZLattice.finite_shell`, and representation numbers
  `ZLattice.representationNumber`;
- Poisson summation over a full lattice, `SchwartzMap.tsum_eq_tsum_dual_fourier`, with the
  reflected and even-function forms `SchwartzMap.tsum_eq_tsum_dual_fourier_neg` and
  `SchwartzMap.tsum_eq_tsum_dual_fourier_of_even`, and the summability of both sides,
  `ZLattice.summable_poisson_left` and `ZLattice.summable_poisson_right`;
- the theta series `ZLattice.thetaSeries` and coset theta series `ZLattice.thetaCoset`, their
  convergence and holomorphy, their q-expansions with representation-number coefficients
  (`ZLattice.IsEven.qExpansion_thetaSeries_coeff`), and the translation law
  `ZLattice.IsEven.thetaSeries_slash_T`.

#### E8, the Golay code, and the Leech lattice

- `TauCeti.IntegralLattice.typeE₈RootLattice`, its evenness, positive-definiteness, and
  determinant, and the explicit enumeration of its roots `typeE₈RootEquiv : Fin 240 ≃ _` with
  `kissingNumber_typeE₈RootLattice`;
- the extended binary Golay code `TauCeti.BinaryGolay.code` in the coordinates of its systematic
  generator, with `finrank_code`, `natCard_code`, `isSelfDual_code`, `isDoublyEven_code`,
  `eight_le_hammingNorm`, and `weightEnumerator_code`;
- Construction B and the Leech lattice `TauCeti.leechLattice`, with `isEven_leechLattice`,
  `isUnimodular_leechLattice`, `isPosDef_leechLattice`, `finrank_leechLattice`, the congruence model
  `mem_leechLattice_carrier_iff_exists`, `minimum_leechLattice`, and the absence of roots
  `vectorsOfNorm_two_leechLattice`;
- the minimum, kissing number, and representation numbers of a positive-definite integral lattice,
  `IntegralLattice.minimum`, `IntegralLattice.kissingNumber`, and
  `IntegralLattice.representationNumber`.

#### Modular forms

- the graded-ring isomorphism `TauCeti.ModularForm.mvPolynomialEquivModularForms` between
  `ℂ[E₄, E₆]` and the level-one modular forms, which turns the theta identities of Layer 5 into
  coefficient comparisons once the theta series is known to be a modular form.

#### Still pending upstream

These remain dependencies rather than results available to SphereCeti:

- the theta `S`-transformation and the theta series of an even unimodular lattice as a level-one
  modular form (Layers 3–8 of the TauCeti ThetaSeries roadmap);
- the comparison between a real integral lattice and its rational model (TauCeti PR #20950,
  `ratModel`, open), which SphereCeti's `IntegralPresentation` is designed to interoperate with
  rather than replace;
- the classification of positive-definite even unimodular lattices of rank 8;
- the classification of rootless positive-definite even unimodular lattices of rank 24;
- the kissing number `196560` of the Leech lattice.

The following table records, for each area, what TauCeti supplies at the pin and what SphereCeti
must still prove.

| Area | Available at the pin | Remaining SphereCeti obligation |
|---|---|---|
| Real/rational bridge (Layer 2) | `ZLattice` duality, integrality, determinant, shells | Compare an `IntegralPresentation` with these predicates and with TauCeti's dual carrier |
| Poisson summation (Layer 4) | `SchwartzMap.tsum_eq_tsum_dual_fourier` and its variants | The finite-orbit periodic identity and the Cohn–Elkies theory |
| Theta series (Layer 5) | Definitions, holomorphy, q-expansions, `T`-translation | Nothing beyond the presentation bridges; the `S`-law and modularity are pending upstream |
| E8 (Layer 6) | `typeE₈RootLattice` and its 240 roots | A Gram-preserving isometry from the production E8 presentation |
| Leech (Layer 6) | `leechLattice`, minimum `4`, no roots, the Golay code | The transported Euclidean lattice, its covolume and shells, and the secondary comparisons |
| Classification (Layer 10) | Neither rank-8 nor rootless rank-24 uniqueness | Retained as required dependencies |

#### Complex and modular analysis

- `TauCeti.Contour.circleIntegral_eq_zero_of_meromorphicOrderAt_nonneg` for closed circles;
- the generic `UpperHalfPlane.resToImagAxis` definition, its lemmas, and its modular
  `S`-transformation;
- q-coefficient vanishing versus cusp-function Big-O estimates;
- the generic function and logarithmic-derivative `S`-transformation;
- finite-index Sturm bounds when a congruence-level identity genuinely requires them;
- the small Fourier-continuity lemma.

These do not replace Sphere-Packing's half-infinite rectangular contour deformation or the
specialized convex-wedge argument under `z ↦ -1/z`.  Closed circles, unbounded rectangles, and
finite path homotopies solve different problems.

## Permanent mathematical conventions

The fuller record is in [`CONVENTIONS.md`](CONVENTIONS.md).  The central choices are:

### Ambient Euclidean space

```lean
abbrev V (d : ℕ) := EuclideanSpace ℝ (Fin d)
```

### Separation and radius

A `SpherePacking` stores center separation `r`; its balls have radius `r / 2`.

- E8 is normalized to separation `√2`, hence ball radius `√2 / 2`.
- Leech is normalized to separation `2`, hence unit balls.

Uniqueness at the scale-free packing constant is stated using positive similarity.  Fixed-radius
intermediate theorems use congruence.

### Fourier transform

Use Mathlib's real inner-product Fourier transform with kernel

```math
  e^{-2\pi i\langle x,\xi\rangle}.
```

Every Gaussian, Poisson, dual-lattice, and theta transformation theorem must be tested against this
normalization.

### Theta series

```text
Theta_Λ(τ) = Σ_{x∈Λ} exp(π i τ ‖x‖²).
```

For even lattices, the modular q parameter is

```text
q = exp(2π i τ),
```

and coefficient `n` counts vectors with squared norm `2n`.

Thus:

- E8 root count is coefficient `1`, equal to `240`;
- Leech has coefficient `1 = 0` and coefficient `2 = 196560`.

### Congruence and similarity

`SpherePacking.map` transports centers by a real affine isometry and preserves separation.
Basepoint-independent density, proved by comparing translated balls, supplies the nontrivial
translation step in density invariance.  `IsCongruent` is equality after such a transport;
`IsSimilar` permits one positive scaling before congruence.  Both relations have reflexivity,
symmetry, and transitivity lemmas, and positive density supplies the center used by rigidity.

### Attributes

Good `@[simp]` declarations are canonical projections and evaluations:

- scaling centers/separation/density;
- `ofZLattice` centers, lattice, and separation;
- shell membership;
- norm-squared profile evaluation;
- coercions of radial Schwartz Fourier transforms.

Large semantic transformations are explicit, not simp rules:

- Poisson summation;
- the Cohn–Elkies bound;
- periodic density expansion;
- theta `S`-transformation;
- theta classification identities;
- contour deformations.

Good `@[grind]` rules are directional structural facts:

- distinct centers imply separation;
- period-lattice action closure;
- orbit representative uniqueness;
- minimum-norm elimination;
- codeword parity and coordinate congruences.

`@[fun_prop]` remains appropriate for TauCeti's imaginary-axis realness/positivity,
differentiability, and algebraic closure properties.

# Roadmap layers

## Layer 0 — synchronized toolchain migration and direct imports

**Goal:** move production `Sphere-Packing-Lean/main` from Lean/Mathlib `v4.32.0` to the exact
4.36/TauCeti dependency graph of SphereCeti, with no mathematical redesign in the same PR.

Deliverables:

1. bump `lean-toolchain` to `v4.36.0-rc1`;
2. pin TauCeti to `271e1af4dd54c50b9192cf3e213b7686843a0b3a`;
3. resolve Mathlib to `2cabef97b63d3275776b8b060d802de6a6fa1055`;
4. repair source incompatibilities without opportunistic refactors;
5. add [checks of required declarations and Fourier conventions](CONVENTIONS.md#declaration-and-convention-checks):
   preserve the expected types, Fourier sign, measure, and normalization constants;
6. add Sphere-Packing as a direct SphereCeti dependency;
7. delete `SphereCeti.Pinned` and rewrite `Suggested.lean` imports against production declarations.

This is the only layer in which the compatibility model is tolerated.

## Layer 1 — packing API preservation and import hygiene

**Goal:** stabilize the public definitions and basic lemmas about packings before adding new
mathematics.

Deliverables:

- preserve the pinned structures and density definitions;
- split production and test aggregators;
- add directional separation and lattice-action lemmas;
- mark safe scale projections and scale density as `@[simp]`;
- add `density_le_constant` lemmas;
- define congruence and similarity;
- preserve public names with compatibility aliases during migrations.

Acceptance tests:

- the E8 packing and density proofs compile;
- `simp` normalizes constructor projections without expanding density formulas;
- `grind` closes basic separation/action residue but does not invoke analysis.

## Layer 2 — one real/algebraic lattice bridge

**Goal:** make TauCeti's rational integral-lattice library and its real `ZLattice` theory two views
of the same concrete lattice data.

TauCeti supplies the real side: the dual `ZLattice.dual`, the predicates `ZLattice.IsIntegral`,
`ZLattice.IsEven`, and `ZLattice.IsUnimodular`, shells and representation numbers, the
Gram-determinant formula `ZLattice.covolume_sq_eq_det_gram`, and the unimodular/covolume-one
criterion.  This layer adds only the comparison of an explicit presentation with that theory.

Deliverables:

- `EuclideanLattice.IntegralPresentation`;
- construction of the TauCeti `ofGramMatrix` lattice;
- Gram compatibility with the real inner product;
- integral equivalences between the real carrier/dual and TauCeti's carrier/dual carrier;
- an explicit real-dual membership theorem in TauCeti dual-carrier coordinates;
- the discriminant of the presentation lattice as the squared real covolume, and unimodularity of
  the presentation as covolume one;
- evenness and unimodularity of a presentation as the real predicates `ZLattice.IsEven` and
  `ZLattice.IsUnimodular`;
- minimum-norm predicates, and shell equivalences between `ZLattice.shell` and TauCeti's
  `vectorsOfNorm`, transporting rootlessness;
- extension of a TauCeti classification isometry to a real linear isometry, then to an affine
  isometry carrying one lattice coset to another.

Do not introduce another integrality predicate on real lattices: TauCeti's `ZLattice.IsIntegral`
is the one.  Positive-definiteness is derived from the full Euclidean presentation rather than
carried as a separate hypothesis.  The E8 and Leech reference objects and classifications remain in
their dimension-specific layers.

TauCeti PR #20950 (open) proposes `ratModel`, the rational model of a real integral lattice, and
several invariant comparisons.  When it lands, `IntegralPresentation` is connected to it by a
comparison theorem; the explicit basis-and-Gram data remain, since the E8 and Leech arguments need
concrete coordinates, but no competing abstract real-to-rational conversion is introduced.

## Layer 3 — periodic orbits and the density formula

**Goal:** replace implementation-dependent representative choices by the canonical orbit
quotient of the production action.

Deliverables:

- `PeriodicSpherePacking.ofZLattice`;
- the existing finite quotient `Quotient P.addAction.orbitRel`, exposed as `P.Orbit`, with the
  chosen representative `P.orbitRep` (through `Quotient.out`); every statement using it is
  independent of the choice at dual frequencies.  Production's basis-relative fundamental-domain
  representatives realize the same quotient through `addActionOrbitRelEquiv'`, and no separate
  pattern structure exists;
- `P.numOrbits = Fintype.card P.Orbit`;
- the canonical center intensity
  `P.centerIntensity = P.numOrbits / ZLattice.covolume P.lattice`;
- basis-free density formula

```math
  \operatorname{density}(P)
  = \operatorname{numOrbits}(P)\,
    \operatorname{vol}(B(0,r/2))/\operatorname{covol}(\Lambda);
```

- translated coordinate boxes and their finite center patterns;
- a Fubini/Følner averaging theorem that finds an arbitrarily large translated box whose
  normalized center count approximates a high finite-density ball;
- guarded repetition of those translated finite patterns, with explicit center/separation
  equations;
- exact periodicized density and fixed-width boundary-layer volume decay;
- `ε`-approximation of every packing density by a periodic packing density;
- `PeriodicSpherePackingConstant d = SpherePackingConstant d` as the resulting corollary.

The large density formula must not be a simp lemma.

## Layer 4 — Poisson summation and Cohn–Elkies

**Goal:** isolate the linear-programming theorem from the dimension-specific magic functions.

Poisson summation is imported, not developed here.  TauCeti's
`SchwartzMap.tsum_eq_tsum_dual_fourier` is the theorem of record:

```math
  \sum_{\ell\in\Lambda} f(v+\ell)
  = \frac{1}{\operatorname{covol}(\Lambda)}
    \sum_{m\in\Lambda^\vee} \widehat f(m)\, e^{2\pi i\langle v,m\rangle},
```

with exactly the positive phase and inverse-covolume factor that the Cohn–Elkies bound needs.  The
dual `ZLattice.dual` carries its own discreteness and full-rank instances, and TauCeti proves
`ZLattice.dual_dual`, `ZLattice.covolume_dual`, and the summability of both sides,
`ZLattice.summable_poisson_left` and `ZLattice.summable_poisson_right`.

Deliverables:

- a unit-Gaussian normalization test and the exact finite-pattern squared-amplitude formula;
- `CohnElkies.Certificate d r`, with no radiality requirement;
- certificate bound and scaling lemmas;
- `Certificate.ofRadial`, the constructor of a certificate from a radial function;
- unrestricted sphere-packing bound;
- lattice sharpness relation;
- complex periodic structure amplitude and its nonnegative real squared-norm structure factor;
- exact nonnegative direct and Fourier defects in `ℝ`;
- equality implies pattern-independent termwise sharpness;
- sharpness plus `0 < P.numOrbits` implies equality;
- positivity of `C.f 0` and `C.bound`.

The periodic equality theorem is essential for uniqueness.  The Fourier-side condition is not simply
“`f̂` vanishes on every nonzero dual vector”: for a multi-coset periodic configuration, a nonzero
structure factor may also vanish.  This distinction must be represented explicitly.
At a dual frequency, the phase is invariant under changing a representative by a period; the
amplitude therefore descends to the canonical orbit quotient.
The two equality directions remain separate: an empty packing has vacuous termwise conditions but
zero density, whereas every certificate bound is positive.

## Layer 5 — theta series, taken from the TauCeti ThetaSeries roadmap

**Goal:** use the general theory of lattice theta series, keeping in SphereCeti only the
comparison with integral presentations and the consequences for the candidate lattices.

The general theory belongs to the TauCeti ThetaSeries roadmap, and part of it has landed: the
theta series `ZLattice.thetaSeries` and coset theta series, their convergence and holomorphy,
their q-expansions with representation-number coefficients, the decomposition over a sublattice,
and the `T`-translation law.  SphereCeti imports these.  The `S`-transformation
`thetaSeries_neg_inv`, the theta series of an even unimodular lattice as a level-one modular form
`thetaForm`, and the identities in ranks 8 and 24 have not landed.  SphereCeti states only those
pending targets, in the form of that roadmap and over TauCeti's implemented definitions; they are
deleted and replaced by imports when TauCeti provides them, and they are not to be developed into a
second general theory.

Deliverables:

- provisional local statements of the pending `ThetaSeries` targets: `thetaSeries_neg_inv`,
  `thetaForm` with its coercion and q-expansion coefficients, and the rank-8, rank-24, and rootless
  identities;
- the presentation bridges: an even (respectively unimodular) integral presentation makes the
  real lattice `ZLattice.IsEven` (`ZLattice.IsUnimodular`), and the root count is the
  representation number `ZLattice.representationNumber Λ 2`;
- the E8/Leech-facing corollaries through the bridges:

```math
  \Theta_\Lambda = E_4, \qquad
  \Theta_\Lambda = E_4^3 + (N_2(\Lambda)-720)\Delta, \qquad
  \Theta_\Lambda = E_4^3-720\Delta \text{ (rootless)}.
```

The theta theory is not merely decorative.  It checks all lattice normalizations, gives shell
cardinalities, and supplies the modular classification used in the E8/Leech infrastructure.  It is
not, however, on the path to the optimality theorems: those need only an explicit lattice, its
minimum and covolume, and a sharp Cohn–Elkies certificate (Layers 4, 6, and 9).  The rank-8 theta
identity remains an input to E8 periodic uniqueness, through the rank-8 classification of Layer 10.

## Layer 6 — E8 and Leech lattice packages

### E8

The canonical algebraic object is TauCeti's `IntegralLattice.typeE₈RootLattice`, the Gram lattice
of the E8 Cartan matrix in simple-root coordinates.  Retain the existing production coordinate and
basis descriptions, then package:

- an `IntegralPresentation`;
- a Gram-preserving isometry from that presentation to `typeE₈RootLattice`, since the two use
  different bases rather than a common coordinate system;
- positive-definiteness, evenness, and unimodularity;
- minimum squared norm `2`;
- root count `240`, transported through the isometry from TauCeti's explicit enumeration
  `typeE₈RootEquiv` and `kissingNumber_typeE₈RootLattice`;
- valid ADE component indices for the root-system classification;
- canonical lattice packing and density;
- theta identity.

The direct minimum-norm proof and the root count are independent of the theta identity.

### Leech

The canonical algebraic object is TauCeti's `leechLattice`: the integral lattice in `ℚ^24` obtained
by adjoining the odd shift `(-3/2, 1/2, …, 1/2)` to the Construction B lattice of TauCeti's Golay
code, in coordinates `x = a / 2` with the form

```math
  B(x,y) = \tfrac12 \sum_{i=1}^{24} x_i y_i .
```

TauCeti proves that it is even, unimodular, and positive definite, characterizes its carrier by
congruence conditions on `a`, and proves minimum `4` and the absence of roots.  SphereCeti does not
construct a second Leech lattice.  The Euclidean Leech lattice used for packings is the image of
`leechLattice` under

```math
  T : \mathbb Q^{24} \to \mathbb R^{24}, \qquad T(x) = x / \sqrt 2,
```

which satisfies `⟪T x, T y⟫ = B(x, y)` and `T(a / 2) = a / √8`.  `T` is an isometric embedding of
the rational lattice, not a real-linear equivalence between `ℚ^24` and `ℝ^24`.

Required results:

- discreteness and full rank of the transported lattice, and covolume one;
- transport of the inner product, of every norm shell, and of the minimum, so that the minimum
  squared norm is `4` and there are no roots;
- an integral presentation and an isometry to `leechLattice`, hence evenness and unimodularity;
- unit-ball packing density `π^12 / 12!`.

Secondary comparisons, which are not prerequisites for optimality:

- the residue-class coordinate description: `x / √8` with `x` integral lies in the lattice exactly
  when the coordinate sum satisfies the modulo-eight condition and, for every residue `r` modulo
  four, the word of coordinates congruent to `r` lies in TauCeti's code;
- the code generated by the parity extension of the first twelve shifts of
  `1 + X + X^5 + X^6 + X^7 + X^9 + X^11` equals TauCeti's code after a coordinate permutation, its
  transcription checked by a unitriangular row-reduction certificate and exact row weights;
- the 24 published integer basis rows, divided by `√8`, span the lattice after a coordinate
  permutation, and their integer matrix has determinant `8^12`.

The published rows are in the octad coordinates of a third realization of the Golay code: eleven of
them fail the residue-class condition for the cyclic code, and also for TauCeti's code, without a
permutation.  None of these descriptions may be identified with another by definition.

Algebraic structure beyond optimality:

- kissing number `leechLattice.kissingNumber = 196560`, with the corollary that the real shell of
  squared norm `4` has `196560` vectors;
- theta identity.

The naive unshifted Construction-A lattice of the extended binary Golay code must not be called the
Leech lattice.

## Layer 7 — radial profiles, parametric integration, and signed kernels

**Goal:** extract the genuinely common analytic pattern without hiding dimension-specific formulas.

Common definitions and lemmas:

- squared-norm radial profile constructor;
- restricted radial Schwartz Fourier transform;
- `+1` and `-1` eigenspace operations;
- Gaussian/Laplace kernel integrability and the complex-parameter Gaussian Fourier transform;
- Fubini/Tonelli interchange between the ambient space and a contour parameter;
- differentiation under parameterized integrals and smoothness of iterated-derivative families;
- the inversion change of variables between `(0,1]` and `[1,∞)`;
- exact local zero orders through nonvanishing cofactors;
- q-expansion Big-O estimates for cusp decay.

The concrete `+1` and `-1` components expose their exact signed kernel transformation laws, and
Layer 8 uses those laws directly.  No structure packaging kernel data, no component left as
`sorry` without a defining formula, and no free complex `eigenvalue` field is among the targets:
the finite Fourier sign occurs in the transformation law that determines it.

## Layer 8 — contour deformation for the magic-function integrals

**Goal:** provide the contour-deformation identities used to evaluate the magic-function contour
integrals, stated once for a single pair of kernels.

All required finite deformations use straight segments and their images under the inversion
`z ↦ -1/z`; all required unbounded deformations use half-infinite axis-aligned rectangles.  The
images of the left and right legs under `z ↦ -1/z` are circular arcs, but they occur only inside
proofs; no circular-arc contour is a target.  Each kind of deformation is proved in exactly one
place:

- unbounded vertical deformations use this layer's theorems on half-infinite rectangles;
- finite deformations under `z ↦ -1/z` use this layer's results on the wedge, which rely on
  Mathlib's Poincaré lemma for curve integrals: integrals of a closed one-form are invariant
  under homotopy.  For a one-form `F dz`, holomorphy of `F`, together with continuity up to the
  closure, supplies the closedness hypotheses used here.

The layer has two independent main results, one for each kind of deformation.

### Unbounded branch: half-infinite rectangles

- boundary vanishing on a bounded rectangle, taken from Mathlib's rectangular
  Cauchy–Goursat theorem;
- deformation of a horizontal edge into the two vertical half-lines above its endpoints, with
  explicit integrability hypotheses on the half-lines and the top edge controlled either by
  uniform decay or by convergence of the top-edge integrals to zero.

These identities feed the vertical-line rewrites, Laplace representations, and double-zero
arguments of Layer 9.

### Finite branch: curve integrals and the wedge

- the scalar one-form of a function `F : ℂ → ℂ`, with the bridge between interval integrals over
  a parametrized segment and Mathlib curve integrals;
- change of variables along a segment, carrying a genuine derivative (chain-rule) hypothesis for
  the substitution;
- a closedness predicate for one-forms combining, in one structure, the two hypotheses of
  Mathlib's curve-integral Poincaré lemma (differentiability-with-closure-continuity and symmetry
  of the within-derivative), together with the lemma that holomorphy with closure continuity
  implies closedness of the scalar one-form (the converse is not a target);
- the inversion `z ↦ -1/z`, its derivative, and its action on the upper half-plane;
- the wedge `{z : 0 < Im z, |Re z - 1| < Im z}`: openness, convexity, and the fact that its
  closure meets the real axis only at `1`;
- the two signed contour-permutation theorems, stated for a single pair `Ψ, Ψ' : ℂ → ℂ`
  satisfying the signed transformation law under `z ↦ -1/z`, with the one-form `Ψ' dz` closed on
  the wedge: the sum of the integrals of `Ψ dz` over the left legs `[-1, -1+i]` and `[-1+i, i]`
  equals the correspondingly signed sum of the integrals of `Ψ' dz` over the right legs
  `[1, 1+i]` and `[1+i, i]`.

Intermediate wedge homotopies are proof devices, not public targets.  Radial families are
special cases of the single-pair statements; they are not part of the generic statements.

### Closing deliverable: the generic component Fourier identities and assembly

The magic contour has six pieces: the left legs `-1 → -1+i → i`, the right legs `1 → 1+i → i`,
the central segment `0 → i`, and the vertical ray from `i` towards `i∞`.  Three theorems compute
their Fourier behavior in even dimension `2k` from explicit hypotheses:

- the **left/right identity**: absolute product integrability, continuity of the
  Gaussian-transformed source kernel on the left legs, the signed inversion law (independent of
  the radial variable `r`)
  `(i/z)^k g(z) = ± z⁻² g'(-1/z)` on the upper half-plane, and closedness of the transported
  kernel's one-form on the wedge give the transform of the left-leg component as the signed
  right-leg component of `g'`;
- the **central-pair identity**: the inversion `z ↦ -1/z` carries the central segment directly onto
  the vertical ray, with explicit integrability on both sides and no wedge homotopy;
- the **six-piece assembly**: with each piece integrable and the piecewise identities exchanging
  left with right and central with ray at a common sign, the assembled component is a Fourier
  eigenfunction with that sign.

Each E8 and Leech component of Layer 9 comes with a theorem, its **defining formula**,
identifying it with the six-piece assembly of its four named kernels, so the identities above
apply to it directly.  In `Suggested.lean` each component is built from a radial profile whose
body is `sorry`, so the defining formula is what determines it.  No structure packaging kernel
data appears among the targets, and no component lacks a defining formula.

## Layer 9 — E8 and Leech magic functions

For each dimension, prove:

- radial Schwartz `+1` and `-1` Fourier eigencomponents;
- the final auxiliary function as the published dimension-specific linear combination of those
  components;
- real-valuedness of the function and Fourier transform;
- the two component Fourier eigenfunction identities and the resulting, generally distinct,
  Fourier transform of the final auxiliary function;
- normalization at zero;
- direct-side nonpositivity beyond the threshold;
- Fourier-side nonnegativity;
- separate exact direct- and Fourier-side zero sets, including absence of extraneous zeros;
- exact local zero orders through nonvanishing cofactors, which imply reusable quantitative lower
  bounds near every shell;
- separate strict direct- and Fourier-side signs away from the shell zeros;
- the Cohn–Elkies certificate, packaged as a structure, with `certificate.f = magic`;
- candidate-lattice sharpness and equality of the bound with the candidate lattice density.

The exact zero set is itself a required result.  Density optimality only needs weak inequalities,
but periodic uniqueness needs to infer that every nonzero pairwise difference lies on an E8 or Leech
shell.

So that the stability roadmaps recorded in `UPSTREAM.md` can reuse the hard analytic work,
preserve multiplicity and quantitative lower-bound information rather than proving only
`f x = 0` statements and discarding the stronger estimates.

## Layer 10 — equality and rigidity

**Goal:** formalize the equality case of the linear-programming argument, not just the numerical
bound.

### Common equality argument

Given an optimal periodic packing and a fundamental pattern:

1. the periodic Cohn–Elkies inequality is an equality;
2. every direct-side summand with strict negative sign must vanish;
3. every nonzero periodic difference lies in the exact shell zero set;
4. Fourier-side terms satisfy the `f̂`/structure-factor alternative;
5. after translating one center to zero, polarization turns the even squared-distance spectrum
   into integral inner products;
6. the period lattice is contained in the generated subgroup, so the latter is a full even integral
   Euclidean lattice; the canonical center-orbit quotient then embeds into the finite relative
   quotient of the generated lattice by the period lattice;
7. the integral Gram determinant gives `covolume ≥ 1`, while the canonical center density and the
   quotient count give `covolume ≤ 1`; hence the generated lattice is unimodular, every quotient
   coset is occupied, and the original center set is exactly one lattice coset;
8. the original separation now supplies minimum squared norm `2` for E8 or `4` for Leech.

This is the formal counterpart of Cohn–Elkies, Lemma 8.2 and the argument immediately following
it.  Expose the covolume/discriminant bridge and quotient-cardinality argument through
reusable intermediate theorems, not hidden in two enormous proofs of the main theorems.
The quotient cardinal inequality is stated only after discreteness and full rank of the generated
lattice, together with its containing the period lattice, have made the relative quotient finite.
Full rank alone does not suffice (`ℤ` and `√2 ℤ` in `ℝ`), and Mathlib's `relIndex` is zero at
infinite index.

### E8 rigidity

The E8 shell spectrum gives a positive-definite even unimodular rank-eight lattice.  Use the
classification theorem that such a lattice is isometric to E8, then transport the center coset to
obtain periodic congruence.

The classification theorem is general integral-lattice mathematics.  In this roadmap it is a
required dependency stated as an assumed theorem, that is, an unproved roadmap target on which the
uniqueness proof relies.  Its intended home is an extension of the TauCeti Integral Lattices
roadmap, recorded in `UPSTREAM.md`.  If TauCeti has not provided it when the production
uniqueness proof needs it, the production development proves it locally, with exactly the intended
statement, and replaces the local proof by an import once TauCeti provides the result.  Acceptance
upstream is never a prerequisite.

The intended proof of the classification (PR M1 in `MIGRATION.md`) obtains the 240 roots of an
arbitrary positive-definite even unimodular rank-eight lattice from the rank-8 theta identity.
TauCeti's enumeration of the roots of `typeE₈RootLattice` does not supply that count, which concerns
one specific lattice, so E8 periodic uniqueness keeps its dependency on the pending theta theory even
though the optimality theorem does not have it.

### Leech rigidity

The Leech shell spectrum gives a rootless positive-definite even unimodular rank-24 lattice.  Use the
uniqueness characterization of Leech and transport the center coset.

The rank-24 dependency is uniqueness of the rootless even unimodular lattice of rank 24, again an
assumed theorem: an unproved roadmap target on which the uniqueness proof relies.  Its intended
home is an extension of the TauCeti Integral Lattices roadmap proving that Niemeier's list is
complete: that roadmap defines the twenty-four Niemeier lattices but does not prove completeness,
so the statement remains a required dependency here, recorded in `UPSTREAM.md`.  SphereCeti uses
only the uniqueness statement and does not restate the list of Niemeier lattices or the case
analysis.  If TauCeti has not provided it when the production uniqueness proof needs it, the
production development proves it locally, with exactly the intended statement, and replaces the
local proof by an import once TauCeti provides the result.

## Layer 11 — assembly of the main theorems

Assemble:

- periodic equals unrestricted packing constant;
- E8 lower bound from its packing;
- E8 upper bound from its certificate;
- Leech lower bound from its packing;
- Leech upper bound from its certificate;
- numerical constant formulas;
- E8 unique optimal periodic packing;
- Leech unique optimal periodic packing;
- lattice uniqueness corollaries.

The main-theorem files contain only imports, two inequalities, `le_antisymm`, and the
equality-case theorem.  Analytic or lattice classification work in a main-theorem file signals
that a supporting layer is missing.

# Uniqueness, universal optimality, and stability

The roadmap includes **exact periodic uniqueness** because it is a direct equality-case continuation
of the same Cohn–Elkies certificates used for density optimality.

Universal optimality and Fourier interpolation are independent projects and are not dependencies
of the optimality or periodic-uniqueness main theorems.  The roadmap does not attempt to absorb the
following larger theories:

- universal optimality for completely monotone functions of squared distance;
- the E8/Leech radial Fourier interpolation formulas;
- quantitative lattice stability;
- local-frame stability for almost-optimal periodic packings;
- energy minimization for general point configurations.

Those topics need additional general objects: point configurations independent of a chosen sphere
radius, energy per point, admissible potentials, completely monotone functions, interpolation bases,
Hausdorff/local-frame metrics, and quantitative estimates.  They deserve separate TauCeti roadmaps.
SphereCeti must preserve exact zero multiplicities and estimates for reuse by those roadmaps.

# PR discipline

The detailed main-first sequence is in [`MIGRATION.md`](MIGRATION.md).  Every production PR must:

- begin from current `main` unless stacked on one named immediate predecessor;
- change one mathematical topic;
- preserve or reduce `sorry` count;
- record source provenance when adapting proofs from `gauss2` or PR #420;
- include small `example`s that check the intended behavior of new API and automation;
- avoid broad directory moves in the same PR as a hard proof;
- provide compatibility aliases before deleting public names;
- distinguish “copied proof material” from “new target API”.

# Repository files

| File | Role |
|---|---|
| `README.md` | Definitive mathematical roadmap |
| `SphereCetiRoadmap/Suggested.lean` | Proposed target signatures and `#check` confirmations |
| `SphereCetiRoadmap/Pinned.lean` | Temporary model of the older Sphere-Packing public API |
| `CONVENTIONS.md` | Permanent normalization and attribute decisions |
| `MIGRATION.md` | Main-first targeted PR sequence |
| `PROVENANCE.md` | Source and dependency record |
| `UPSTREAM.md` | Issue-ready list of Mathlib/TauCeti upstream candidates |
| `VALIDATION.md` | Static consistency check and Lean-elaboration validation record |
| `scripts/check_roadmap.py` | Deterministic check of pins, links, and required declarations |
| `.github/workflows/ci.yml` | Static consistency check followed by Lean elaboration |
| `lakefile.toml` | Exact TauCeti dependency |
| `lake-manifest.json` | Full resolved pin set |
| `lean-toolchain` | Lean `v4.36.0-rc1` |

# References

Core papers:

- H. Cohn and N. Elkies, *New upper bounds on sphere packings I*, Annals of Mathematics 157
  (2003), 689–714.
- M. Viazovska, *The sphere packing problem in dimension 8*, Annals of Mathematics 185 (2017),
  991–1015.
- H. Cohn, A. Kumar, S. Miller, D. Radchenko, and M. Viazovska,
  *The sphere packing problem in dimension 24*, Annals of Mathematics 185 (2017), 1017–1033.
- H. Cohn and A. Kumar, *Optimality and uniqueness of the Leech lattice among lattices*, Annals of
  Mathematics 170 (2009), 1003–1050.
- H. Cohn, A. Kumar, S. Miller, D. Radchenko, and M. Viazovska,
  *Universal optimality of the E8 and Leech lattices and interpolation formulas*, Annals of
  Mathematics 196 (2022), 983–1082.
- K. J. Böröczky, D. Radchenko, and J. P. G. Ramos,
  *A quantitative stability result for the sphere packing problem in dimensions 8 and 24*, 2023.

Formal sources and sibling projects:

- `thefundamentaltheor3m/Sphere-Packing-Lean` at the pinned production baseline;
- `TauCetiProject/TauCeti` at the exact dependency pin;
- `TauCetiProject/TauCetiRoadmap`, especially the IntegralLattices and ContourIntegration roadmaps;
- Mathlib's `ZLattice`, Schwartz/Fourier, Gaussian, modular-form, q-expansion, and measure-theory
  libraries.

## Infrastructure

**Our infrastructure adapts the work of the TauCeti contributors:**
[TauCeti](https://github.com/TauCetiProject/TauCeti),
[TauCetiRoadmap](https://github.com/TauCetiProject/TauCetiRoadmap),
[TauCetiReview](https://github.com/TauCetiProject/TauCetiReview),
[TauCetiWorker](https://github.com/TauCetiProject/TauCetiWorker),
[TauCetiProgress](https://github.com/TauCetiProject/TauCetiProgress), and
[TauCetiData](https://github.com/TauCetiProject/TauCetiData).
The [infrastructure plan](INFRASTRUCTURE-PLAN.md) records their roles, exact candidate source
snapshots, and the focused PR sequence. Imports retain source attribution and applicable licenses.

### Build boundaries

```bash
lake env python3 -I scripts/check_audits.py
lake build
```

The default build checks both `SphereCeti` (the admission-free scaffold/adapters) and
`SphereCetiRoadmap` (the roadmap target library). This separation does not change the
production proof home. See [module boundaries](docs/infrastructure/module-boundaries.md) for
the source inventory, tests, limitations, and the roadmap integration contract.

The [trusted candidate build](docs/infrastructure/trusted-build.md) adapts TauCeti's pinned
sandbox and configuration attestation. It uses approved tools, builds an immutable PR head,
and reports build and scope separately; all current changes require human review.
[Compiled audits](docs/infrastructure/compiled-audits.md) check every module, transitive axiom
dependencies, lint, and the roadmap admission ledger.

### Project diagnostics

```bash
uv run --locked sphereceti doctor --offline
uv run --locked sphereceti status --json
```

The installed CLI packages project identity, policy, and the upstream source ledger. These
commands report the project's state; worker and automated review/merge capabilities remain disabled.
See [CLI configuration and installation](docs/infrastructure/cli.md).

[Lifecycle maintenance](docs/infrastructure/lifecycle.md) reports main CI health, conflicts,
and quiet work using the shared merge observation. `sphereceti maintenance` previews by default;
label publication is separately policy-gated and disabled. Recommendations never close PRs.

The [TauCetiReview import](tools/review/README.md) preserves its engine, ten ordered rubrics,
and upstream tests. `sphereceti review N --dry-run` verifies the exact proposed PR, selected
context, and dependency sources without invoking a provider. An explicitly configured provider
can produce a [local advisory review](docs/infrastructure/local-review.md).
[Review records](docs/infrastructure/review-records.md) bind that evidence to API-verified
publication identities. `review N --read-records` inspects them without inference; explicit
`--post` requires approved posting policy, which remains disabled. The legacy launchers remain disabled.

The [durable review archive](docs/infrastructure/review-archive.md) keeps completed review
metadata and numeric run facts in a local journal/outbox. `sphereceti archive preview` and
`archive rebuild --output /tmp/reviews.sqlite` are provider-free; remote sync remains disabled.

The [evaluation tools](docs/infrastructure/evaluation.md) summarize recorded costs, apply
explicit dated price snapshots, compare compatible fresh shadow arms, and retain local human
labels. `sphereceti evaluation costs --json` is offline and never invokes a provider.

The [advisory profiler](docs/infrastructure/profiling.md) compares exact Git revisions using
the trusted-build sandbox and host CPU/wall-time measurements. `sphereceti profile-plan`
inspects inputs locally; `profile-run` measures them with prepared dependencies. Reports
label library and roadmap sources separately and have no mathematical or merge authority.
