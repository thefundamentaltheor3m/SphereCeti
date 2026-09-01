# SphereCeti

A TauCeti-style roadmap for a unified Lean development of sphere packing in dimensions 8 and 24,
starting from the existing `Sphere-Packing-Lean` definitions and culminating in optimality and
uniqueness among periodic packings for the E8 and Leech configurations.

This repository is a **roadmap and compile-oriented target-signature package**, not a competing production
formalization.  The intended production home remains
[`thefundamentaltheor3m/Sphere-Packing-Lean`](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean),
with generic mathematics upstreamed to Mathlib or TauCeti as appropriate.

`README.md` is definitive.  [`SphereCeti/Suggested.lean`](SphereCeti/Suggested.lean) records
suggested declaration shapes and theorem endpoints, but it is deliberately nonexhaustive and may be
adjusted when implementation reveals a better Mathlib-shaped API.

## The two deliberate differences from TauCetiRoadmap

SphereCeti follows TauCetiRoadmap's mathematical and API discipline, with two explicit changes.

1. **SphereCeti imports a fixed TauCeti snapshot.**  TauCeti is not merely an external source or an
   informal upstream target: it is a Lake dependency pinned to a full commit.  This makes the
   `Suggested.lean` imports and `#check` contracts reproducible.
2. **Upstream candidates live in one file.**  There is no parallel directory tree of
   proposed Mathlib or TauCeti roadmaps.  [`UPSTREAM.md`](UPSTREAM.md) is an issue-ready ledger of
   declarations and larger topics whose intended destination is Mathlib or an appropriate
   TauCeti roadmap.  It records destinations only: upstream acceptance is never a prerequisite
   for any SphereCeti target.

## Exact dependency snapshot

| Component | Pin |
|---|---|
| Lean toolchain line | `leanprover/lean4:v4.34.0-rc1` |
| TauCeti | `8671bee98125933c56b9b00a08ded873b77dd23b` |
| Exact Mathlib commit resolved by that TauCeti snapshot | `618f225e1ff4a6b2790a944e01b806b7c68bdc56` |
| Sphere-Packing semantic baseline | `bad3de916074748eb88b7d1ee6dbf9494361ad17` |

Here “the 4.34.0-rc1 Mathlib pin” means the **Lean/Mathlib release line** selected by the toolchain,
while source reproducibility is supplied by the exact Mathlib commit in `lake-manifest.json`.  We do
not add an independent floating Mathlib requirement beside TauCeti: SphereCeti must use the same
resolved Mathlib graph as its pinned TauCeti dependency.

The TauCeti dependency is the complete repository snapshot at the SHA above, not a
contour-specific release.

The pinned Sphere-Packing baseline uses Lean/Mathlib `v4.32.0`, which is incompatible with this
package's dependency graph.  [`SphereCeti/Pinned.lean`](SphereCeti/Pinned.lean) therefore models the
public structures and semantic normalizations at that exact production commit.  Layer 0 upgrades
production to the shared dependency line; PR A2 then deletes the compatibility model and replaces
it with direct imports.  The compatibility model is not permitted to become a second
implementation.

The committed `lake-manifest.json` records the entire resolved dependency graph from the TauCeti
snapshot, not merely the user-facing TauCeti SHA.

## Summit statements

The density endpoints are:

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

The uniqueness endpoints are deliberately restricted to periodic packings:

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
| Equality in the periodic Cohn--Elkies sum forces all pairwise differences onto the magic-function zero shells | Sphere-Packing/SphereCeti | It depends on packing density, finite periodic patterns, and the specific certificate |
| The translated center set generates a full even integral lattice, and optimal density forces the packing to equal one coset of it | Sphere-Packing/SphereCeti | This is the geometric rigidity step from a packing to a lattice |
| Every positive-definite even unimodular rank-eight integral lattice is isometric to E8 | TauCeti IntegralLattices extension | Pure integral-lattice classification, independent of sphere packing |
| Every rootless positive-definite even unimodular rank-24 integral lattice is isometric to Leech | TauCeti IntegralLattices/Niemeier extension | Niemeier classification, with Leech isolated as the unique empty-root case |
| Universal optimality, Fourier interpolation, and quantitative stability | Separate TauCeti roadmaps | They require energy, interpolation, and quantitative metric infrastructure beyond packing density |

The most economical exact-uniqueness route is the one isolated by Cohn--Elkies, Section 8.  It
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

Fourier structure factors remain part of the general equality API and are useful checks, but
Cohn--Elkies explicitly note that the uniqueness deduction needs only the exact direct-side root
set, not restrictions on the roots of the Fourier transform.

## Governing principles

1. **Preserve the existing packing semantics.**  The pinned `SpherePacking`,
   `PeriodicSpherePacking`, `balls`, `finiteDensity`, `density`, and packing constants are the
   starting definitions.
2. **Build one common 8+24 library, not two copied proofs.**  Common structure includes lattices,
   Poisson summation, Cohn--Elkies certificates, theta series, radial Schwartz Fourier eigenspaces,
   equality conditions, and periodic rigidity.
3. **Do not force unlike dimension-specific modular formulas into a typeclass.**  Explicit data
   records passed to common constructors are acceptable; a global `MagicDimension` instance is
   not.
4. **Use TauCeti's integral-lattice layer rather than creating duplicate algebraic predicates.**
   SphereCeti owns the bridge to Mathlib's real topological `ZLattice` representation.
5. **Pin every hidden normalization.**  Fourier sign, Haar measure, theta exponent, q parameter,
   separation versus sphere radius, covolume, and modular slash conventions are permanent API
   decisions.
6. **Separate inequality from equality.**  An optimal density theorem needs weak sign conditions;
   periodic uniqueness additionally needs exact zero sets and a termwise equality analysis of the
   Poisson bound.
7. **Keep geometric density in `ℝ≥0∞`.**  Add coercion lemmas for finite expressions rather than
   replacing the measure-theoretic definition by a real-valued surrogate.
8. **Every production PR starts from current `main`.**  The historical `gauss2` branch and PR #420
   are proof quarries, not branch bases or architectural specifications.
9. **Automation attributes are part of the public API.**  `@[simp]`, `@[grind]`, and `@[fun_prop]`
   additions require small contract examples.
10. **Generic local work is shaped for upstream from the beginning.**  The issue-ready destination
    is recorded in `UPSTREAM.md`, even when waiting would block SphereCeti and a local proof is
    temporarily necessary.

## Existing material to preserve and consume

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
- consolidate `numReps`/`numReps'` into one orbit-count API;
- remove global heterogeneous `NNReal`/`ENNReal` arithmetic instances;
- remove `@[simp]` from the large basis-free periodic density expansion;
- replace duplicate Fourier involution arguments in `a/Eigenfunction` and `b/Eigenfunction` by the
  radial Schwartz API;
- retire the temporary Cohn--Elkies prerequisites file after the real Poisson API lands;
- extract generic q-series and analytic lemmas from the E8-specific files.

### From the `gauss2` branch

Mine, with exact source attribution:

- the completed E8 summit theorem;
- the final normalization of the magic function;
- real-valuedness and Fourier-eigenfunction assembly;
- exact sign and zero deductions;
- the Möbius-inversion wedge contour argument;
- the more developed Fourier permutation proof for the integral pieces.

Do not wholesale merge or rebase the branch.  Port one coherent theorem or API at a time onto the
upgraded production `main`.

### From PR #420

Mine and split:

- general lattice summability for Schwartz functions;
- dual-lattice infrastructure;
- Poisson summation;
- basis-independent covolume statements;
- general periodic Cohn--Elkies counting.

### From the pinned TauCeti snapshot

SphereCeti must directly consume the following coherent APIs.

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
“integral real lattice” would create a permanent schism.

#### Complex and modular analysis

- `TauCeti.Contour.circleIntegral_eq_zero_of_meromorphicOrderAt_nonneg` for closed circles;
- the generic `UpperHalfPlane.resToImagAxis` API and its modular `S`-transformation;
- q-coefficient vanishing versus cusp-function Big-O estimates;
- the generic function and logarithmic-derivative `S`-transformation;
- finite-index Sturm bounds when a congruence-level identity genuinely requires them;
- the small Fourier-continuity adapter.

These do not replace Sphere-Packing's open rectangular contour deformation or the specialized
convex-wedge Möbius argument.  Closed circles, unbounded rectangles, and finite path homotopies solve
different problems.

## Permanent mathematical conventions

The fuller ledger is in [`CONVENTIONS.md`](CONVENTIONS.md).  The central choices are:

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

\[
  e^{-2\pi i\langle x,\xi\rangle}.
\]

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
`IsSimilar` permits one positive scaling before congruence.  Both relations have
reflexive/symmetric/transitive APIs, and positive density supplies the center used by rigidity.

### Attributes

Good `@[simp]` declarations are canonical projections and evaluations:

- scaling centers/separation/density;
- `ofZLattice` centers, lattice, and separation;
- shell membership;
- norm-squared profile evaluation;
- coercions of radial Schwartz Fourier transforms.

Large semantic transformations are explicit, not simp rules:

- Poisson summation;
- the Cohn--Elkies bound;
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
4.34/TauCeti dependency graph of SphereCeti, with no mathematical redesign in the same PR.

Deliverables:

1. bump `lean-toolchain` to `v4.34.0-rc1`;
2. pin TauCeti to `8671bee98125933c56b9b00a08ded873b77dd23b`;
3. resolve Mathlib to `618f225e1ff4a6b2790a944e01b806b7c68bdc56`;
4. repair source incompatibilities without opportunistic refactors;
5. add exact `#check` and Fourier-normalization contracts;
6. add Sphere-Packing as a direct SphereCeti dependency;
7. delete `SphereCeti.Pinned` and rewrite `Suggested.lean` imports against production declarations.

This is the only layer in which the compatibility model is tolerated.

## Layer 1 — packing API preservation and import hygiene

**Goal:** stabilize the public geometric boundary before adding new mathematics.

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

**Goal:** make TauCeti's rational integral-lattice library and Mathlib's Euclidean `ZLattice`
representation two views of the same concrete lattice data.

Deliverables:

- `EuclideanLattice.IntegralPresentation`;
- construction of the TauCeti `ofGramMatrix` lattice;
- Gram compatibility with the real inner product;
- integral equivalences between the real carrier/dual and TauCeti's carrier/dual carrier;
- an explicit real-dual membership theorem in TauCeti dual-carrier coordinates;
- discriminant/covolume and unimodular/covolume-one comparisons;
- finite norm shells and minimum-norm predicates;
- shell equivalences and transport of evenness, unimodularity, and rootlessness;
- extension of a TauCeti classification isometry to a real linear isometry, then to an affine
  isometry carrying one lattice coset to another.

Do not introduce a second global `IsIntegral` predicate on real lattices.  Integrality is witnessed
by the presentation and discharged through TauCeti.
Positive-definiteness is derived from the full Euclidean presentation rather than carried as a
separate hypothesis.  The E8 and Leech reference objects and classifications remain in their
dimension-specific layers.

## Layer 3 — periodic orbit and density API

**Goal:** replace implementation-dependent representative choices by one canonical finite-pattern
interface.

Deliverables:

- `PeriodicSpherePacking.ofZLattice`;
- one `FundamentalPattern` structure whose representatives have type `P.centers`;
- the existing finite quotient `Quotient P.addAction.orbitRel`, exposed as `P.Orbit`;
- `P.numOrbits = Fintype.card P.Orbit` and `D.reps.card = P.numOrbits`;
- the canonical center intensity
  `P.centerIntensity = P.numOrbits / ZLattice.covolume P.lattice`;
- basis-free density formula

\[
  \operatorname{density}(P)
  = \operatorname{numOrbits}(P)\,
    \operatorname{vol}(B(0,r/2))/\operatorname{covol}(\Lambda);
\]

- translated coordinate boxes and their finite center patterns;
- a Fubini/Følner averaging theorem that finds an arbitrarily large translated box whose
  normalized center count approximates a high finite-density ball;
- guarded repetition of those translated finite patterns, with explicit center/separation
  equations;
- exact periodicized density and fixed-width boundary-layer volume decay;
- `ε`-approximation of every packing density by a periodic packing density;
- `PeriodicSpherePackingConstant d = SpherePackingConstant d` as the resulting corollary.

The large density formula must not be a simp lemma.

## Layer 4 — Poisson summation and Cohn--Elkies

**Goal:** isolate the linear-programming theorem from the dimension-specific magic functions.

Deliverables:

- Schwartz summability on lattice translates;
- shifted and unshifted Poisson summation with the exact positive phase and inverse-covolume
  factor;
- automatic discreteness, full-rank, double-dual, and reciprocal-covolume APIs for the real dual;
- a unit-Gaussian normalization test and the exact finite-pattern squared-amplitude formula;
- `CohnElkies.Certificate d r`, with no radiality requirement;
- certificate bound and scaling API;
- `Certificate.ofRadial` as a construction adapter;
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

## Layer 5 — theta series

**Goal:** add a genuine lattice theta API, distinct from the existing Jacobi theta functions.

Deliverables:

- analytic theta definition and normal convergence;
- finite-shell regrouping and q-expansion without `Set.ncard` fallback semantics;
- even-lattice `T`, Poisson/dual `S`, and unimodular `S` transformations;
- even-unimodular level-one modular form with a coercion theorem identifying its function with
  `latticeTheta` and explicit constant/first q-coefficients;
- weight-four and weight-twelve level-one linear classification theorems stated as equalities in
  the structured modular-form types;
- rank-eight classification

\[
  \Theta_\Lambda = E_4;
\]

- rank-24 classification

\[
  \Theta_\Lambda
  = E_4^3 + (N_2(\Lambda)-720)\Delta;
\]

- rootless specialization

\[
  \Theta_\Lambda=E_4^3-720\Delta.
\]

The theta theory is not merely decorative.  It checks all lattice normalizations, gives shell
cardinalities, and supplies the modular classification used in the E8/Leech infrastructure.

## Layer 6 — E8 and Leech lattice packages

### E8

Retain the existing coordinate and basis descriptions, then package:

- an `IntegralPresentation`;
- positive-definiteness, evenness, and unimodularity;
- minimum squared norm `2`;
- theta identity;
- root count `240`;
- valid ADE component indices for the root-system classification;
- canonical lattice packing and density.

The direct minimum-norm proof remains independent of the theta identity.

### Leech

Pin the extended Golay code by its exact polynomial generator matrix and prove its dimension,
cardinality, self-duality, doubly-evenness, minimum weight, all-one word, and full weight enumerator.
Check the matrix transcription in Lean through a unitriangular row-reduction certificate and exact
generator-row weights.
Define Leech by the exact modulo-eight/residue-code coordinate conditions with `1 / sqrt 8`
scaling.  The 24 published integer basis rows divided by `sqrt 8` must lie in and span exactly that
single coordinate lattice; its integer matrix has determinant `8^12`.  These finite matrix claims
must use explicit Lean-checked certificates rather than relying on an unverified transcription.  No
second opaque lattice submodule is introduced.

Required endpoints:

- even, unimodular, positive-definite;
- minimum squared norm `4`;
- theta identity;
- shell cardinality `196560`;
- unit-ball packing density `π^12 / 12!`.

The naive unshifted Construction-A lattice of the extended binary Golay code must not be called the
Leech lattice.

## Layer 7 — radial profiles, parametric integration, and signed kernels

**Goal:** extract the genuinely common analytic pattern without hiding dimension-specific formulas.

Common API:

- squared-norm radial profile constructor;
- restricted radial Schwartz Fourier transform;
- `+1` and `-1` eigenspace operations;
- Gaussian/Laplace kernel integrability and the complex-parameter Gaussian Fourier transform;
- Fubini/Tonelli interchange between the ambient space and a contour parameter;
- differentiation under parameterized integrals and smoothness of iterated-derivative families;
- the inversion change of variables between `(0,1]` and `[1,∞)`;
- exact local zero orders through nonvanishing cofactors;
- q-expansion Big-O estimates for cusp decay.

The concrete `+1` and `-1` component proofs expose their exact signed kernel transformation laws
before a common constructor is extracted.  The extracted declaration contains only hypotheses
proved in both constructions, and its finite Fourier sign occurs in the transformation law that
determines the eigenvalue.  No free complex `eigenvalue` field is part of this interface.

## Layer 8 — contour deformation and magic-integral transport

**Goal:** provide the deformation identities that transport the magic-function contour integrals,
stated once over a single pair of kernels.

All required finite deformations use straight segments and their images under the Möbius
inversion `z ↦ -1/z`; all required unbounded deformations use axis-aligned rectangles.  Each
contour tool has one owner:

- closed circles without poles use TauCeti's meromorphic Goursat theorem;
- unbounded vertical deformations use this layer's open-rectangle theorems;
- finite Möbius deformations use this layer's wedge interface, consuming Mathlib's
  curve-integral Poincaré lemma.

The layer has two independent summits.

### Unbounded branch: open rectangles

- boundary vanishing on a bounded rectangle, consumed from Mathlib's rectangular
  Cauchy--Goursat theorem;
- deformation of a horizontal edge into the two vertical half-lines above its endpoints, with
  explicit integrability hypotheses on the half-lines and the top edge controlled either by
  uniform decay or by convergence of the top-edge integrals to zero.

These identities feed the vertical-line rewrites, Laplace representations, and double-zero
arguments of Layer 9.

### Finite branch: curve-integral transport and the Möbius wedge

- the scalar one-form of a function `F : ℂ → ℂ`, with the bridge between interval integrals over
  a parametrized segment and Mathlib curve integrals;
- change of variables along a segment, carrying an honest derivative/chain-rule hypothesis for
  the substitution;
- a closed-one-form adapter bundling differentiability-with-closure-continuity and symmetry of
  the within-derivative, together with the one-way discharge lemma from holomorphy with closure
  continuity to closedness of the scalar one-form; the converse is not a target;
- the Möbius inversion, its derivative, and its action on the upper half-plane;
- the wedge `{z : 0 < Im z, |Re z - 1| < Im z}`: openness, convexity, and the fact that its
  closure meets the real axis only at `1`;
- the two signed contour-permutation theorems, stated for a single pair `Ψ, Ψ' : ℂ → ℂ`
  satisfying the signed Möbius transformation law with `ω_{Ψ'}` closed on the wedge: the
  integrals over the left legs `[-1, -1+i]` and `[-1+i, i]` equal the correspondingly signed
  integrals over the right legs `[1, 1+i]` and `[1+i, i]`.

Intermediate wedge homotopies are proof devices, not public targets.  Radial families
instantiate the single-pair statements; they are not part of the generic interface.

### Closing deliverable: the generic component Fourier identity

For even dimension `2k`, one theorem computes the Fourier transform of a radial left-leg contour
component `x ↦ ∫ g(z) exp(π i ‖x‖² z) dz` from explicit hypotheses: absolute product
integrability of the double integral, the `r`-free signed Möbius law
`(i/z)^k g(z) = ± z⁻² g'(-1/z)` on the upper half-plane, and closedness of the transported
kernel's one-form on the wedge.  Its conclusion is the correspondingly signed right-leg
component of `g'`.  The E8 and Leech components of Layer 9 are transparent instantiations of
this theorem; no bundled kernel record and no opaque constructor stands between them and the
contour machinery.

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
- the bundled Cohn--Elkies certificate with `certificate.f = magic`;
- candidate-lattice sharpness and equality of the bound with the candidate lattice density.

The exact zero set is a first-class endpoint.  Density optimality only needs weak inequalities, but
periodic uniqueness needs to infer that every nonzero pairwise difference lies on an E8 or Leech
shell.

So that the stability roadmaps recorded in `UPSTREAM.md` can reuse the hard analytic work,
preserve multiplicity and quantitative lower-bound information rather than proving only
`f x = 0` statements and discarding the stronger estimates.

## Layer 10 — equality and rigidity

**Goal:** formalize the equality case of the linear-programming argument, not just the numerical
bound.

### Common equality engine

Given an optimal periodic packing and a fundamental pattern:

1. the periodic Cohn--Elkies inequality is an equality;
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

This is the formal counterpart of Cohn--Elkies, Lemma 8.2 and the argument immediately following
it.  Expose the covolume/discriminant bridge and quotient-cardinality argument through
reusable intermediate theorems, not hidden in two enormous summit proofs.
The quotient cardinal inequality is stated only after discreteness and full rank of the generated
lattice have made the relative quotient finite; Mathlib's `relIndex` is zero at infinite index.

### E8 rigidity

The E8 shell spectrum gives a positive-definite even unimodular rank-eight lattice.  Use the
classification theorem that such a lattice is isometric to E8, then transport the center coset to
obtain periodic congruence.

The classification theorem is generic integral-lattice mathematics; its intended home is a
TauCeti IntegralLattices roadmap extension, recorded in `UPSTREAM.md`.  It is a required
dependency of this roadmap: implement it locally, with exactly the upstream-shaped statement,
whenever coordination or timing requires it.  Upstream acceptance is never a prerequisite.

### Leech rigidity

The Leech shell spectrum gives a rootless positive-definite even unimodular rank-24 lattice.  Use the
uniqueness characterization of Leech and transport the center coset.

The rank-24 route is the Niemeier classification.  Its target interface enumerates all 24 cases,
constructs the canonical lattice attached to each root-system/glue-code case, produces the
classification isometry, and proves that the root set is empty exactly for the Leech case.  The
generic development belongs in TauCeti and is recorded in `UPSTREAM.md`; it remains a required
dependency and is proved locally with the same statement shape when coordination requires it.

## Layer 11 — summit assembly

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

The summit files contain only imports, two inequalities, `le_antisymm`, and the equality-case
theorem.  Analytic or lattice classification work in a summit file signals a missing API layer.

# Uniqueness, universal optimality, and stability

The roadmap includes **exact periodic uniqueness** because it is a direct equality-case continuation
of the same Cohn--Elkies certificates used for density optimality.

It does not attempt to absorb the following larger theories:

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
- change one mathematical boundary;
- preserve or reduce `sorry` count;
- record source provenance when mining `gauss2` or PR #420;
- include small API/automation contract examples;
- avoid broad directory moves in the same PR as a hard proof;
- provide compatibility aliases before deleting public names;
- distinguish “copied proof material” from “new target API”.

# Repository files

| File | Role |
|---|---|
| `README.md` | Definitive mathematical roadmap |
| `SphereCeti/Suggested.lean` | Proposed target signatures and contract checks |
| `SphereCeti/Pinned.lean` | Temporary model of the older Sphere-Packing public API |
| `CONVENTIONS.md` | Permanent normalization and attribute decisions |
| `MIGRATION.md` | Main-first targeted PR sequence |
| `PROVENANCE.md` | Source and dependency ledger |
| `UPSTREAM.md` | Issue-ready Mathlib/TauCeti upstream ledger |
| `VALIDATION.md` | Static contract and Lean-elaboration validation record |
| `scripts/check_roadmap.py` | Deterministic pin, link, and target-shape contract check |
| `.github/workflows/ci.yml` | Static contract check followed by Lean elaboration |
| `lakefile.toml` | Exact TauCeti dependency |
| `lake-manifest.json` | Full resolved pin set |
| `lean-toolchain` | Lean `v4.34.0-rc1` |

# References

Core papers:

- H. Cohn and N. Elkies, *New upper bounds on sphere packings I*, Annals of Mathematics 157
  (2003), 689--714.
- M. Viazovska, *The sphere packing problem in dimension 8*, Annals of Mathematics 185 (2017),
  991--1015.
- H. Cohn, A. Kumar, S. Miller, D. Radchenko, and M. Viazovska,
  *The sphere packing problem in dimension 24*, Annals of Mathematics 185 (2017), 1017--1033.
- H. Cohn and A. Kumar, *Optimality and uniqueness of the Leech lattice among lattices*, Annals of
  Mathematics 170 (2009), 1003--1050.
- H. Cohn, A. Kumar, S. Miller, D. Radchenko, and M. Viazovska,
  *Universal optimality of the E8 and Leech lattices and interpolation formulas*, Annals of
  Mathematics 196 (2022), 983--1082.
- K. J. Böröczky, D. Radchenko, and J. P. G. Ramos,
  *A quantitative stability result for the sphere packing problem in dimensions 8 and 24*, 2023.

Formal sources and sibling projects:

- `thefundamentaltheor3m/Sphere-Packing-Lean` at the pinned production baseline;
- `TauCetiProject/TauCeti` at the exact dependency pin;
- `TauCetiProject/TauCetiRoadmap`, especially the IntegralLattices and ContourIntegration roadmaps;
- Mathlib's `ZLattice`, Schwartz/Fourier, Gaussian, modular-form, q-expansion, and measure APIs.
