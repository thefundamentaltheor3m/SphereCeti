# Main-first migration and PR sequence

Use the phases below to identify dependencies and adapt source material. New mathematical
proofs land in SphereCeti under `SphereCeti/<Topic>/`. Start from this repository's current
`main` unless the PR names one immediate stacking dependency. Historical branches and PR
#420 are provenance sources.

Steps that edit existing Sphere-Packing-Lean files describe work specific to that repository.
A1 upgrades its toolchain and A2 replaces SphereCeti's frozen compatibility layer with direct
imports. A proof using SphereCeti's existing pinned dependencies can proceed today. A proof
that requires direct imports from the migrated external project still depends on A2.

## 1. Migration invariants

Every PR must preserve the following unless its title explicitly changes one of them.

1. `SpherePacking` stores center separation, and balls have half that radius.
2. Geometric density is `ℝ≥0∞` and infinite density is a limsup.
3. E8 remains available through its current public declarations during migration.
4. The Fourier kernel is Mathlib's `exp(-2πi⟪x,ξ⟫)` convention.
5. Public names receive compatibility aliases before removal.
6. No new theorem imports a tactic test file through the production root.
7. No hard proof is mixed with a tree-wide file move.
8. No source material adapted from `gauss2` or PR #420 is copied without a provenance note.
9. `@[simp]`, `@[grind]`, and `@[fun_prop]` changes include small, focused `example`s that check the
   intended behavior.
10. Build the full project at the PR head. Document any proposed specification change explicitly.
    A library proof of an existing target does not require changing its roadmap statement.

## 2. Material disposition

| Existing material | Disposition |
|---|---|
| `Basic/SpherePacking.lean` definitions | Preserve statements and semantics |
| scaling theorems | Preserve; add safe simp attributes |
| periodic density proof | Preserve mathematics; replace exposed implementation details |
| `Basic/E8.lean` | Preserve mathematical content; split only after PR H1's bridge results land |
| `ForMathlib/RadialSchwartz/*` | Make this the standard setting for Fourier analysis |
| Jacobi theta, E2/E4/E6, Δ, Serre derivative | Preserve; converge generic lemmas with TauCeti |
| `MagicFunction/a`, `b`, `g` | Preserve E8 proof content; move generic pieces out incrementally |
| `CohnElkies/Prereqs.lean` | Retire after genuine Poisson summation and dual-lattice results land |
| root aggregator test imports | Remove immediately |
| `numReps'` and basis-dependent public counting | Migrate to a single orbit-count definition |
| heterogeneous `NNReal`/`ENNReal` global instances | Remove in a focused PR |
| full periodic density formula marked `@[simp]` | Remove attribute; retain named theorem |
| `gauss2` completed theorem | Port theorem-by-theorem after foundations |
| PR #420 | Import TauCeti summability, duality, Poisson, and covolume APIs; adapt periodic Cohn–Elkies counting only |

## 3. Phase A — establish the exact dependency line

### PR A0 — initial SphereCeti roadmap

**Repository:** `thefundamentaltheor3m/SphereCeti`

Create the roadmap package with:

- exact Lean/TauCeti/Mathlib pins;
- `README.md`;
- `SphereCetiRoadmap/Suggested.lean`;
- the temporary `Pinned.lean` compatibility model;
- convention, migration, provenance, and upstream records;
- build-only CI.

Acceptance:

- manifest parses;
- every markdown link resolves;
- no placeholder theorem is disguised as `True`;
- `lake build` passes on the pinned toolchain.

### PR A1 — production toolchain migration only

**Repository:** `Sphere-Packing-Lean`

Bump production to:

```text
Lean       v4.36.0-rc2
TauCeti    83769e442d55cda9d85b3927a93b286831c595ff
Mathlib    1b1ccf4b088b32fa3f23f2de1127433254a81e1e
```

Scope:

- toolchain and Lake files;
- syntax/API repairs forced by the bump;
- exact imports of the required TauCeti modules;
- no mathematical refactor;
- no directory move;
- no new abstraction beyond compatibility shims required for the build.

Acceptance:

- full production build green;
- E8 public declarations remain available;
- the main theorem retains its statement;
- checks of the Fourier convention pass: the kernel sign and Gaussian transform agree with
  [CONVENTIONS.md §10](CONVENTIONS.md#10-fourier-transform), using proofs without new admissions;
- no dependency has an unpinned branch revision.

### PR A2 — direct SphereCeti imports

**Repository:** `SphereCeti`

Add `Sphere-Packing-Lean` as an exact dependency at the migrated production commit.  Replace
`SphereCetiRoadmap.Pinned` imports and temporary declarations with exact production imports.  Delete
`Pinned.lean` in full.

Acceptance:

- every required declaration in `Suggested.lean` resolves to production or pinned TauCeti
  declarations, and typed checks confirm the expected interfaces (a bare `#check` checks only
  name resolution);
- no duplicate `SpherePacking`, `PeriodicSpherePacking`, or `RadialSchwartzMap` remains;
- the manifest records exact commits for both dependencies.

## 4. Phase B — stabilize the existing public definitions

### PR B1 — keep test files out of the production import graph

Split:

```text
SpherePacking.lean       -- production modules only
SpherePackingTests.lean  -- tactic tests and behavior checks
```

Do not change proofs beyond import fallout.

### PR B2 — basic lemmas for sphere packings

Add:

- directional center-separation theorem with a clean proof;
- `density_le_SpherePackingConstant`;
- `density_le_PeriodicSpherePackingConstant`;
- safe `[simp]` constructor projections;
- `[simp]` on positive scale density and scale-to-packing projections;
- basepointed finite density and a proof that upper density is basepoint-independent;
- transport by real affine isometries, with explicit formulas for the transported centers and
  separation;
- `IsCongruent` and `IsSimilar` with reflexivity, symmetry, and transitivity lemmas;
- positive density implies that the center set is nonempty.

The periodic `scale_density` target has no dimension-positivity hypothesis.  Translation invariance
must pass through basepoint independence rather than a finite-density rewrite at the origin.

Do not expand the full density formula under `simp`.

### PR B3 — checks of root declarations and namespaces

Add a small module of checks confirming:

- public declaration names and namespaces;
- separation/radius semantics;
- E8 normalization;
- Fourier convention;
- no test module in the production import graph.

This is intentionally separate from B2 to give downstream refactors a stable early check that fails
if any of these change.

## 5. Phase C — the real/rational lattice bridge

This phase can begin in parallel with the periodic refactors after A1.

### PR C1 — minimum norms over TauCeti's shells

Shells, their finiteness, representation numbers, and their invariance under linear isometries are
TauCeti's (`ZLattice.shell`, `ZLattice.finite_shell`, `ZLattice.representationNumber`,
`ZLattice.representationNumber_comap`).  Add only:

- a predicate expressing a lower bound on nonzero squared norms, and its attainment;
- membership simp lemmas where TauCeti does not already provide them;
- minimum-norm grind rules.

### PR C2 — integral presentations

Define explicit data:

```lean
EuclideanLattice.IntegralPresentation Λ
```

containing a finite `ℤ`-basis, integer symmetric Gram matrix, and compatibility with the real inner
product.  Construct the corresponding `TauCeti.IntegralLattice.ofGramMatrix`.

Acceptance:

- E8 obtains a presentation without changing `E8Lattice`;
- the presentation has no typeclass instance that would become ambiguous if a lattice has several
  bases;
- basis change produces an integral-lattice isometry.

Provide an `ofBasis` constructor that derives Gram symmetry from the real inner-product equation;
callers do not prove a separate `gram_isSymm` field.

### PR C3 — dual compatibility

Compare:

- the real inner-product dual `ZLattice.dual` (TauCeti);
- TauCeti's rational dual carrier.

Construct integral equivalences between the real carrier/dual and TauCeti's carrier/dual carrier.
Prove real-dual membership equivalence through the rational dual-carrier coordinates and transport
evenness and unimodularity to `ZLattice.IsEven` and `ZLattice.IsUnimodular`, rootlessness, and
exact norm shells between `ZLattice.shell` and `vectorsOfNorm`.

### PR C4 — discriminant/covolume compatibility

TauCeti proves that the squared covolume is the Gram determinant of any `ℤ`-basis
(`ZLattice.covolume_sq_eq_det_gram`) and that an integral real lattice is unimodular exactly when it
has covolume one (`ZLattice.IsIntegral.isUnimodular_iff_covolume_eq_one`).  Prove:

- TauCeti's discriminant of the presentation lattice is the squared real covolume;
- positive-definite unimodular presentations have covolume one;
- isometry invariance;
- every TauCeti classification isometry extends to a real linear isometry mapping carriers, and
  then to an affine isometry mapping lattice cosets.

Derive positive-definiteness from a full Euclidean presentation.  The determinant lower bound and
classification statements do not carry redundant positivity or nondegeneracy hypotheses.

Avoid global coercion instances between rational and real lattice types.  Compare
`IntegralPresentation` with TauCeti's rational model `ZLattice.ratModel` (#21332, superseding
#20950) through the basis-induced isometry `IntegralPresentation.ratModelIsometry` rather than
creating a second conversion, and obtain the real-side adapters by transporting TauCeti's model
comparisons along it; see the [resync watchlist](UPSTREAM.md#g-resync-watchlist).

## 6. Phase D — periodic packings and density

### PR D1 — canonical lattice packing constructor

Add:

```lean
PeriodicSpherePacking.ofZLattice
```

from a full discrete Euclidean lattice, a positive separation, and a minimum-norm hypothesis.

Refactor `E8Packing` through it while preserving the existing public name and theorem statements.

### PR D2 — orbit quotient and chosen representatives

Expose the quotient of the centers by the period lattice as `Orbit`, an abbreviation for the
existing `Quotient P.addAction.orbitRel`, and prove that it is finite.  Where an argument needs
actual centers, use the chosen representative `orbitRep` (through `Quotient.out`) and prove:

- every center differs from the representative of its orbit by a period
  (`exists_lattice_vadd_orbitRep`);
- representatives of distinct orbits lie in distinct cosets of the period lattice
  (`orbitRep_sub_mem_lattice_iff`).

Relate the quotient to production's basis-relative fundamental-domain representatives through
`addActionOrbitRelEquiv'`.  No separate pattern structure is introduced, and every statement that
uses the representatives is independent of the choice.

### PR D3 — retire duplicate representative counts

Define `numOrbits` as the `Fintype.card` of `Orbit` and prove that it agrees with the old `numReps`
and `numReps'`.  Migrate the declarations that use the old counts, define `centerIntensity` as
`numOrbits / covolume`, deprecate `numReps` and `numReps'`, then remove the duplicate
representative code in PR O3.

### PR D4 — basis-free density formula

State the density formula in terms of:

- the canonical `P.numOrbits`;
- ball volume;
- lattice covolume.

Remove the global heterogeneous arithmetic instances.  Remove `@[simp]` from the large expansion.
Add explicit, short specializations for one-coset lattice packings.

### PR D5 — periodic approximation

Use translated coordinate boxes with a guard band of one center separation.  Define the finite
patch, its period lattice, and the repeated center set, then state explicit equations
for the centers and separation of `ofFinitePatternInBoxAt`.

The volume estimate for coordinate boxes and the counting step of the averaging lemma do not
involve packings and may land first:

- a fixed-width coordinate-box boundary layer has volume ratio tending to zero;
- for a finite set `S` and a measurable set `Q`, the number of points of `S` in `a +ᵥ Q` has
  integral `#S * vol(Q)` over `a`, so some translate with `a` in a set of finite positive volume
  containing `S - Q` meets `S` in at least the average number of points.

Then prove in order:

- a Fubini/Følner averaging lemma: from an arbitrarily large ball whose finite density approaches
  the ball-limsup density, extract an arbitrarily large translated coordinate box whose normalized
  center count loses only a prescribed error, using the counting step;
- the repeated patch satisfies the packing inequality, including across adjacent boxes;
- its exact density in terms of the patch cardinality and box covolume;
- for every positive `ε`, every packing has a periodic packing `Q` with
  `P.density ≤ Q.density + ε`, using the boundary-layer estimate.

Deduce:

```lean
PeriodicSpherePackingConstant d = SpherePackingConstant d
```

as its own theorem/file.  The proof does not depend on E8 or dimension-specific modular forms.

## 7. Phase E — Poisson summation

TauCeti supplies Poisson summation over a full lattice, the dual lattice with its instances, and
`dual_dual` and `covolume_dual`.  The translated formula

```text
Σ_{x∈Λ} f(x+a) = covol(Λ)⁻¹ Σ_{y∈Λᵛ} f̂(y) exp(2πi⟪y,a⟫)
```

is `SchwartzMap.tsum_eq_tsum_dual_fourier`.  PR #420's summability, duality, and Poisson pieces are
therefore not ported; only its periodic counting is adapted, in Phase F.

### PR E1 — adopt TauCeti's Poisson summation

Replace the uses of the temporary Cohn–Elkies prerequisites by
`SchwartzMap.tsum_eq_tsum_dual_fourier` over `ZLattice.dual`, with the summability of both sides
from `ZLattice.summable_poisson_left` and `ZLattice.summable_poisson_right`.  Test the
normalization on the unit Gaussian and on the self-dual covolume-one case.

### PR E2 — structure factors

From the translated formula, derive the finite-pattern amplitude and structure factor:

```text
A_P(y) = Σ_{s∈pattern} exp(2πi⟪y,s⟫),
S_P(y) = |A_P(y)|².
```

Prove that the phase at a dual frequency is independent of the representative of `P.Orbit`.
Record `0 ≤ S_P(y)`, `S_P(y) = 0 ↔ A_P(y) = 0`, and the exact vanishing alternative required
by periodic equality cases.

## 8. Phase F — Cohn–Elkies as a reusable theorem

### PR F1 — certificate structure

Add a nonradial `CohnElkies.Certificate d r` and its basic theory:

- direct/Fourier real-valuedness;
- sign conditions;
- positivity at Fourier zero;
- scale and linear-isometry transport;
- `ofRadial`, the constructor from radial functions.

### PR F2 — lattice and periodic bounds

Prove the lattice bound first, then the finite-pattern periodic bound.  Keep all finite sums visible
until nonnegativity is applied.

### PR F3 — unrestricted bound

Combine the periodic theorem with D5.  Retire `CohnElkies/Prereqs.lean` once every result that uses
it relies instead on TauCeti's Poisson summation (E1).

### PR F4 — equality relation

Define the equality/sharpness data separately from the certificate.  Expose exact real-valued
nonnegative defects satisfying

```text
m f(0) - (m² / covol(Λ)) f̂(0) = D_Fourier + D_direct
```

and, for `0 < m`, the normalized gap identity obtained by division by `m f̂(0)`.  Prove:

- equality forces direct-side zero terms;
- equality forces Fourier-side products `f̂(y) * S_P(y)` to vanish;
- strict signs upgrade these products to exact shell or structure-factor statements.
- equality implies canonical pattern-independent sharpness;
- sharpness and `0 < P.numOrbits` imply equality.

Also derive `Certificate.f_zero_pos` and `Certificate.bound_pos` from Fourier inversion,
`fourier_nonneg`, and `fourier_zero_pos`.  Do not combine the two equality directions into an
unqualified `iff`: the empty packing makes termwise sharpness vacuous.

Do not yet prove dimension-specific rigidity.

## 9. Phase G — theta series from the TauCeti ThetaSeries roadmap

This phase can run in parallel with the magic-function port after E1/C4.  Lattice theta series
with their transformation laws, the theta series of an even unimodular lattice as a modular form,
and the identities in ranks 8 and 24 belong to the TauCeti ThetaSeries roadmap; SphereCeti uses
them.  TauCeti has implemented the theta series, its convergence, holomorphy, and q-expansion, and
its `T`-translation law (`ZLattice.thetaSeries` and related declarations), the `S`-transformation
`ZLattice.thetaSeries_S_smul`, the level-one form `ZLattice.thetaForm`, and the rank-8/24
identities; the [resync watchlist](UPSTREAM.md#g-resync-watchlist) records their sources.
Nothing in this phase is needed for the optimality theorems.

### PR G1 — import the ThetaSeries results

Import TauCeti's theta inversion, theta form, and rank-8/24 identities and keep typed checks of
their normalizations, as `Suggested.lean` Layer 5 does.  SphereCeti states no general theta
targets of its own and does not develop a second general theory.

### PR G2 — comparison with integral presentations

Relate integral presentations to TauCeti's real predicates: an even (unimodular) presentation makes
the real lattice `ZLattice.IsEven` (`ZLattice.IsUnimodular`), and the root count is the
representation number `ZLattice.representationNumber Λ 2`.

### PR G3 — E8/Leech theta corollaries

Derive, through these comparisons, the three corollaries used by the E8 and Leech lattice
packages:

```text
rank 8 even unimodular: Θ = E₄
rank 24 even unimodular: Θ = E₄³ + (N₂ - 720) Δ
rootless rank 24: Θ = E₄³ - 720 Δ
```

Each is a specialization of TauCeti's identity (`ZLattice.IsEven.thetaForm_eq_E₄`,
`ZLattice.IsEven.thetaSeries_eq_E₄_cube_add_mul_discriminant`) through G2.

## 10. Phase H — E8 as a fully bridged object

### PR H1 — bridge results without splitting the E8 file

Without moving the large existing E8 file, add:

- integral presentation;
- a Gram-preserving isometry from that presentation to TauCeti's
  `IntegralLattice.typeE₈RootLattice`;
- positive-definite/even/unimodular proofs;
- covolume-one bridge;
- shell compatibility.

### PR H2 — root count

Prove the cardinality `240` of the real shell of squared norm `2`, by transporting TauCeti's
enumeration `typeE₈RootEquiv` (equivalently `kissingNumber_typeE₈RootLattice`) through H1's
isometry.  This count is independent of theta theory.  Keep the direct minimum-norm proof as the
packing input.

### PR H3 — theta identity

After G3, prove `Theta_E8 = E₄` as a second characterization and regression test.  It is not an
input to E8 optimality.

### PR H4 — file split

Only after H1/H2, split the E8 development into basic, Gram/integral, packing, and theta modules,
with compatibility import shims.

## 11. Phase I — Golay and Leech

TauCeti supplies the coding theory, the extended binary Golay code `TauCeti.BinaryGolay.code`, and
the canonical Leech lattice `TauCeti.leechLattice` with its evenness, unimodularity, congruence
model, minimum `4`, and absence of roots.  This phase constructs no second Golay code or Leech
lattice; it transports TauCeti's lattice into the packing space and compares the other
descriptions with it.

### PR I1 — transported Euclidean Leech lattice

Define the Euclidean Leech lattice as the image of `leechLattice.carrier` under
`T(x) = x / √2`, so that `T(a / 2) = a / √8`.  Prove:

- `⟪T x, T y⟫ = B(x, y)`, where `B` is the form of `leechLattice`;
- discreteness and full rank of the image, and covolume one;
- transport of every norm shell, hence minimum squared norm `4` and no roots, from
  `minimum_leechLattice` and `vectorsOfNorm_two_leechLattice`;
- an integral presentation with an isometry to `leechLattice`, hence evenness and unimodularity.

### PR I2 — canonical packing

Construct the canonical unit-ball packing of separation `2` and prove its density `π^12 / 12!`.
PR I1 and this PR are the only Leech inputs to optimality.

### PR I3 — secondary comparisons

Prove, with explicit finite certificates where the statement is computational:

- the residue-class coordinate description with TauCeti's code: `x / √8`, for integral `x`, lies in
  the lattice exactly when the coordinate-sum condition modulo eight holds and every residue-class
  word lies in `BinaryGolay.code`;
- the code generated by the parity extension of the first twelve shifts of
  `1 + X + X^5 + X^6 + X^7 + X^9 + X^11` equals `BinaryGolay.code` after a coordinate permutation;
- the 24 published basis rows, divided by `√8`, span the lattice after a coordinate permutation, and
  their integer matrix has determinant `8^12`.

The published rows are not in the cyclic code's coordinates: eleven of them fail its residue-class
condition.  Each comparison names its permutation; none is an identification by definition.

### PR I4 — kissing number and theta identity

Import `TauCeti.kissingNumber_leechLattice` and `TauCeti.ncard_vectorsOfNorm_four_leechLattice`
from `Rank24/Leech/MinimalVectors.lean`, which count by direct enumeration independently of theta
theory, and transport the count to the real shell of squared norm `4` through
`Leech.representationNumber_lattice`.  After G3, derive the theta identity.  Neither result is an
input to optimality.

## 12. Phase J — common analytic tools for the magic functions

### PR J1 — radial squared-norm profiles

Add `RadialSchwartzMap.ofNormSq`, evaluation/coercion lemmas, and its compatibility with the
Fourier eigenspace operations.

### PR J2 — signed transformation laws of the modular kernels

State the exact signed transformation laws under `z ↦ -1/z` satisfied by the kernels of each
concrete `+1` and `-1` component, in the form the Layer 8 contour theorems use directly.  The
Fourier sign occurs in the transformation law and determines the resulting eigenvalue; there is
no structure packaging kernel data, no shared constructor, and no free complex eigenvalue
parameter.

### PR J3 — integration and differentiation lemmas

Collect:

- integrability of parameterized Gaussian kernels;
- Fubini/Tonelli interchanges;
- differentiation under the integral;
- Schwartz decay from q-expansion Big-O estimates;
- TauCeti's predicates for functions on the imaginary axis.

### PR J4 — segment integrals, scalar one-forms, and change of variables

Add the following curve-integral definitions and results:

- the scalar one-form `F(z) dz` of a complex function;
- the identification of Mathlib curve integrals along a segment with parametrized interval
  integrals;
- change of variables along a segment, with a genuine derivative (chain-rule) hypothesis;
- the structure recording that a one-form is closed, and the implication that a function
  complex-differentiable (holomorphic) on a set and continuous on its closure has a closed scalar
  one-form there (the converse is not a target).

### PR J5 — the inversion `z ↦ -1/z`, the wedge, and the signed permutations

Prove the main result for finite contours:

- the inversion `z ↦ -1/z`, its derivative, and its action on the upper half-plane;
- openness and convexity of the wedge, and the fact that its closure meets the real axis only at
  `1`;
- the two signed contour-permutation theorems for a single pair of kernels, via Mathlib's
  Poincaré lemma for curve integrals;
- the general left/right and central-pair Fourier identities and the six-piece assembly, using
  the Fubini and Gaussian lemmas of J3.

Radial families are special cases of the single-pair statements; the homotopies inside the wedge
are proof devices, not public declarations.

### PR J6 — deformation of half-infinite rectangles

Prove the main result for unbounded contours: deformation of a horizontal edge into the two
vertical half-lines above its endpoints, with explicit integrability on the half-lines and the top
edge controlled by uniform decay or by convergence of the top-edge integrals.  This PR is
independent of J4–J5.

Across J4–J6, keep the two kinds of contour deformation separate:

- deformation of half-infinite rectangles at infinity;
- finite deformation inside the wedge, via the Poincaré lemma.

Do not force the two into one general contour framework; no circular-arc contour is a target.

## 13. Phase K — port the E8 proof from `gauss2`

Each PR adapts proofs from a named source range and is rebased onto current `main`.

### PR K1 — E8 `a` Fourier permutation

Port the completed integral/Fourier interchange and contour identities for the `+1`
eigencomponent.  Replace duplicate generic Fourier involution by
`RadialSchwartzMap.fourier_apply_apply`.

### PR K2 — E8 `b` Fourier permutation

Do the analogous migration for the `-1` eigencomponent through the common radial Schwartz lemmas.

The production source has a sign error to correct, not port.  At the pinned commit `bad3de9`
(and on production `main` as of 2026-11-17), `SpherePacking/MagicFunction/b/Basic.lean` defines
`J₆' := 2 * ∫ t in Ici 1, Ψ₆ x t`.  Viazovska's (52) and the production blueprint
(`construct-a-b.tex`) have `-2 ∫_i^{i∞} ψ_S …`.  With `+2`, `𝓕 J₅ = +J₆` and `b(0) ≠ 0`, so the
function is not a `-1` eigenfunction; production's `perm_J₅ : 𝓕 J₅ = -J₆` and `b_zero` are both
`sorry` there.  Open Sphere-Packing-Lean #504 changes `J₆'` to `-2 * ∫ …`.  The ray kernel `E8.minusKernelRay` follows the paper.  `Pinned.lean` stays frozen,
so the migration must account for the production correction explicitly.

### PR K3 — E8 Schwartz and special values

Port and clean the full Schwartz proof, normalization at zero, and lattice-shell zeros.  For `b`,
use the corrected `J₆` of PR K2: `b(0) = 0` fails for the production definition at `bad3de9`.

### PR K4 — E8 sign and exact zeros

Prove weak signs for optimality and strict signs/exact zero sets for rigidity.  Preserve zero
multiplicity and quantitative estimates needed by the stability roadmaps recorded in
`UPSTREAM.md`.

### PR K5 — E8 certificate and numerical bound

Assemble the final auxiliary function as
`((π * I) / 8640) • magicPlus - (I / (240 * π)) • magicMinus`, Viazovska's `g` for `b` defined by
(52).  Theorem 4 of arXiv:1603.04246 prints `+`, consistently with its (58) but not with
(52)–(53); the `ψ_I` coefficient of (62) forces `-` (see `E8.magicProfile`).  Production
`MagicFunction.g` at `bad3de9` has `+`, with the uncorrected `J₆`; Sphere-Packing-Lean #504
corrects both.  Derive its distinct Fourier
transform from the two component eigenvalue theorems, package the certificate, and prove its bound
equals `π^4/384`.

### PR K6 — E8 optimality main theorem

The main theorem has a short lower-bound/upper-bound `le_antisymm` proof.

## 14. Phase L — Leech magic function

Phase L follows Phase K for the Leech lattice, using the same common definitions and lemmas with
the dimension-24 kernels and modular forms, but does not copy E8 files wholesale.  Each file must
make clear which theorem is common and which modular identity is specifically 24-dimensional.

### PR L1 — dimension-24 modular forms and q-expansions

Define only the Leech-specific weakly holomorphic/quasimodular inputs and prove their finite
q-expansions, transformation laws, growth at the cusp, and reality on the imaginary axis, using
TauCeti's common results.

### PR L2 — the contour identities in dimension 24

Specialize the general contour results to the 24-dimensional kernels: the signed transformation
laws under `z ↦ -1/z`, closedness of the relevant one-forms on the wedge, the Fubini/Tonelli
interchanges, and the Gaussian Fourier transforms used by the component constructions below.
Import TauCeti's contour theorems only where their statement matches the actual geometry.

### PR L3 — +1 Fourier eigencomponent

Construct the `+1` Fourier eigencomponent through its defining formula as a six-piece contour
integral, so that the general left/right and central-pair Fourier identities apply to it.
Keep its normalization and contour decomposition explicit.

### PR L4 — −1 Fourier eigencomponent

Construct the `-1` Fourier eigencomponent in the same way, through its defining formula.  Reverse
permutations must use the radial Fourier involution rather than duplicate Fourier inversion.

### PR L5 — Schwartz estimates

Establish smoothness and rapid decay of every radial piece and the assembled functions.  Reuse the
q-coefficient/Big-O cusp dictionary and preserve quantitative bounds useful for the stability
roadmaps recorded in `UPSTREAM.md`.

### PR L6 — special values and exact shell zeros

Prove normalization at zero, all direct and Fourier shell zeros, their multiplicities where known,
and the absence of additional zeros in the sign ranges.

### PR L7 — strict signs and certificate

Assemble the final auxiliary function as
`-((π * I) / 113218560) • magicPlus - (I / (262080 * π)) • magicMinus`, derive its distinct
Fourier transform, prove the weak sign hypotheses for optimality and strict sign hypotheses for
equality rigidity, and package the resulting `CohnElkies.Certificate 24 2` together with the
equation identifying its function `f`.

### PR L8 — candidate comparison and Leech optimality main theorem

Prove lattice sharpness, identify the certificate bound with `π^12 / 12!` through the candidate
density, and assemble the Leech lower and upper bounds in a short `le_antisymm` theorem.  No
contour, q-expansion, or sign calculation belongs in the main-theorem file.

## 15. Phase M — algebraic uniqueness in TauCeti-facing form

The reusable classification results have TauCeti's IntegralLattices roadmap extension as their
intended home.  They are required dependencies of this roadmap: if TauCeti has not provided them
when the uniqueness proofs need them, production proves them locally, with exactly the intended
statements, and replaces the local proofs by imports once TauCeti provides the results.

### PR M1 — rank-eight even-unimodular uniqueness

Target:

```text
Every positive-definite even unimodular integral lattice of rank 8 is isometric to E8.
```

TauCeti proves this, theta-independently and for the same `typeE₈RootLattice`, as
`TauCeti.IntegralLattice.IsPosDef.nonempty_isometry_typeE₈RootLattice_of_isEven`
(`PosDef/SmallRankUnimodular.lean`).  SphereCeti's `E8.even_unimodular_rank_eight_unique` is that
theorem with the isometry reversed and the rank converted by `IntegralLattice.finrank_carrier`; no
local classification proof is needed, and M1 does not depend on G3.  The theorem does not mention
sphere packings.

### PR M2 — rootless rank-24 uniqueness

Target:

```text
Every positive-definite even unimodular rootless rank-24 lattice is isometric to Leech.
```

Use Niemeier classification.  Define the exact 24-case type: Leech and the 23 root systems
`A1^24`, `A2^12`, `A3^8`, `A4^6`, `A5^4 D4`, `A6^4`, `A7^2 D5^2`, `A8^3`, `A9^2 D6`,
`A11 D7 E6`, `A12^2`, `A15 D9`, `A17 E7`, `A24`, `D4^6`, `D6^4`, `D8^3`, `D10 E7^2`,
`D12^2`, `D16 E8`, `D24`, `E6^4`, and `E8^3`.  The classification development constructs each
canonical lattice from its root system and glue code and produces an integral-lattice isometry.
Prove the criterion that the norm-two root set is empty if and only if the classified case is
Leech, then derive the rootless uniqueness target.

The classification sources are Niemeier, *Journal of Number Theory* 5 (1973), 142–178, and
Conway–Sloane, Chapter 16, §1 and Table 16.1 plus §3.  The root-system proof and the rootless
characterization follow Conway–Sloane, Chapter 18, §§2–5, especially §5.

Do not postulate the theorem as an opaque axiom in production.

## 16. Phase N — equality and periodic rigidity

### PR N1 — generated lattice from an equality configuration

For a canonical-separation optimal periodic packing:

- translate one center to zero;
- prove all nonzero pairwise differences have squared norm in the exact even shell spectrum;
- use polarization to prove integral inner products;
- form the generated additive subgroup;
- prove discreteness and full rank.

### PR N2 — Cohn–Elkies quotient and covolume squeeze

Do **not** argue that evenness by itself makes the generated lattice a valid Leech-scale
superpacking.  Instead formalize the exact Section-8 argument:

- the original period lattice maps into the generated lattice;
- define an explicit embedding from the canonical center-orbit quotient into the generated
  lattice modulo the period lattice;
- establish discreteness and full rank of the generated lattice, hence finiteness of the relative
  quotient;
- only then derive `numOrbits ≤ relIndex period generated` from the embedding;
- Mathlib's covolume/index theorem rewrites that relative index as a covolume ratio;
- the generated lattice has a full integral Gram matrix with nonzero integer determinant, so the
  determinant/covolume bridge gives `1 ≤ covolume generated`;
- at the canonical normalization, optimal density says the center density is one, equivalently
  `covolume period = numOrbits`;
- the inequalities squeeze the relative index to `numOrbits` and the generated covolume to one.

This PR must expose the quotient injection, determinant lower bound, and numerical squeeze as
separate reusable lemmas.
The cardinal inequality must carry the generated-lattice discreteness/full-rank hypotheses and use
the inclusion `periodLattice_le_generatedIntegralLattice`: without them the relative quotient can be
infinite and Mathlib's `relIndex` is zero.

### PR N3 — every generated-lattice coset is occupied

From equality of the quotient cardinalities, prove that the finite pattern occupies every coset of
the period lattice in the generated lattice.  Deduce

```text
translated centers = generated lattice.
```

Now—and only now—the packing separation transfers to all nonzero generated-lattice vectors.  Thus
the minimum squared norm is at least `2` in the E8 normalization and at least `4` in the Leech
normalization.  The latter is the rootlessness input needed by M2.

The Fourier structure-factor conditions from F4 remain available as an independent equality
description, but Cohn–Elkies' exact periodic uniqueness argument does not need restrictions on the
Fourier-side root set.

### PR N4 — E8 periodic uniqueness

Show the generated rank-eight lattice is positive-definite, even, unimodular, and has the inherited
minimum norm; invoke M1; transport back through translation and scale to `IsSimilar E8.packing`.

### PR N5 — Leech periodic uniqueness

Show the generated rank-24 lattice is positive-definite, even, unimodular, and rootless using the
center-set equality from N3; invoke M2; transport back to `IsSimilar Leech.packing`.

### PR N6 — lattice uniqueness corollaries

State the cleaner lattice-packing versions and connect them to the classical uniqueness among
lattices results.

## 17. Phase O — final assembly and cleanup

### PR O1 — dimension-8 main-theorem module

Imports only stable API modules; proves the numerical constant, optimality, and periodic/lattice
uniqueness.

### PR O2 — dimension-24 main-theorem module

Analogous.

### PR O3 — compatibility removal

Remove the deprecated `numReps` and `numReps'` aliases and the duplicate representative
construction after D3 migrates the declarations that use them.  Delete `CohnElkies/Prereqs.lean`
after E1–E2 and F1 supply its replacements.  Remove every other compatibility alias only when an
earlier PR names both its canonical replacement and every migrated use.

### PR O4 — upstream issue creation

Turn `UPSTREAM.md` entries that have concrete uses and stable APIs into GitHub issues in the
appropriate repository.  This PR changes only the links and status recorded in `UPSTREAM.md`, not
production mathematics.

## 18. Parallelization map

After A1:

- B1–B3 can proceed independently of C1–C4.
- C1/C2 can proceed in parallel with D1/D2, but C4 is needed before lattice theta classification.
- E1/E2 can proceed in parallel with D3/D4.
- G1/G2 can begin once E1 and C2 exist.
- H1 can begin immediately after C2, and H2 immediately after H1; only H3 waits for G3.
- I1–I3 can run in parallel with E/F/G and the E8 magic-function port; only I4's theta identity
  waits for G3.
- J1–J6 can run in parallel with G and Leech lattice construction; J6 is independent of J4–J5.
- K can start after J foundations and F1; K5 waits for F2/F3.  K6 does not wait for H3.
- L1–L7 can start after J foundations and F1, in parallel with the Leech lattice package;
  L8 waits for I1/I2 and the generic lattice/periodic bound, not for I3, I4, or G.
- M1 is supplied by TauCeti's classifier; the E8 uniqueness argument that uses it needs only the
  lattice bridges, not G3 or the magic function.
- M2 can proceed once the transported Leech lattice and the required classification results exist;
  it does not wait for the magic function.
- N1–N3 wait for F4 plus the dimension-specific exact zero results, and do not wait for M1/M2;
  N4 additionally waits for M1, N5 for M2, and N6 follows from N4/N5.

## 19. PR description template

Every nontrivial PR must state:

```text
Mathematical topic:
Dependency/stacking:
Public declarations added or changed:
Compatibility aliases:
Automation attributes and behavior-checking examples:
Source provenance (if adapted):
Axiom/sorry delta:
Downstream roadmap targets discharged:
```

A green build alone does not establish that a refactor preserved the intended normalization; the
checks of the mathematical conventions are part of acceptance; notation linting alone is not enough.
