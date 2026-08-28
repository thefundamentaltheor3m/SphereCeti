# Main-first migration and PR sequence

This file translates the mathematical layers in `README.md` into production-sized changes against
`thefundamentaltheor3m/Sphere-Packing-Lean/main`.  It is not a license to merge the historical
`gauss2` branch or PR #420 wholesale.

The standing rule is:

> Every production branch starts from current `main`, unless its PR description names one immediate
> predecessor on which it is intentionally stacked.

The SphereCeti roadmap repository is downstream documentation and target-signature checking.  The
mathematics lands in Sphere-Packing-Lean, TauCeti, or Mathlib according to the boundary in
`UPSTREAM.md`.

## 1. Migration invariants

Every PR must preserve the following unless its title explicitly changes one of them.

1. `SpherePacking` stores center separation, and balls have half that radius.
2. Geometric density is `ℝ≥0∞` and infinite density is a limsup.
3. E8 remains available through its current public declarations during migration.
4. The Fourier kernel is Mathlib's `exp(-2πi⟪x,ξ⟫)` convention.
5. Public names receive compatibility aliases before removal.
6. No new theorem imports a tactic test file through the production root.
7. No hard proof is mixed with a tree-wide file move.
8. No source material mined from `gauss2` or PR #420 is copied without a provenance note.
9. `@[simp]`, `@[grind]`, and `@[fun_prop]` changes include focused contract examples.
10. The full project builds at the PR head; roadmap target signatures are updated in the same PR or
    an immediately following SphereCeti PR.

## 2. Material disposition

| Existing material | Disposition |
|---|---|
| `Basic/SpherePacking.lean` definitions | Preserve statements and semantics |
| scaling theorems | Preserve; add safe simp attributes |
| periodic density proof | Preserve mathematics; replace exposed implementation details |
| `Basic/E8.lean` | Preserve mathematical content; split only after adapters land |
| `ForMathlib/RadialSchwartz/*` | Make canonical common Fourier layer |
| Jacobi theta, E2/E4/E6, Δ, Serre derivative | Preserve; converge generic APIs with TauCeti |
| `MagicFunction/a`, `b`, `g` | Preserve E8 proof content; move generic pieces out incrementally |
| `CohnElkies/Prereqs.lean` | Retire after genuine Poisson/dual API lands |
| root aggregator test imports | Remove immediately |
| `numReps'` and basis-dependent public counting | Migrate to one orbit API |
| heterogeneous `NNReal`/`ENNReal` global instances | Remove in a focused PR |
| full periodic density formula marked `@[simp]` | Remove attribute; retain named theorem |
| `gauss2` completed theorem | Port theorem-by-theorem after foundations |
| PR #420 | Split into summability, duality, Poisson, and Cohn--Elkies PRs |

## 3. Phase A — establish the exact dependency line

### PR A0 — SphereCeti roadmap bootstrap

**Repository:** `thefundamentaltheor3m/SphereCeti`

Create the roadmap package with:

- exact Lean/TauCeti/Mathlib pins;
- `README.md`;
- `SphereCeti/Suggested.lean`;
- the temporary `Pinned.lean` compatibility model;
- convention, migration, provenance, and upstream ledgers;
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
Lean       v4.34.0-rc1
TauCeti    8671bee98125933c56b9b00a08ded873b77dd23b
Mathlib    618f225e1ff4a6b2790a944e01b806b7c68bdc56
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
- the summit theorem retains its statement;
- Fourier Gaussian normalization contract passes;
- no dependency has an unpinned branch revision.

### PR A2 — direct SphereCeti imports

**Repository:** `SphereCeti`

Add `Sphere-Packing-Lean` as an exact dependency at the migrated production commit.  Replace
`SphereCeti.Pinned` imports and temporary declarations with exact production imports.  Delete
`Pinned.lean` in full.

Acceptance:

- every `#check` in `Suggested.lean` resolves to production or pinned TauCeti declarations;
- no duplicate `SpherePacking`, `PeriodicSpherePacking`, or `RadialSchwartzMap` remains;
- the manifest records exact commits for both dependencies.

## 4. Phase B — stabilize the existing public boundary

### PR B1 — import hygiene

Split:

```text
SpherePacking.lean       -- production modules only
SpherePackingTests.lean  -- tactic and contract tests
```

Do not change proofs beyond import fallout.

### PR B2 — core packing API polish

Add:

- directional center-separation theorem with a clean proof;
- `density_le_SpherePackingConstant`;
- `density_le_PeriodicSpherePackingConstant`;
- safe `[simp]` constructor projections;
- `[simp]` on positive scale density and scale-to-packing projections;
- basepointed finite density and a proof that upper density is basepoint-independent;
- transport by real affine isometries, with characteristic center and separation equations;
- `IsCongruent` and `IsSimilar` with reflexive/symmetric/transitive API;
- positive density implies that the center set is nonempty.

The periodic `scale_density` target has no dimension-positivity hypothesis.  Translation invariance
must pass through basepoint independence rather than a finite-density rewrite at the origin.

Do not expand the full density formula under `simp`.

### PR B3 — root declaration and namespace contracts

Add a small contract module checking:

- public declaration names and namespaces;
- separation/radius semantics;
- E8 normalization;
- Fourier convention;
- no test module in the production import graph.

This is intentionally separate from B2 to give downstream refactors a stable tripwire.

## 5. Phase C — the real/rational lattice bridge

This phase can begin in parallel with the periodic refactors after A1.

### PR C1 — Euclidean norm shells

Add a generic Euclidean lattice namespace with:

- `normSqShell`;
- `minNormSq` or a predicate expressing a lower bound;
- finiteness of bounded shells;
- shell transport under linear isometries;
- membership simp lemmas;
- minimum-norm grind rules.

No TauCeti dependency is needed yet beyond the project-wide pin.

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

- Mathlib's real inner-product dual lattice;
- TauCeti's rational dual carrier.

Construct integral equivalences between the real carrier/dual and TauCeti's carrier/dual carrier.
Prove real-dual membership equivalence through the rational dual-carrier coordinates and transport
unimodularity, rootlessness, and exact norm shells.

### PR C4 — discriminant/covolume compatibility

Prove:

- Gram determinant equals TauCeti determinant/discriminant;
- real covolume squared equals the nonnegative Gram determinant;
- positive-definite unimodular presentations have covolume one;
- isometry invariance;
- every TauCeti classification isometry extends to a real linear isometry mapping carriers, and
  then to an affine isometry mapping lattice cosets.

Derive positive-definiteness from a full Euclidean presentation.  The determinant lower bound and
classification statements do not carry redundant positivity or nondegeneracy hypotheses.

Avoid global coercion instances between rational and real lattice types.

## 6. Phase D — periodic packings and density

### PR D1 — canonical lattice packing constructor

Add:

```lean
PeriodicSpherePacking.ofZLattice
```

from a full discrete Euclidean lattice, a positive separation, and a minimum-norm hypothesis.

Refactor `E8Packing` through it while preserving the existing public name and theorem statements.

### PR D2 — canonical finite pattern

Introduce one `FundamentalPattern` data type for a periodic packing:

- finite representatives of type `P.centers` in a fundamental domain;
- coverage;
- uniqueness modulo the period lattice;
- pairwise distinct orbits.

Its membership type makes separate ambient membership and action-soundness fields unnecessary.
Prove conversion from the existing representative construction.

### PR D3 — retire duplicate representative counts

Expose `Orbit` as an abbreviation for the existing `Quotient P.addAction.orbitRel` and define
`numOrbits` as its `Fintype.card`.  Prove `FundamentalPattern.card_eq_numOrbits`, migrate consumers,
define `centerIntensity` as `numOrbits / covolume`, deprecate `numReps` and `numReps'`, then remove
the duplicate representative code in PR O3.

### PR D4 — basis-free density formula

State the density formula in terms of:

- the canonical `P.numOrbits`;
- ball volume;
- lattice covolume.

Remove the global heterogeneous arithmetic instances.  Remove `@[simp]` from the large expansion.
Add explicit, short specializations for one-coset lattice packings.

### PR D5 — periodic approximation

Use translated coordinate boxes with a guard band of one center separation.  Define the finite
patch, its period lattice, and the repeated center set, then expose the characteristic equations
for the centers and separation of `ofFinitePatternInBoxAt`.  Prove in order:

- a Fubini/Følner averaging lemma: from an arbitrarily large ball whose finite density approaches
  the ball-limsup density, extract an arbitrarily large translated coordinate box whose normalized
  center count loses only a prescribed error;
- the repeated patch satisfies the packing inequality, including across adjacent boxes;
- its exact density in terms of the patch cardinality and box covolume;
- a fixed-width coordinate-box boundary layer has volume ratio tending to zero;
- for every positive `ε`, every packing has a periodic packing `Q` with
  `P.density ≤ Q.density + ε`.

Deduce:

```lean
PeriodicSpherePackingConstant d = SpherePackingConstant d
```

as its own theorem/file.  The proof does not depend on E8 or dimension-specific modular forms.

## 7. Phase E — Poisson summation

Mine PR #420, but split it.

### PR E1 — Schwartz lattice summability

Add generic theorems for:

- summability over a full lattice;
- translated Schwartz functions;
- uniform/local estimates needed by Poisson;
- finite-dimensional Euclidean specialization.

### PR E2 — real dual-lattice API

Add only the missing real-topological dual facts required by Poisson.  Reuse Mathlib's bilinear-form
dual submodule where possible, and keep the comparison to TauCeti in the bridge layer.  Provide
automatic `DiscreteTopology` and `IsZLattice` instances for the dual, together with `dual_dual` and
`covolume_dual`.

### PR E3 — unshifted Poisson summation

Prove the exact inverse-covolume formula and normalization.  Test it on the unit Gaussian and on
the self-dual covolume-one case.

### PR E4 — shifted Poisson and structure factors

Prove the translated formula

```text
Σ_{x∈Λ} f(x+a) = covol(Λ)⁻¹ Σ_{y∈Λᵛ} f̂(y) exp(2πi⟪y,a⟫)
```

and derive the finite-pattern amplitude and structure factor:

```text
A_P(y) = Σ_{s∈pattern} exp(2πi⟪y,s⟫),
S_P(y) = |A_P(y)|².
```

Prove that the phase at a dual frequency is independent of the representative of `P.Orbit`.
Record `0 ≤ S_P(y)`, `S_P(y) = 0 ↔ A_P(y) = 0`, and the exact vanishing alternative required
by periodic equality cases.

## 8. Phase F — Cohn--Elkies as a reusable theorem

### PR F1 — certificate structure

Add a nonradial `CohnElkies.Certificate d r` and its basic API:

- direct/Fourier real-valuedness;
- sign conditions;
- positivity at Fourier zero;
- scale and linear-isometry transport;
- `ofRadial` adapter.

### PR F2 — lattice and periodic bounds

Prove the lattice bound first, then the finite-pattern periodic bound.  Keep all finite sums visible
until nonnegativity is applied.

### PR F3 — unrestricted bound

Combine the periodic theorem with D5.  Retire `CohnElkies/Prereqs.lean` once all consumers use the
real Poisson API.

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

## 9. Phase G — theta series

This phase can run in parallel with the magic-function port after E3/C4.

### PR G1 — analytic theta

Define the lattice theta series with exponent `π i τ ‖x‖²`.  Prove absolute/local uniform
convergence and holomorphy.

### PR G2 — shells and q-expansion

For even integral presentations, regroup by squared norm `2n` and identify coefficients with finite
shell cardinalities.  Construct shells as `Finset`s after supplying discreteness; do not use the
zero-on-infinite-sets behavior of `Set.ncard`.

### PR G3 — theta S-transformation

Derive it from Gaussian Poisson summation.  State the even-lattice `T` law, the general
dual/covolume `S` law, and the even-unimodular level-one specialization.  The modular-form adapter
must coerce back to `latticeTheta`, and its constant and first coefficients must be exposed.

### PR G4 — level-one classification

First prove that every weight-four level-one form is a scalar multiple of `E4` and every
weight-twelve level-one form is a linear combination of `E4^3` and `Delta`.  Use those
Mathlib/TauCeti dimension results to prove:

```text
rank 8 even unimodular: Θ = E₄
rank 24 even unimodular: Θ = E₄³ + (N₂ - 720) Δ
rootless rank 24: Θ = E₄³ - 720 Δ
```

Do not use a general Sturm bound where the level-one dimension formula gives a shorter structural
proof.

## 10. Phase H — E8 as a fully bridged object

### PR H1 — split-free adapters

Without moving the large existing E8 file, add:

- integral presentation;
- associated TauCeti integral lattice;
- positive-definite/even/unimodular proofs;
- covolume-one bridge;
- shell compatibility.

### PR H2 — theta identity and shell checksum

Prove `Theta_E8 = E₄` and the cardinality `240`.  Keep the direct minimum-norm proof as the packing
input; theta is a second characterization and regression test.

### PR H3 — file split

Only after H1/H2, split the E8 development into basic, Gram/integral, packing, and theta modules,
with compatibility import shims.

## 11. Phase I — Golay and Leech

### PR I1 — binary-code prerequisites

Develop only the coding theory needed by the extended binary Golay code:

- Hamming weight and distance;
- dual code and self-duality;
- doubly-evenness;
- generator/parity-check matrices;
- weight enumerator facts actually consumed by the lattice proof.

This material is a leading candidate for a TauCeti coding-theory roadmap; use upstream-shaped names.

### PR I2 — extended Golay code

Construct it as the row span of the parity extension of the first 12 shifts of
`1 + X + X^5 + X^6 + X^7 + X^9 + X^11`.  Verify dimension `12`, cardinality `2^12`, self-duality,
doubly-evenness, minimum weight `8`, the all-one word, and weight enumerator
`1 + 759 X^8 + 2576 X^12 + 759 X^16 + X^24`.

### PR I3 — Leech coordinate/glue construction

Define the actual Leech lattice as the `1 / sqrt 8` scaling of integral vectors whose coordinate
sum and residue-class words satisfy the pinned modulo-eight/Golay conditions.  Prove the exact
membership theorem, closure, integrality, evenness, rootlessness, and the minimum-norm lower bound
from that coordinate description.  This is not naive unshifted Construction A.

### PR I4 — Leech Gram presentation

Use the pinned 24-row integer matrix divided by `sqrt 8`.  Prove that every row lies in the
coordinate lattice and that their integer span is exactly that lattice, then construct the integral
presentation directly from those rows.  Do not introduce a second opaque lattice submodule.

### PR I5 — unimodularity, theta, and packing

Prove:

- positive-definite, even, unimodular;
- minimum squared norm `4`;
- theta identity and first shell `196560`;
- covolume one;
- canonical unit-ball packing and density.

## 12. Phase J — common magic-function analytic machinery

### PR J1 — radial squared-norm profiles

Add `RadialSchwartzMap.ofNormSq`, evaluation/coercion lemmas, and transport under Fourier eigenspace
operations.

### PR J2 — sign-aware modular kernels

Expose the exact signed transformation hypotheses used by each concrete `+1` and `-1` component.
After both instances exist, extract their proven common hypotheses into a shared constructor.  Its
finite Fourier sign occurs in the transformation law and determines the resulting eigenvalue; it
has no unconstrained complex eigenvalue parameter.

### PR J3 — integration and differentiation adapters

Consolidate:

- integrability of parameterized Gaussian kernels;
- Fubini/Tonelli swaps;
- differentiation under the integral;
- Schwartz decay from q-expansion Big-O estimates;
- TauCeti imaginary-axis predicates.

### PR J4 — contour adapters

Maintain three explicit interfaces:

- TauCeti pole-free meromorphic circle Goursat;
- open rectangular deformation at infinity;
- finite convex-region/Poincare path deformation.

Do not force all three into one generic contour abstraction.

## 13. Phase K — port the E8 proof from `gauss2`

Each PR is mined from a named source range and rebased onto current `main`.

### PR K1 — E8 `a` Fourier permutation

Port the completed integral/Fourier interchange and contour identities for the `+1`
eigencomponent.  Replace duplicate generic Fourier involution by
`RadialSchwartzMap.fourier_apply_apply`.

### PR K2 — E8 `b` Fourier permutation

Do the analogous migration for the `-1` eigencomponent through the common radial API.

### PR K3 — E8 Schwartz and special values

Port and clean the full Schwartz proof, normalization at zero, and lattice-shell zeros.

### PR K4 — E8 sign and exact zeros

Prove weak signs for optimality and strict signs/exact zero sets for rigidity.  Preserve zero
multiplicity and quantitative estimates needed by the stability roadmaps recorded in
`UPSTREAM.md`.

### PR K5 — E8 certificate and numerical bound

Assemble the final auxiliary function as
`((π * I) / 8640) • magicPlus - (I / (240 * π)) • magicMinus`, derive its distinct Fourier
transform from the two component eigenvalue theorems, bundle the certificate, and prove its bound
equals `π^4/384`.

### PR K6 — E8 optimality summit

The summit is a short lower-bound/upper-bound `le_antisymm` proof.

## 14. Phase L — Leech magic function

Mirror Phase K at the common API boundary, but do not copy E8 files wholesale.  Each file must make
clear which theorem is common and which modular identity is specifically 24-dimensional.

### PR L1 — dimension-24 modular forms and q-expansions

Define only the Leech-specific weakly holomorphic/quasimodular inputs and prove their finite
q-expansion, transformation, cusp-growth, and imaginary-axis reality contracts through the common
TauCeti APIs.

### PR L2 — direct-side radial function

Construct the `+1` Fourier eigencomponent through the common squared-norm radial and
modular-kernel layer.  Keep its normalization and contour decomposition explicit.

### PR L3 — Fourier-side radial function

Construct the `-1` Fourier eigencomponent and prove the forward contour permutation.  Reverse
permutations must use the radial Fourier involution rather than duplicate Fourier inversion.

### PR L4 — contour and interchange theorems

Prove the finite and open-contour deformations, change-of-variables identities, Fubini/Tonelli
interchanges, and Gaussian Fourier transforms needed by L2--L3.  Import TauCeti's contour theorems
only where their statement matches the actual geometry.

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
equality rigidity, and bundle the resulting `CohnElkies.Certificate 24 2` with its characteristic
equation.

### PR L8 — candidate comparison and Leech optimality summit

Prove lattice sharpness, identify the certificate bound with `π^12 / 12!` through the candidate
density, and assemble the Leech lower and upper bounds in a short `le_antisymm` theorem.  No
contour, q-expansion, or sign calculation belongs in the summit file.

## 15. Phase M — algebraic uniqueness in TauCeti-facing form

The reusable classification results have TauCeti's IntegralLattices roadmap extension as their
intended home; prove them locally with exactly that statement shape whenever coordination or
timing requires it.  They are required dependencies of this roadmap either way.

### PR M1 — rank-eight even-unimodular uniqueness

Target:

```text
Every positive-definite even unimodular integral lattice of rank 8 is isometric to E8.
```

Use the following constructive route rather than a mass-formula argument:

- theta identity supplies 240 roots;
- prove the norm-two roots are a finite crystallographic root system and span rank eight;
- decompose the root system into irreducible ADE components;
- use total rank `8` and root count `240` to identify the unique component as `E8`;
- prove the E8 root sublattice has index one in the unimodular lattice;
- construct the integral-lattice isometry.

The source conventions are Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter VI,
§4 and Plates I--IX, together with Conway--Sloane, *Sphere Packings, Lattices and Groups*,
Chapter 4, §8.1.  The theorem does not mention sphere packings.

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
Expose the exact characteristic theorem that the norm-two root set is empty if and only if the
classified case is Leech, then derive the rootless uniqueness target.

The classification sources are Niemeier, *Journal of Number Theory* 5 (1973), 142--178, and
Conway--Sloane, Chapter 16, §1 and Table 16.1 plus §3.  The root-system proof and the rootless
characterization follow Conway--Sloane, Chapter 18, §§2--5, especially §5.

Do not postulate the theorem as an opaque axiom in production.

## 16. Phase N — equality and periodic rigidity

### PR N1 — generated lattice from an equality configuration

For a canonical-separation optimal periodic packing:

- translate one center to zero;
- prove all nonzero pairwise differences have squared norm in the exact even shell spectrum;
- use polarization to prove integral inner products;
- form the generated additive subgroup;
- prove discreteness and full rank.

### PR N2 — Cohn--Elkies quotient and covolume squeeze

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
The cardinal inequality must carry the generated-lattice discreteness/full-rank hypotheses: without
them the relative quotient can be infinite and Mathlib's `relIndex` is zero.

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
description, but Cohn--Elkies' exact periodic uniqueness argument does not need restrictions on the
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

### PR O1 — dimension-8 summit module

Imports only stable API modules; proves the numerical constant, optimality, and periodic/lattice
uniqueness.

### PR O2 — dimension-24 summit module

Analogous.

### PR O3 — compatibility removal

Remove the deprecated `numReps` and `numReps'` aliases and the duplicate representative
construction after D3 migrates their consumers.  Delete `CohnElkies/Prereqs.lean` after E3--E4 and
F1 supply its replacements.  Remove every other compatibility alias only when an earlier PR names
both its canonical replacement and every migrated consumer.

### PR O4 — upstream issue creation

Turn `UPSTREAM.md` entries that have concrete consumers and stable APIs into GitHub issues in the
appropriate repository.  This PR changes only the ledger links/status, not production mathematics.

## 18. Parallelization map

After A1:

- B1--B3 can proceed independently of C1--C4.
- C1/C2 can proceed in parallel with D1/D2, but C4 is needed before lattice theta classification.
- E1/E2 can proceed in parallel with D3/D4.
- G1/G2 can begin once E3 and C2 exist.
- H1 can begin immediately after C2; H2 waits for G4.
- I1/I2 can run in parallel with E/F/G and the E8 magic-function port.
- J1--J3 can run in parallel with G and Leech lattice construction.
- K can start after J foundations and F1; K5 waits for F2/F3.
- L1--L7 can start after J foundations and F1, in parallel with the Golay/Leech lattice package;
  L8 waits for I5 and the generic lattice/periodic bound.
- M1 can proceed once TauCeti lattice bridges and E8 root data are available; it does not wait for
  the magic function.
- M2 can proceed once Leech/Golay and the required classification infrastructure exist; it does not
  wait for the magic function.
- N1--N3 wait for F4 plus the dimension-specific exact zero results, and do not wait for M1/M2;
  N4 additionally waits for M1, N5 for M2, and N6 follows from N4/N5.

## 19. PR description template

Every nontrivial PR must state:

```text
Mathematical boundary:
Dependency/stacking:
Public declarations added or changed:
Compatibility aliases:
Automation attributes and contract tests:
Source provenance (if mined):
Axiom/sorry delta:
Downstream roadmap targets discharged:
```

A green build alone does not establish that a refactor preserved the intended normalization; the
normalization contracts are part of acceptance.
