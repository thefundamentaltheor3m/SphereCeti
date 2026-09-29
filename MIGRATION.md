# Main-first migration and PR sequence

This file translates the mathematical layers in `README.md` into production-sized changes against
`thefundamentaltheor3m/Sphere-Packing-Lean/main`.  It is not a license to merge the historical
`gauss2` branch or PR #420 wholesale.

The standing rule is:

> Every production branch starts from current `main`, unless its PR description names one immediate
> predecessor on which it is intentionally stacked.

The SphereCeti roadmap repository is downstream documentation and target-signature checking.  The
mathematics lands in Sphere-Packing-Lean, TauCeti, or Mathlib according to the division recorded
in `UPSTREAM.md`.

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
10. The full project builds at the PR head; roadmap target signatures are updated in the same PR or
    an immediately following SphereCeti PR.

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
| PR #420 | Split into summability, duality, Poisson, and Cohn--Elkies PRs |

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
Lean       v4.35.0-rc3
TauCeti    1308f316bc62983c8350ec69f0a03dec25dbbbff
Mathlib    b2bf051988bf69448bce88722cc09a05fea31662
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
`numOrbits` as its `Fintype.card`.  Prove `FundamentalPattern.card_eq_numOrbits`, migrate the
declarations that use the old counts, define `centerIntensity` as `numOrbits / covolume`, deprecate
`numReps` and `numReps'`, then remove the duplicate representative code in PR O3.

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

Adapt proofs from PR #420, but split it.

### PR E1 — Schwartz lattice summability

Add generic theorems for:

- summability over a full lattice;
- translated Schwartz functions;
- uniform/local estimates needed by Poisson;
- finite-dimensional Euclidean specialization.

### PR E2 — real dual-lattice lemmas

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
it relies instead on the real Poisson summation theorems.

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

This phase can run in parallel with the magic-function port after E3/C4.  Duality of real
lattices, Poisson summation, lattice theta series with their transformation laws, and the
classifications in ranks 8 and 24 are to be developed in the TauCeti ThetaSeries roadmap;
SphereCeti uses them.

### PR G1 — temporary ThetaSeries statements

Add temporary copies of the ThetaSeries roadmap's target statements, stated exactly as there:
`dual`, `poissonSummation` with its two summability lemmas, `shell`/`repNum`, real-lattice
`IsEven`/`IsUnimodular`, `thetaSeries`, `thetaSeries_neg_inv`, `thetaForm` with its coercion and
q-expansion coefficients, `thetaForm_eq_E₄`, `repNum_two_rank_eight`, `thetaForm_rank_24`, and
`coe_thetaForm_rank_24_rootless`.  These copies are deleted and replaced by imports from TauCeti
when the corresponding TauCeti implementation lands; they are not to be developed into a second
general theory.

### PR G2 — comparison with integral presentations

Relate integral presentations to the roadmap's vocabulary for real lattices: evenness,
unimodularity, the equality of duals `EuclideanLattice.dual = ThetaSeries.dual`, and the
identification of the root count with a shell coefficient,
`rootCard = repNum 2 = thetaEvenCoeff 1`.  Construct shells as `Finset`s after supplying
discreteness; do not use the zero-on-infinite-sets behavior of `Set.ncard`.

### PR G3 — E8/Leech theta corollaries

Derive, through these comparisons, the three corollaries used by the E8 and Leech lattice
packages:

```text
rank 8 even unimodular: Θ = E₄
rank 24 even unimodular: Θ = E₄³ + (N₂ - 720) Δ
rootless rank 24: Θ = E₄³ - 720 Δ
```

## 10. Phase H — E8 as a fully bridged object

### PR H1 — bridge results without splitting the E8 file

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
- weight enumerator facts actually used by the lattice proof.

This material is a leading candidate for a TauCeti coding-theory roadmap; choose names in the form
intended for upstream.

### PR I2 — extended Golay code

Construct it as the row span of the parity extension of the first 12 shifts of
`1 + X + X^5 + X^6 + X^7 + X^9 + X^11`.  Verify dimension `12`, cardinality `2^12`, self-duality,
doubly-evenness, minimum weight `8`, the all-one word, and weight enumerator
`1 + 759 X^8 + 2576 X^12 + 759 X^16 + X^24`.  Check the cyclic indexing and independence through
explicit executable row-weight and unitriangular-pivot certificates.

### PR I3 — Leech coordinate/glue construction

Define the actual Leech lattice as the `1 / sqrt 8` scaling of integral vectors whose coordinate
sum and residue-class words satisfy the pinned modulo-eight/Golay conditions.  Prove the exact
membership theorem, closure, integrality, evenness, rootlessness, and the minimum-norm lower bound
from that coordinate description.  This is not naive unshifted Construction A.

### PR I4 — Leech Gram presentation

Use the pinned 24-row integer matrix divided by `sqrt 8`.  Prove that every row lies in the
coordinate lattice and that their integer span is exactly that lattice, then construct the integral
presentation directly from those rows.  Check its determinant `8^12` with an explicit finite
certificate suitable for kernel verification.  Do not introduce a second opaque lattice submodule.

### PR I5 — unimodularity, theta, and packing

Prove:

- positive-definite, even, unimodular;
- minimum squared norm `4`;
- theta identity and first shell `196560`;
- covolume one;
- canonical unit-ball packing and density.

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

Prove the curve-integral change-of-variables results:

- the scalar one-form `F(z) dz` of a complex function;
- the identification of Mathlib curve integrals along a segment with parametrized interval
  integrals;
- change of variables along a segment, with a genuine derivative (chain-rule) hypothesis;
- the structure recording that a one-form is closed, and the implication that a function
  differentiable on a set and continuous on its closure has a closed scalar one-form there (the
  converse is not a target).

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
independent of J4--J5.

Across J4--J6, keep the two kinds of contour deformation separate:

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

### PR K3 — E8 Schwartz and special values

Port and clean the full Schwartz proof, normalization at zero, and lattice-shell zeros.

### PR K4 — E8 sign and exact zeros

Prove weak signs for optimality and strict signs/exact zero sets for rigidity.  Preserve zero
multiplicity and quantitative estimates needed by the stability roadmaps recorded in
`UPSTREAM.md`.

### PR K5 — E8 certificate and numerical bound

Assemble the final auxiliary function as
`((π * I) / 8640) • magicPlus - (I / (240 * π)) • magicMinus`, derive its distinct Fourier
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

### PR L3 — direct-side radial function

Construct the `+1` Fourier eigencomponent through its defining formula as a six-piece contour
integral, so that the general left/right and central-pair Fourier identities apply to it.
Keep its normalization and contour decomposition explicit.

### PR L4 — Fourier-side radial function

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
when the uniqueness proofs need them, prove them locally in SphereCeti with exactly the intended
statements; the local statements and proofs are deleted once TauCeti provides the results.

### PR M1 — rank-eight even-unimodular uniqueness

Target:

```text
Every positive-definite even unimodular integral lattice of rank 8 is isometric to E8.
```

Use the following constructive route rather than a mass-formula argument:

- theta identity supplies 240 roots;
- prove the norm-two roots are a finite crystallographic root system and span rank eight;
- decompose the root system into valid irreducible ADE components, with the `A` and `D` index
  ranges represented explicitly;
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
Prove the criterion that the norm-two root set is empty if and only if the classified case is
Leech, then derive the rootless uniqueness target.

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

### PR O1 — dimension-8 main-theorem module

Imports only stable API modules; proves the numerical constant, optimality, and periodic/lattice
uniqueness.

### PR O2 — dimension-24 main-theorem module

Analogous.

### PR O3 — compatibility removal

Remove the deprecated `numReps` and `numReps'` aliases and the duplicate representative
construction after D3 migrates the declarations that use them.  Delete `CohnElkies/Prereqs.lean`
after E3--E4 and F1 supply its replacements.  Remove every other compatibility alias only when an
earlier PR names both its canonical replacement and every migrated use.

### PR O4 — upstream issue creation

Turn `UPSTREAM.md` entries that have concrete uses and stable APIs into GitHub issues in the
appropriate repository.  This PR changes only the links and status recorded in `UPSTREAM.md`, not
production mathematics.

## 18. Parallelization map

After A1:

- B1--B3 can proceed independently of C1--C4.
- C1/C2 can proceed in parallel with D1/D2, but C4 is needed before lattice theta classification.
- E1/E2 can proceed in parallel with D3/D4.
- G1/G2 can begin once E3 and C2 exist.
- H1 can begin immediately after C2; H2 waits for G3.
- I1/I2 can run in parallel with E/F/G and the E8 magic-function port.
- J1--J6 can run in parallel with G and Leech lattice construction; J6 is independent of J4--J5.
- K can start after J foundations and F1; K5 waits for F2/F3.
- L1--L7 can start after J foundations and F1, in parallel with the Golay/Leech lattice package;
  L8 waits for I5 and the generic lattice/periodic bound.
- M1 can proceed once TauCeti lattice bridges and E8 root data are available; it does not wait for
  the magic function.
- M2 can proceed once Leech/Golay and the required classification results exist; it does not
  wait for the magic function.
- N1--N3 wait for F4 plus the dimension-specific exact zero results, and do not wait for M1/M2;
  N4 additionally waits for M1, N5 for M2, and N6 follows from N4/N5.

## 19. PR description template

Every nontrivial PR must state:

```text
Mathematical statement:
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
