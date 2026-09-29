# SphereCeti convention ledger

This file records choices that must not be rediscovered independently in the 8- and
24-dimensional developments.  A change to one of these conventions is an architectural change:
it requires a migration plan, explicit compatibility lemmas, and regression tests at E8 and Leech.

`README.md` remains the definitive roadmap.  This ledger fixes the notation and normalization under
which the roadmap is to be implemented.

## 1. Dependency and pinning policy

The roadmap package uses:

```text
Lean       leanprover/lean4:v4.35.0-rc3
TauCeti    1308f316bc62983c8350ec69f0a03dec25dbbbff
Mathlib    b2bf051988bf69448bce88722cc09a05fea31662
```

The Mathlib commit is not an independent choice: it is the resolved Mathlib revision in the pinned
TauCeti manifest.  The committed `lake-manifest.json` is authoritative.

Every dependency update is atomic:

1. update the Lean toolchain;
2. update the TauCeti SHA;
3. regenerate the manifest;
4. record the resolved Mathlib SHA;
5. build every `SphereCeti.*` module;
6. check required declarations and mathematical conventions as described below;
7. record any semantic changes in this file.

Never use `main`, a tag that can move, or an unrecorded local checkout as the effective TauCeti pin.

The pinned `Sphere-Packing-Lean` semantic baseline is
`bad3de916074748eb88b7d1ee6dbf9494361ad17`.  Its Lean/Mathlib 4.32 pin requires the temporary
statement-level model in `SphereCetiRoadmap/Pinned.lean`.  PR A2 deletes that model after the synchronized
4.35 migration; no production theorem may depend on two competing packing implementations.

### Declaration and convention checks

These are regression checks that a dependency upgrade preserves the mathematical interface.
They have two purposes:

- **Required declarations and their types.** Check that the intended imports supply the named
  definitions and theorems, with the expected hypotheses and conclusions. A bare `#check name`
  only checks that a name resolves and displays its type. To check an expected type as well,
  use `#check (name : ExpectedType)` or a small typed `example`. The current declaration list in
  `SphereCetiRoadmap/Suggested.lean` primarily supplies the first, weaker check; the production
  migration must also check the types on which downstream arguments rely.
- **Mathematical conventions.** Prove standard identities using the actual imported definitions
  to check Fourier signs, measures, and normalization constants; see §10 below. These checks
  concern the mathematics, not merely the choice of notation. A theorem stated with `sorry` in
  the roadmap specifies a required identity but does not verify it. The corresponding production
  checks must use proofs without new admissions.

We call these **checks of declarations and mathematical conventions**. They are more than
notation linting: a notation linter alone cannot establish that the imported operations have
the intended meaning.

## 2. Ambient Euclidean spaces

Use:

```lean
abbrev V (d : ℕ) := EuclideanSpace ℝ (Fin d)
```

The coordinate index type is `Fin d`, not an arbitrary finite type, in every statement about
packings.  General lattice and Fourier lemmas may be stated for an arbitrary finite-dimensional real
inner-product space and specialized to `V d` where packings enter.

The standard measure on `V d` is Mathlib's additive Haar/Lebesgue measure induced by the Euclidean
structure.  Covolume and Fourier transform theorems must use the same measure normalization.

## 3. Packings, separation, and sphere radius

A `SpherePacking d` stores:

- a set of centers;
- a positive **center separation** `r`;
- pairwise distance at least `r`.

The packed open balls have radius `r / 2`.  Never call the stored `separation` the sphere radius.

Standard normalizations:

| Configuration | Minimum center distance | Ball radius |
|---|---:|---:|
| E8 | `Real.sqrt 2` | `Real.sqrt 2 / 2` |
| Leech | `2` | `1` |

The scale-free packing constant ranges over all positive separations.  Intermediate equality and
rigidity statements first fix the canonical separation and prove congruence; the final
scale-free theorem uses similarity.

## 4. Density

Geometric density has codomain `ℝ≥0∞`:

```lean
SpherePacking.finiteDensity : SpherePacking d → ℝ → ℝ≥0∞
SpherePacking.density       : SpherePacking d → ℝ≥0∞
```

The infinite density is the limsup of finite densities.  Keep this definition.  Do not replace it
with a real-valued density merely to shorten the Cohn--Elkies algebra.

Use named coercion lemmas for finite real formulas, for example:

```lean
ENNReal.ofReal (Real.pi ^ 4 / 384)
ENNReal.ofReal (Real.pi ^ 12 / 12.factorial)
```

No theorem may infer global equality of center sets from equality of upper density: finite
modifications preserve the limsup.  Exact uniqueness is therefore stated for periodic packings (or
for lattices), not arbitrary packings.

## 5. Congruence and similarity

`SpherePacking.IsCongruent P Q` means that one ambient metric-space isometry equivalence carries the
center set of `P` onto the center set of `Q`, with equal separation.  Since a general Euclidean
isometry may include translation, this is the correct notion for center sets.

`SpherePacking.IsSimilar P Q` means that a positive scaling of one packing is congruent to the
other.  Similarity is the scale-free notion of equivalence used in the uniqueness theorems.

Do not identify lattices solely up to translation: a lattice is an additive subgroup through zero.
Packing uniqueness may first translate a center to zero and then produce an isometry of the
resulting lattice.

## 6. Two lattice representations and one bridge

There are two deliberately different representations.

### Real topological lattice

Where packings meet Poisson summation:

```lean
Λ : Submodule ℤ (V d)
[DiscreteTopology Λ]
[IsZLattice ℝ Λ]
```

This is Mathlib's real full-rank discrete lattice representation.  Covolume, fundamental regions,
lattice sums, and the action on periodic center sets are developed for this representation.

### Rational integral lattice

For integrality, duality, discriminant forms, gluing, and classification, use:

```lean
TauCeti.IntegralLattice W
```

in a rational ambient space.  TauCeti's predicates `IsEven`, `IsUnimodular`, `IsPosDef`, and its
notion of isometry are the ones used throughout.

### Bridge

A real Euclidean lattice is connected to the rational theory through an explicit finite
`IntegralPresentation` containing:

- a `ℤ`-basis of the real lattice;
- an integral symmetric Gram matrix;
- the equality between that matrix and the real inner products;
- the associated TauCeti Gram lattice;
- a real/rational comparison map.

Do not create a second global predicate called `IsIntegral` on real lattices.  Integrality is a
property of a presentation and then a theorem about the associated TauCeti lattice.

The bridge must compare:

- real and rational Gram matrices;
- real dual lattice and TauCeti dual carrier;
- determinant, discriminant, and real covolume;
- real isometry and integral-lattice isometry;
- minimum norm and finite shells.

## 7. Dual lattices

For a real lattice in `V d`, use the inner-product dual:

```text
Λ* = {y | ∀ x ∈ Λ, ⟪y, x⟫_ℝ ∈ ℤ}.
```

For a TauCeti integral lattice, use `L.dualCarrier`, defined from the rational bilinear form.

Every theorem crossing the two notions must name the presentation that identifies them.  Do not
let typeclass inference choose a bilinear form or a presentation.

A Fourier-side Poisson theorem uses the real dual lattice.  A unimodularity classification theorem
uses TauCeti's dual carrier.  The bridge is what permits the same concrete E8 or Leech lattice to
be used in both settings.

## 8. Covolume and determinant

For a full Euclidean lattice, covolume is the Haar volume of a fundamental domain.  It is
basis-independent and nonnegative.

For an integral presentation with Gram matrix `G`:

```text
covol(Λ)^2 = |det G|.
```

For a positive-definite integral lattice, unimodularity gives `|det G| = 1` and hence covolume `1`.
The square-root and positivity steps must be named theorems; avoid relying on `nlinarith` to infer a
choice of square root through hidden nonnegativity.

## 9. Minimum norms and shells

Use squared norms for algebraic shell indexing:

```lean
EuclideanLattice.normSqShell Λ a := {x : Λ | ‖(x : V d)‖ ^ 2 = a}
```

For an even integral lattice, use natural half-norm coefficients:

```text
shell n = {x | ‖x‖² = 2n}.
```

Standard data:

- E8: minimum squared norm `2`; shell `n = 1` has cardinality `240`.
- Leech: minimum squared norm `4`; shell `n = 1` is empty; shell `n = 2` has cardinality `196560`.

Membership simp lemmas are appropriate; full shell-classification or cardinality theorems are not
simp rules.

## 10. Fourier transform

Use Mathlib's real inner-product Fourier transform with kernel

```text
exp(-2 π i ⟪x, ξ⟫).
```

Under this convention the Gaussian

```text
x ↦ exp(-π t ‖x‖²),  t > 0,
```

transforms to

```text
t^(-d/2) exp(-π ‖ξ‖²/t).
```

Regression tests must include:

1. the kernel sign, through its defining identity or a shifted/modulated test function;
2. the one-dimensional Gaussian;
3. the `d`-dimensional Gaussian factor;
4. Fourier involution on even/radial Schwartz maps;
5. the Poisson formula's covolume factor;
6. the theta `S`-transformation.

At `t = 1` the Gaussian is its own Fourier transform. This is a useful normalization check,
but the centered Gaussian is even and cannot by itself distinguish the two Fourier signs.

Do not define a second Fourier transform for the magic-function layer.

## 11. Radial functions and squared-norm profiles

Intrinsic radiality means factorization through `‖x‖`.  Keep
`Function.IsRadial` and `RadialSchwartzMap` at that level.

Viazovska-type formulas are naturally written as profiles in `‖x‖²`, so add an explicit constructor
such as:

```lean
def RadialSchwartzMap.ofNormSq (φ : 𝓢(ℝ, ℂ)) :
    RadialSchwartzMap ℂ (V d) ℂ
```

with an evaluation theorem.  Do not redefine radiality as factorization through squared norm.

The restricted Fourier transform on `RadialSchwartzMap` is the canonical involution, and the `+1`
and `-1` eigenspaces are defined in terms of it.  Dimension-specific `a` and `b` proofs do not
reprove generic Fourier inversion.

## 12. Poisson summation

The target normalization is:

```text
Σ_{x∈Λ} f(x + u)
  = covol(Λ)⁻¹ Σ_{y∈Λ*} f̂(y) exp(2π i ⟪y,u⟫).
```

The unshifted formula is the `u = 0` specialization.  Periodic multi-coset Cohn--Elkies arguments
need the shifted formula or an equivalent finite structure-factor formula.

Poisson summation is never a simp rule.  Name it explicitly, with lattice, measure, and Fourier
conventions visible in its type or imports.

## 13. Cohn--Elkies certificates

The generic certificate is not radial.  It contains a Schwartz function and the real/sign
hypotheses needed for the linear-programming bound.  Radiality is a constructor convenience for the
8- and 24-dimensional magic functions.

At minimum the certificate records:

- positive threshold `r`;
- real-valued direct and Fourier transforms;
- `f(x) ≤ 0` for `‖x‖ ≥ r`;
- `f̂(x) ≥ 0` for all `x`;
- `f̂(0) > 0`.

Do not carry a separate `f ≠ 0` field: positivity at Fourier zero implies nonzeroness.

The bound is normalized by the ratio `f(0)/f̂(0)` and the volume of the radius-`r/2` ball, in the
same convention as the packing definition.

Equality data are separate from the inequality certificate.  They include exact zero sets and,
for a periodic finite pattern, the direct and Fourier structure-factor terms that must vanish.

When the data for a construction are already available, the target is defined as a direct
application of its constructor, so that its defining equations hold by unfolding the definition.
In particular, the E8 and Leech certificates are literally `Certificate.ofRadial` applied to their
data, and the equations for their `f` components follow from that constructor.  A construction
whose body is not given explicitly (a `sorry`-bodied, hence opaque, definition) must come with a
theorem stating its defining equation in its structured type; do not postulate an unrelated
object together with a plausible pointwise equation.

## 14. Theta series and q-expansions

The analytic lattice theta series is

```text
Θ_Λ(τ) = Σ_{x∈Λ} exp(π i τ ‖x‖²),  Im τ > 0.
```

For even lattices, write

```text
q = exp(2π i τ)
```

and obtain

```text
Θ_Λ(τ) = Σ_{n≥0} #(x : ‖x‖² = 2n) q^n.
```

This is distinct from the existing Jacobi theta functions `Θ₂`, `Θ₃`, and `Θ₄`.  Put lattice theta
in a lattice namespace such as `EuclideanLattice.theta` or `IntegralLattice.theta`, never in the
Jacobi namespace.

For a rank-`d` real lattice:

```text
Θ_Λ(-1/τ) = (-iτ)^(d/2) / covol(Λ) * Θ_{Λ*}(τ),
```

with the power expressed in the integral-weight language available for even rank.  The exact Lean
statement must avoid an ambiguous complex square-root branch.  In ranks 8 and 24 the weights are 4
and 12, so ordinary natural powers suffice after the general Poisson identity is specialized.

Standard level-one identities:

```text
Θ_E8 = E₄
Θ_Λ24 = E₄^3 + (N₂(Λ) - 720) Δ
Θ_Leech = E₄^3 - 720 Δ.
```

## 15. Modular forms and the imaginary axis

Use TauCeti's generic

```lean
UpperHalfPlane.resToImagAxis
UpperHalfPlane.RealOnImagAxis
UpperHalfPlane.PosOnImagAxis
UpperHalfPlane.EventuallyPosOnImagAxis
```

and the lemma `UpperHalfPlane.resToImagAxis_slash_S` for the modular `S`-transformation.
Sphere-Packing's older names receive temporary compatibility aliases during migration; new code
uses the TauCeti names.

Use TauCeti's q-coefficient/Big-O dictionary for cusp decay instead of reproving coefficientwise
asymptotics in each dimension.

Use a Sturm bound only when dimension/rank-one arguments are unavailable or less natural.  For E8
and rank-24 even-unimodular theta classification, the level-one dimension formula is the preferred
proof.

## 16. E8 and Leech definitions

### E8

Keep both:

- the coordinate parity/half-integral description;
- an explicit basis/Gram description.

Prove them equal.  The direct minimum-norm proof remains independent of theta theory.

### Leech

Keep both:

- a standard Golay/glue coordinate description;
- an explicit basis/Gram description.

Prove them equal.  The naive unshifted Construction-A lattice of the extended binary Golay code has
roots and is not the Leech lattice; naming must reflect the actual glue/shift construction.

## 17. Uniqueness scopes

Use three distinct results.

### Algebraic lattice classification

Generic theorems:

```text
positive-definite + even + unimodular + rank 8  ⇒ isometric to E8
positive-definite + even + unimodular + rank 24 + rootless ⇒ isometric to Leech
```

Their intended home is TauCeti's integral-lattice ecosystem (the second either via Niemeier
classification or a narrower rootless theorem).

### Lattice packing uniqueness

An optimal lattice packing in dimension 8 or 24 is similar to the E8 or Leech lattice packing.  This
is a SphereCeti consequence combining the Cohn--Elkies equality case with algebraic classification.

### Periodic packing uniqueness

An optimal periodic packing is similar to the canonical packing.  The general equality theory for
periodic packings must retain the Fourier structure factor, but the E8/Leech uniqueness deduction
follows the more specific Cohn--Elkies Section-8 route:

1. exact direct-side roots force even integral pairwise squared distances;
2. the translated centers generate a full even integral lattice;
3. the periodic pattern injects into the generated-lattice quotient by the period lattice;
4. the integer Gram determinant gives generated covolume at least one;
5. unit center density squeezes the quotient index and covolume to equality;
6. every quotient coset is occupied, so the centers are one lattice coset;
7. the original separation yields minimum norm and, in dimension 24, rootlessness.

Do not replace step 4 by the false general claim that every even integral rank-24 lattice already
has minimum norm four.  Do not state uniqueness for all packings under limsup density.  Quantitative
local-frame stability is a separate theory and does not upgrade to literal global equality.

## 18. Automation attributes

### `@[simp]`

Use for canonical evaluation and projection:

- constructor fields;
- coercions;
- scale centers/separation/density;
- shell membership;
- squared-norm profile evaluation;
- Fourier coercion on radial Schwartz maps.

Do not use for:

- Poisson summation;
- density expansions;
- Cohn--Elkies bounds;
- theta transformations or classifications;
- contour deformations;
- exact zero-set theorems.

### `@[grind]`

Use directional rules for:

- center separation;
- lattice actions;
- orbit representative uniqueness;
- minimum-norm consequences;
- code parity/congruence consequences;
- equality-case elimination after establishing the relevant analytic equality.

Do not register analytic convergence, modular transformations, Fourier integral identities, or
nontrivial inequalities as global grind rules.

### `@[fun_prop]`

Use TauCeti's established compositional `fun_prop` lemmas for realness/positivity on the imaginary
axis, differentiability, and algebraic closure.  Add new rules only after proving the actual
analytic statement, never as a substitute for it.

Every new global attribute gets a small `example` or `#guard` check of its intended behavior in
the same PR.

## 19. Typeclass policy

Use typeclasses for canonical ambient structure:

- topology and measure structures;
- `DiscreteTopology Λ` and `IsZLattice ℝ Λ`;
- nondegeneracy when TauCeti treats it as a mixin.

Do not use typeclasses for data with multiple reasonable choices:

- a lattice basis;
- an integral presentation;
- a fundamental pattern;
- a magic modular kernel;
- a Cohn--Elkies certificate;
- an equality witness;
- a chosen E8 or Leech identification.

Explicit data prevents hidden normalization choices and brittle instance search.

## 20. Naming and file placement

Suggested production layout:

```text
SpherePacking/
  Packing/
  Lattice/
    Euclidean/
    Bridge/
    E8/
    Leech/
    Theta/
  Fourier/
  CohnElkies/
  MagicFunction/
    Common/
    E8/
    Leech/
  Rigidity/
  MainTheorems/
```

Compatibility aliases stay near the new declaration and carry deprecation metadata.  Do not add a
new public declaration merely to abbreviate a one-line proposition unless it is a stable
mathematical concept used across layers.
