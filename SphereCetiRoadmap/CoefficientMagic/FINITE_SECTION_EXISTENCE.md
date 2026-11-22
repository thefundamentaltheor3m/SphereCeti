# A finite modular certificate for coefficient existence

## Status and intended use

This is a proposed alternative to the Riemann–Roch **existence step** in
[Hexagon 2610.00330v1, *A construction of the sphere-packing magic functions in
dimensions 8 and 24*](https://hexagonmath.org/2610.00330v1). The paper constructs
coefficient solutions from six-component holomorphic functions satisfying
explicit automorphy laws and cusp conditions. Its existence argument uses the
Euler characteristic of the corresponding bundle. The construction below supplies
explicit nonzero normalized functions satisfying those same laws and conditions,
using elementary finite linear algebra and existing scalar modular/theta
infrastructure.

The finite identities have been checked independently in this research session,
and [`scripts/check_finite_sections.py`](../../scripts/check_finite_sections.py) reproduces the exact rational algebra. **This
is not Lean-verified.** In particular, the script does not verify analytic theta
transformation laws, convergence, the Cauchy boundary correspondence, or
Riemann–Roch. A successful implementation must prove those analytic facts it uses
in the native libraries.

This route should be an additional proof path in the roadmap. It establishes
neither the paper's geometric identity `χ(E_d) = 1` nor independent global sign
inequalities. The original geometric result remains a separate target.

The corresponding Lean targets are in the namespace `SphereCeti.CoefficientMagic.Witness` of
[`Suggested.lean`](Suggested.lean): `H₂`, `H₄` and their transformation laws, `V₂`, `W₄`,
`det_V₂_W₄_sq` for (7), `plusBlock` and `plusBlock_S` for (1)–(2), `sixFields` for (4),
`candidate8` and `candidate24` for (8)–(9) and (12)–(13), with their laws for every parameter
vector (`candidate8_holo`, `candidate8_translate`, `candidate8_invert`, and likewise in dimension
24), `cuspMatrix8` and `cuspMatrix24` for
(10) and (14), `witness8` and `witness24` for (11) and (15), `isGlobalSolution_candidate8` and
`isGlobalSolution_candidate24` for the passage from a null vector to the six-field laws and the
cusp table, and `normalization_section8`, `normalization_section24` for (16).  The block
splitting is `splitting_mul_glueInvert`, `splitting_mul_glueTranslate`, and
`Witness.splitting_mulVec_sixFields` in the same file.  The only statements proved there are the
rational identities `M₈ v₈ = 0` and `M₂₄ v₂₄ = 0`.  The identification of each matrix entry
with the Laurent coefficient it represents (§8 below) has no Lean statement yet.

## 1. Coordinates, derivatives, and the original six fields

Keep the paper's two power-series coordinates distinct:

\[
\mathfrak q=e^{2\pi i\tau},\qquad
q_{\mathrm{coeff}}=e^\pi e^{\pi i\tau}
                 =e^\pi\mathfrak q^{1/2}.
\]

The half-power always means `exp(π i τ)` on the upper half-plane. It is not an
arbitrary square-root branch. All coefficient extractions in this note refer to
the modular coordinate `𝔮`.

Use the normalized derivative

\[
D_0=\mathfrak q\frac{d}{d\mathfrak q}
   =\frac1{2\pi i}\frac{d}{d\tau},\qquad
\delta=2\pi i,\qquad D_\tau=\delta D_0.
\]

The production derivative API already uses the normalized convention. The
ordinary derivative in the paper's block formulas is `D_τ`, so the factors of
`δ` below are essential.

Set `k = -4` in dimension 8 and `k = -12` in dimension 24. The overall
six-component inversion weight is `k + 2`, namely `-2` or `-10`.

For scalar weakly holomorphic modular forms `F, B₀, C₀` of weights
`k, k + 2, k + 4`, define

\[
\begin{aligned}
p_0&=F,\\
p_1&=\delta\left(\frac2kD_0F+B_0\right),\\
p_2&=\delta^2\left(
 \frac{D_0^2F}{k(k+1)}+\frac{D_0B_0}{k+2}+C_0\right).
\end{aligned}
\tag{1}
\]

Equivalently, set `B = δ B₀`, `C = δ² C₀` and write

\[
p_1=\frac2kD_\tau F+B,\qquad
p_2=\frac{D_\tau^2F}{k(k+1)}+
                         \frac{D_\tau B}{k+2}+C.
\]

Differentiating `F(-1/τ) = τ^k F(τ)` gives

\[
\begin{aligned}
(D_\tau F)(-1/\tau)
 &=\tau^{k+2}D_\tau F+k\tau^{k+1}F,\\
(D_\tau^2F)(-1/\tau)
 &=\tau^{k+4}D_\tau^2F+(2k+2)\tau^{k+3}D_\tau F
                   +k(k+1)\tau^{k+2}F.
\end{aligned}
\]

Consequently (1) satisfies precisely the paper's plus-block laws:

\[
\begin{aligned}
p_0(-1/\tau)&=\tau^kp_0(\tau),\\
p_1(-1/\tau)&=\tau^{k+2}p_1(\tau)+2\tau^{k+1}p_0(\tau),\\
p_2(-1/\tau)&=\tau^{k+4}p_2(\tau)+\tau^{k+3}p_1(\tau)
                                        +\tau^{k+2}p_0(\tau).
\end{aligned}
\tag{2}
\]

All three fields are periodic under `τ ↦ τ + 1`.

For the minus block, set `m₁ = 0`, and choose `(m₀,m₂)` of weight `k + 2` for
the two-dimensional representation

\[
\rho(S)=\frac12\begin{pmatrix}-1&3\\1&1\end{pmatrix},\qquad
\rho(T)=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
\tag{3}
\]

Recover the six fields of the paper by

\[
\begin{array}{lll}
a_0=p_0+m_0,&a_1=p_1,&a_2=p_2,\\
a_3=m_2,&a_4=p_1-p_2,&a_5=p_0-m_0.
\end{array}
\tag{4}
\]

This is the inverse of the constant splitting in the paper's §8 and §11.5,
restricted to `m₁ = 0`. Thus (2)–(3), together with periodicity, imply its full
six-component gluing laws. In a Lean implementation, prove this equivalence
against the actual displayed `J_tr` and `J_inv`, rather than introducing an
unrelated bundle definition with a convenient existence field.

## 2. Explicit vector-valued theta forms

Write

\[
x=\theta_4^4,\qquad y=\theta_2^4,\qquad
a=x+y/2,\qquad b=-y/2,
\]

and define

\[
V_2=\binom a b,\qquad
W_4=\binom{-a^2+3b^2}{2ab}.
\tag{5}
\]

The relevant theta identities, in these exact conventions, are

\[
\begin{aligned}
x(-1/\tau)&=-\tau^2y(\tau),&
y(-1/\tau)&=-\tau^2x(\tau),\\
x(\tau+1)&=x(\tau)+y(\tau),&
y(\tau+1)&=-y(\tau).
\end{aligned}
\]

They imply that `V₂` has weight 2 for (3). Substituting (3) into the quadratic
polynomial defining `W₄` proves that it has weight 4 for the same representation.
This is an exact polynomial identity, not a numerical fit.

Their determinant is

\[
\det[V_2,W_4]=3b(a^2-b^2)
            =-\frac32\theta_2^4\theta_3^4\theta_4^4.
\tag{6}
\]

Using Jacobi's identity `θ₃⁴ = θ₂⁴ + θ₄⁴` and the existing identity

\[
\Delta=\frac{(\theta_2^4\theta_3^4\theta_4^4)^2}{256}
\]

gives the particularly useful certificate

\[
\boxed{\det[V_2,W_4]^2=576\Delta.}
\tag{7}
\]

Since `Δ` is nonzero on the upper half-plane, these two vectors are pointwise
independent there. This is stronger than the leading-coefficient check
`a = 1 + O(𝔮)`, `b = -8 𝔮^(1/2) + O(𝔮^(3/2))`.

Proving (5)–(7) is a useful small initial PR after the existing theta API has
been migrated to the current pinned dependencies. Reuse native `H₂`, `H₃`,
`H₄`, discriminant, and slash-action definitions; do not rebuild theta functions
or modular forms to support this calculation.

## 3. The eight-dimensional finite space

For parameters `(u,v,w,x,r,s) ∈ ℂ⁶`, choose

\[
F=u\frac{E_4^2}{\Delta},\qquad
B_0=v\frac{E_4E_6}{\Delta},\qquad
C_0=\frac{wE_4^3+xE_6^2}{\Delta},
\tag{8}
\]

\[
\binom{m_0}{m_2}
 =\frac{rE_4^2V_2+sE_6W_4}{\Delta}.
\tag{9}
\]

The weights are `-4,-2,0` in (8) and `-2` in (9), as required. The
denominator has no zeros in the upper half-plane, so these are holomorphic
there. Their only possible poles are at the modular cusp.

Write `p̃₁ = p₁/δ` and `p̃₂ = p₂/δ²`. Impose the following conditions:

| Condition | Purpose |
|---|---|
| `[𝔮⁻¹] p̃₁ = 0` | `p₁` is bounded at the cusp. |
| `[𝔮⁻¹] p̃₂ = [𝔮⁰] p̃₂ = 0` | `p₂` vanishes to order at least 1. |
| `[𝔮⁻¹/²] m₂ = 0` | `m₂` begins at exponent at least `1/2`. |
| `[𝔮⁻¹](p₀ - m₀) = 0` | `a₅` is bounded at the cusp. |

The resulting fields (4) satisfy exactly the required lower bounds on cusp orders:

\[
(a_0,a_1,a_2,a_3,a_4,a_5):\quad(-1,0,1,1/2,0,0).
\]

In the parameter order `(u,v,w,x,r,s)`, the five conditions have matrix

\[
M_8=\begin{pmatrix}
1/2&1&0&0&0&0\\
1/12&1/2&1&1&0&0\\
0&0&744&-984&0&0\\
0&0&0&0&-8&-16\\
1&0&0&0&-1&1
\end{pmatrix}.
\tag{10}
\]

It has rank 5 and the exact rational kernel vector

\[
v_8=\left(-3,\frac32,-\frac{41}{144},-\frac{31}{144},-2,1\right)^T.
\tag{11}
\]

Here the coordinate named `x` in the parameter vector is a scalar coefficient,
not the theta function `x = θ₄⁴` from §2. Implementation names should distinguish
them.

## 4. The twenty-four-dimensional finite space

For parameters `(u,v,w,x,y,r,s,t) ∈ ℂ⁸`, choose

\[
F=\frac{uE_4^3+vE_6^2}{\Delta^2},\qquad
B_0=w\frac{E_4^2E_6}{\Delta^2},\qquad
C_0=\frac{xE_4^4+yE_4E_6^2}{\Delta^2},
\tag{12}
\]

\[
\binom{m_0}{m_2}
 =\frac{rE_4^3V_2+sE_6^2V_2+tE_4E_6W_4}{\Delta^2}.
\tag{13}
\]

The weights in (12) are `-12,-10,-8`; (13) has weight `-10`. The following
seven homogeneous conditions suffice:

| Condition | Purpose |
|---|---|
| `[𝔮⁻²] p̃₁ = 0` | `p₁` has at most a simple cusp pole. |
| `[𝔮⁻²] p̃₂ = [𝔮⁻¹] p̃₂ = [𝔮⁰] p̃₂ = 0` | `p₂` begins at exponent at least 1. |
| `[𝔮⁻³/²] m₂ = [𝔮⁻¹/²] m₂ = 0` | `m₂` begins at exponent at least `1/2`. |
| `[𝔮⁻²](p₀ - m₀) = 0` | `a₅` has at most a simple cusp pole. |

They give exactly the paper's required lower bounds on cusp orders:

\[
(a_0,a_1,a_2,a_3,a_4,a_5):\quad(-2,-1,1,1/2,-1,-1).
\]

In the parameter order `(u,v,w,x,y,r,s,t)`, the matrix is

\[
M_{24}=\begin{pmatrix}
1/3&1/3&1&0&0&0&0&0\\
1/33&1/33&1/5&1&1&0&0&0\\
64/11&-80/11&12/5&1008&-720&0&0&0\\
0&0&0&401544&-54648&0&0&0\\
0&0&0&0&0&-8&-8&-16\\
0&0&0&0&0&-6176&7648&3008\\
1&1&0&0&0&-1&-1&1
\end{pmatrix}.
\tag{14}
\]

It has rank 7 and the exact rational kernel vector

\[
v_{24}=\left(-\frac{49}{8},\frac{25}{8},1,
 -\frac{23}{1760},-\frac{169}{1760},-\frac89,-\frac{10}{9},1\right)^T.
\tag{15}
\]

As in §3, the scalar parameters `x,y,t` must have names distinct from theta
functions and Gaussian variables in implementation code.

## 5. Normalization is explicit

The paper sets `a₁(τ) = -i A₁(q_coeff)`. Thus its normalization functional is

\[
\lambda=\frac{c_{1,0}}4
       =\frac{i}{4}[\mathfrak q^0]p_1
       =-\frac\pi2[\mathfrak q^0]\widetilde p_1.
\tag{16}
\]

For (11) the constant coefficient of `p̃₁` is `-360`; for (15) it is
`-196560`. Therefore

\[
\lambda(v_8)=180\pi,\qquad
\lambda(v_{24})=98280\pi.
\]

Dividing every parameter in (11) or (15) by the respective scalar gives a
section with `λ = 1`. This also proves directly that the section is nonzero.
It uses neither Poisson summation nor a previously constructed magic function
to establish nonzero normalization.

As consistency checks, the normalized eight-dimensional correction part is

\[
4R_{0,1}-\frac{R_{2,0}}{30\pi}-\frac{54}{5\pi}R_{0,0},
\]

and the normalized twenty-four-dimensional correction part is

\[
4R_{0,1}-\frac{R_{4,0}}{16380\pi}
 -\frac{14347}{1365\pi}R_{0,0}
 +\frac1{39}R_{2,1}-\frac{292}{4095\pi}R_{2,0}.
\]

These agree with the paper's later comparison formulas. That agreement is a
check on coordinates and normalizations, not an input to the construction.

All the scalar Fourier coefficients used here are real before the explicit
factors `δ,δ²`. Reversing the paper's changes
`A₁ = i a₁`, `A₂ = -a₂` gives real coefficient vectors after normalization.
The analytic proof should expose this directly or obtain it from uniqueness
and conjugation, as the paper does.

## 6. Why the finite dimension argument is legitimate

There are six independent trial parameters in dimension 8 and eight in
dimension 24. The independence must be proved if existence is presented solely
as "more unknowns than equations": a redundant parametrization would not suffice.

If all six fields (4) vanish, the inverse constant splitting gives `p = m = 0`.
Recover `F`, then `B₀`, then `C₀` from (1). The pairs `E₄³,E₆²` are linearly
independent because their constant coefficients agree and
`E₄³ - E₆² = 1728 Δ ≠ 0`; multiplying by a nonzero scalar modular form
preserves this independence. The remaining scalar products are nonzero.
For the minus block, (7) gives independence of `V₂,W₄`; the same scalar
independence handles the two coefficients multiplying `V₂` in dimension 24.
Every parameter is therefore zero.

Rank-nullity now gives nonzero sections from the 5-by-6 and 7-by-8 systems.
For the shortest Lean existence proof, the explicit witnesses and their
nonzero normalizations are sufficient; proving matrix rank or injectivity is
not a prerequisite to using those witnesses. Their proofs remain useful
independent structural results.

**This does not assert that every section belongs to these trial spaces.**
The matrices' one-dimensional kernels prove uniqueness within the finite
parametrizations. They do not, by themselves, prove uniqueness of all global
sections, all coefficient solutions, or all radial Schwartz functions.

## 7. What remains to reach the paper's coefficient theorems

The dependency chain for this route is:

1. Prove the actual modular/theta identities, holomorphy, cusp expansions, and
   discriminant nonvanishing used above.
2. Prove that the witnesses satisfy the paper's six-field gluing laws and cusp
   tables, with the actual normalizations.
3. Prove the section-to-coefficient reconstruction: first four fields give
   Laurent coefficients, the Cauchy functions have the required traces and
   jumps, endpoint circle terms vanish, and the Fourier moment equations
   follow. This is Lemma 6.1 and the reverse direction of Lemma 11.2 in the
   paper. It includes the difference between unrestricted zeroth moments in
   dimension 24 and vanishing zeroth moments in dimension 8.
4. Prove the native coefficient synthesis map is Schwartz and injective, and
   identify the Fourier sampling operator with the moment operator.
5. For uniqueness in the entire `ℓ²` coefficient family, prove endpoint
   continuation and coefficient-to-section reconstruction, then use the
   vanishing arguments of Proposition 8.1 and Lemma 11.4, or prove an exhaustive
   classification of sections. The finite trial-space rank calculation is not
   such a classification.
6. For the bounded inverse, separately construct the explicit compact
   regularizer on arbitrary coefficient vectors and prove the coercivity
   argument. An abstract projection onto the known kernel does not fulfill
   the paper's specified construction.
7. Transfer signs by comparison with the existing functions to obtain the
   packing certificates. An independent sign proof remains its own research
   target. Full radial-Schwartz uniqueness remains dependent on interpolation
   unless an additional proof is supplied.

The global holomorphy of the first four fields gives recovered coefficient
series on `|q_coeff| < exp(π)`, apart from the specified finite principal parts.
Cauchy's coefficient estimate then gives weighted absolute summability for
every `1 < r < exp(π)`, as in the paper. The formal proof must include the
coordinate change; a bound in the modular coordinate alone is not the stated
coefficient bound.

## 8. Suggested proof boundaries and native APIs

These are proposed implementation boundaries, not claims that these modules
already exist:

| Boundary | Required mathematical content |
|---|---|
| `ThetaCovariants` | Native theta quartics; (3), (5), and (7); analytic/holomorphic laws. |
| `DerivativeBlocks` | Normalize `D₀` versus `D_τ`; prove (1)–(2) and equivalence to the six-field laws. |
| `FiniteCuspData` | Laurent coefficients of the displayed modular expressions; genuine cusp order bounds. |
| `FiniteSections8` / `FiniteSections24` | Define the actual functions and witnesses; prove (10)–(16); `λ = 1`. |
| `SectionToCoefficients` | Explicit Laurent extraction and the global-solution-to-coefficient Cauchy reconstruction needed for existence. |
| `CoefficientUniqueness` | Entire-kernel continuation plus native low-weight vanishing. |

Use native Mathlib modular-form and finite-dimensional linear-algebra APIs at
the current pin. The earlier production `DimensionFormulas` scaffold contains
admissions, so importing it is not a substitute for a proved finite-dimensional
statement. This alternate existence proof does not need a general modular-form
dimension formula: the displayed polynomial identities and finite witnesses
suffice.

The existing production theta files are a reuse source, subject to the old
roadmap's migration/build boundary. Textual absence of `sorry` in an individual
file does not establish its transitive proof status. Record actual imports,
compiled assumptions, and the current pinned build when implementation lands.

For finite calculations, prefer exact rational equalities proved by Lean's
kernel-checked algebraic tactics. The SymPy script is a development check and
is not a proof oracle. A native proof should connect every matrix entry to
the Laurent coefficient it represents; checking a standalone matrix without
that connection is insufficient.

## 9. Relation to the geometric target

The paper's Proposition 7.1 and Lemma 11.3 compute
`χ(E_d) = h⁰(E_d) - h¹(E_d) = 1`. The argument above proves existence of
specific sections. Even combined with a uniqueness proof giving `h⁰ = 1`, it
does not prove `h¹ = 0` without additional geometry.

A literal implementation of the cited Candelori–Franc route must account for
the compactified modular orbifold, its central and elliptic stabilizers, the
cusp extension, determinant line bundle, and an applicable Riemann–Roch
theorem. Candelori–Franc §5 uses GAGA for proper Deligne–Mumford stacks to
transport the analytic bundle to the algebraic weighted projective line
`P(4,6)`. An analytic or specialized alternative may reduce that foundation
cost, but requires its own proof. The finite witness route avoids making this
large geometric development a prerequisite for the first independent
coefficient construction.

In the core implementation, the global solution space should first be the
explicit space of six holomorphic functions satisfying the two gluing laws and
the cusp table. The word "section" in this note is shorthand for such a tuple.
Identifying that space with the actual `H⁰` of an orbifold bundle belongs to the
separate geometric target. This keeps the finite certificate independent of a
general orbifold formalization.

## Sources and reproducible checks

- [Hexagon 2610.00330v1: paper](https://hexagonmath.org/pdf/2610.00330v1), especially
  §6–§8 for the six-field laws, cusp bounds, correspondence and vanishing;
  §10 for the 24-dimensional comparison; and §11 for the 8-dimensional changes.
- [Exact TeX source of version 1](https://hexagonmath.org/api/v1/works/2610.00330v1/source?path=magic-8-24.tex).
- [Candelori–Franc, *Vector valued modular forms and the modular orbifold of
  elliptic curves*](https://arxiv.org/pdf/1506.09192), §5 and Theorem 6.1, for
  the geometric existence route that this proposal postpones.
- Pinned production reuse sources at `bad3de916074748eb88b7d1ee6dbf9494361ad17`:
  [Jacobi theta transformations](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/bad3de916074748eb88b7d1ee6dbf9494361ad17/SpherePacking/ModularForms/JacobiTheta/Basic.lean),
  [Jacobi and discriminant identities](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/bad3de916074748eb88b7d1ee6dbf9494361ad17/SpherePacking/ModularForms/JacobiTheta/JacobiIdentity.lean),
  and the [normalized derivative](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/bad3de916074748eb88b7d1ee6dbf9494361ad17/SpherePacking/ModularForms/Derivative.lean).
- [`scripts/check_finite_sections.py`](../../scripts/check_finite_sections.py): exact checks of the theta polynomial
  covariants, six-component rational group relations and block splitting,
  derivative block identities, cusp matrices, ranks,
  rational witnesses, normalizations, and finite correction coefficients.

Run it with `uv run --with sympy python -I scripts/check_finite_sections.py`.  The expected
output, recorded on 2026-11-22 with SymPy 1.14.0, is:

```text
Theta covariant polynomial identities passed
Six-component rational group relations and block splitting passed
Ordinary-derivative block identities passed
d=8: shape=(5, 6), rank=5, lambda=180*pi; all cusp and finite-coefficient checks passed
d=24: shape=(7, 8), rank=7, lambda=98280*pi; all cusp and finite-coefficient checks passed
```

followed by the two cusp matrices and the two rational witnesses displayed above. All analytic/formal verification
obligations listed above remain explicit roadmap targets.
