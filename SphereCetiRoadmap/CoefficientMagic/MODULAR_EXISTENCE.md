# Existence of solutions of the sample equations from explicit modular forms

## Status and intended use

This note proposes an alternative to the existence step, by Riemann–Roch, in
[Hexagon 2610.00330v1, *A construction of the sphere-packing magic functions in
dimensions 8 and 24*](https://hexagonmath.org/2610.00330v1). The paper constructs
solutions of the sample equations from six-component holomorphic functions satisfying
explicit automorphy laws and cusp conditions. Its existence argument uses the
Euler characteristic of the corresponding bundle. The construction below gives explicit
six-tuples of functions which, once the analytic facts of §7 are proved, are global analytic
solutions whose coefficient vectors have nonzero normalization. It uses only finite-dimensional
linear algebra and known results on scalar modular forms and theta functions.

The script [`scripts/check_modular_identities.py`](../../scripts/check_modular_identities.py)
checks the finite algebra of this note exactly; the list of its checks is under *Sources and
reproducible checks* below.  It does not prove the theta transformation laws, holomorphy, that
the listed coefficient conditions imply the full cusp-order bounds, convergence, the Cauchy
boundary correspondence, Riemann–Roch, or anything else analytic.  In Lean, only the two
identities `C₈ v₈ = 0` and `C₂₄ v₂₄ = 0` are proved; the ranks of the cusp matrices and the
identification of their rows with Laurent coefficients are facts checked by the script, with no
Lean statement.  An implementation must prove in Lean the analytic facts it uses.

This argument is an additional proof of existence.  It proves neither the paper's geometric
identity `χ(𝓔_d) = 1` nor the global sign inequalities independently; the geometric result
remains a separate target.

The corresponding Lean targets are in the namespace `SphereCeti.CoefficientMagic.Witness` of
[`Suggested.lean`](Suggested.lean): `H₂`, `H₄` and their transformation laws, `V₂`, `W₄`,
`det_V₂_W₄_sq` for (7), `plusBlock` and `plusBlock_S` for (1)–(2), `sixFields` for (4),
`candidate8` and `candidate24` for (8)–(9) and (12)–(13), with their laws for every parameter
vector (`candidate8_holo`, `candidate8_translate`, `candidate8_invert`, and likewise in dimension
24), `cuspMatrix8` and `cuspMatrix24` for the matrices `C₈`, `C₂₄` of (10) and (14),
`witness8` and `witness24` for (11) and (15), `isGlobalSolution_candidate8` and
`isGlobalSolution_candidate24` for the passage from a null vector to the cusp-order bounds of
§3–§4, and `normalization_section8`, `normalization_section24` for (16).  The block splitting is
`splitting_mul_glueInvert`, `splitting_mul_glueTranslate`, and
`Witness.splitting_mulVec_sixFields` in the same file.  Among the C5 statements, only the
rational identities `C₈ v₈ = 0` and `C₂₄ v₂₄ = 0` are proved in Lean.  The identification of
each matrix entry with the Laurent coefficient it represents (§8 of this note) has no Lean
statement yet.

## 1. Coordinates, derivatives, and the six functions of the paper

The paper uses two coordinates for power series, which must be kept distinct:

\[
\mathfrak q=e^{2\pi i\tau},\qquad
q_{\mathrm{coeff}}=e^\pi e^{\pi i\tau}
                 =e^\pi\mathfrak q^{1/2}.
\]

The half-power `𝔮^(1/2)` always means `exp(π i τ)` on the upper half-plane, not
another branch of the square root. All Laurent coefficients `[𝔮^e]` in this note
are taken in the cusp coordinate `𝔮`.

The derivative normalized by the factor `1/(2πi)` is

\[
D_0=\mathfrak q\frac{d}{d\mathfrak q}
   =\frac1{2\pi i}\frac{d}{d\tau},\qquad
\delta=2\pi i,\qquad D_\tau=\delta D_0.
\]

The derivative in production already uses this normalization. The paper's block
formulas use the ordinary derivative `D_τ`, so the factors of `δ` below cannot be
omitted.

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

All three components are periodic under `τ ↦ τ + 1`.

The constant splitting of the paper's §8 (Lean: `splitting`) takes the six functions to a plus
block `(p₀, p₁, p₂)` and a minus block `(m₀, m₁, m₂)`.  For the minus block, set `m₁ = 0`, and
choose `(m₀,m₂)` of weight `k + 2` for
the two-dimensional representation

\[
\rho(S)=\frac12\begin{pmatrix}-1&3\\1&1\end{pmatrix},\qquad
\rho(T)=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.
\tag{3}
\]

Recover the six functions of the paper by

\[
\begin{array}{lll}
a_0=p_0+m_0,&a_1=p_1,&a_2=p_2,\\
a_3=m_2,&a_4=p_1-p_2,&a_5=p_0-m_0.
\end{array}
\tag{4}
\]

This is the inverse of the constant splitting in the paper's §8 and §11.5,
restricted to `m₁ = 0`. Thus (2)–(3), together with periodicity, imply its full
six-component gluing laws. In Lean, this equivalence is to be proved for the
matrices `J_tr` and `J_inv` of the paper (Lean: `glueTranslate`, `glueInvert`), not
through an auxiliary bundle structure whose hypotheses include the existence being proved.

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

In these conventions, the theta identities needed are

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

gives the identity

\[
\boxed{\det[V_2,W_4]^2=576\Delta.}
\tag{7}
\]

Since `Δ` is nonzero on the upper half-plane, these two vectors are pointwise
independent there. Their expansions begin `a = 1 + O(𝔮)`, `b = -8 𝔮^(1/2) + O(𝔮^(3/2))`.

Once the existing theta functions of production have been migrated to the current
pinned dependencies, (5)–(7) can be proved in a small first PR, using the existing
definitions of `H₂`, `H₃`, `H₄`, the discriminant, and the slash action; theta
functions and modular forms are not to be redefined for this calculation.

## 3. The finite-dimensional family in dimension 8

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

For a parameter vector, the six functions (4) satisfy the required lower bounds on cusp orders

\[
(a_0,a_1,a_2,a_3,a_4,a_5):\quad(-1,0,1,1/2,0,0)
\]

if and only if these coefficients vanish; the remaining bounds are automatic from the same
expansions.  Existence uses only the implication from the conditions to the bounds.

In the parameter order `(u,v,w,x,r,s)`, the five coefficients are the linear forms given by the
rows of the matrix (computed by the script; no Lean statement yet, see §8)

\[
C_8=\begin{pmatrix}
1/2&1&0&0&0&0\\
1/12&1/2&1&1&0&0\\
0&0&744&-984&0&0\\
0&0&0&0&-8&-16\\
1&0&0&0&-1&1
\end{pmatrix}.
\tag{10}
\]

By the script, it has rank 5; its null space is spanned by the rational null vector

\[
v_8=\left(-3,\frac32,-\frac{41}{144},-\frac{31}{144},-2,1\right)^T.
\tag{11}
\]

Here the coordinate named `x` in the parameter vector is a scalar coefficient,
not the theta function `x = θ₄⁴` from §2. Names in Lean should distinguish them.

## 4. The finite-dimensional family in dimension 24

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

The weights in (12) are `-12,-10,-8`; (13) has weight `-10`. Impose the following
seven homogeneous conditions:

| Condition | Purpose |
|---|---|
| `[𝔮⁻²] p̃₁ = 0` | `p₁` has at most a simple cusp pole. |
| `[𝔮⁻²] p̃₂ = [𝔮⁻¹] p̃₂ = [𝔮⁰] p̃₂ = 0` | `p₂` begins at exponent at least 1. |
| `[𝔮⁻³/²] m₂ = [𝔮⁻¹/²] m₂ = 0` | `m₂` begins at exponent at least `1/2`. |
| `[𝔮⁻²](p₀ - m₀) = 0` | `a₅` has at most a simple cusp pole. |

As in §3, the six functions satisfy the paper's required lower bounds on cusp orders

\[
(a_0,a_1,a_2,a_3,a_4,a_5):\quad(-2,-1,1,1/2,-1,-1)
\]

if and only if these coefficients vanish, and existence uses only the implication from the
conditions to the bounds.  In the parameter order `(u,v,w,x,y,r,s,t)`, the seven coefficients
are given, as in §3, by the rows of

\[
C_{24}=\begin{pmatrix}
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

By the script, it has rank 7; its null space is spanned by the rational null vector

\[
v_{24}=\left(-\frac{49}{8},\frac{25}{8},1,
 -\frac{23}{1760},-\frac{169}{1760},-\frac89,-\frac{10}{9},1\right)^T.
\tag{15}
\]

As in §3, the scalar parameters `x,y,t` must have names in Lean distinct from the
theta quartics and from other variables of the roadmap; so must `u` (also the squared
radius), `r` (also the summability weight), and `s`.

## 5. The normalization

The paper sets `a₁(τ) = -i A₁(q_coeff)`, where `A₁ = Σ_m c_{1,m} q^m` is the generating series
of the coefficients `c_{1,m}`. Thus, for the coefficient vector `c` of a global analytic
solution, the normalizing functional takes the value

\[
\lambda(c)=\frac{c_{1,0}}4
       =\frac{i}{4}[\mathfrak q^0]p_1
       =-\frac\pi2[\mathfrak q^0]\widetilde p_1.
\tag{16}
\]

For (11) the constant coefficient of `p̃₁` is `-360`; for (15) it is
`-196560`. Therefore, writing `c[v]` for the coefficient vector of the global analytic
solution given by a null vector `v`,

\[
\lambda(c[v_8])=180\pi,\qquad
\lambda(c[v_{24}])=98280\pi.
\]

Dividing every parameter in (11) or (15) by the respective scalar gives a null vector
whose coefficient vector has normalization 1, and is in particular nonzero. Neither
Poisson summation nor a previously constructed magic function is used to show
that the normalization is nonzero.

As consistency checks, the correction part of the normalized coefficient vector, that is, the
sum of the terms `c_{j,-ℓ} e^{-πℓ} R_{ℓ,j}` of the nonpositive modes (with `R_{ℓ,0}`, `R_{ℓ,1}`
the correction functions of C0), is in dimension 8

\[
4R_{0,1}-\frac{R_{2,0}}{30\pi}-\frac{54}{5\pi}R_{0,0},
\]

and in dimension 24

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
The analytic proof should show this directly or obtain it from uniqueness
and conjugation, as the paper does.

## 6. Why the parameter count is valid

There are six parameters in dimension 8 and eight in dimension 24. If existence
is deduced only from there being more unknowns than equations, the parameters
must be shown to be independent: a redundant parametrization would not suffice.

If all six functions (4) vanish, the inverse constant splitting gives `p = m = 0`.
Recover `F`, then `B₀`, then `C₀` from (1). The pairs `E₄³,E₆²` are linearly
independent because their constant coefficients agree and
`E₄³ - E₆² = 1728 Δ ≠ 0`; multiplying by a nonzero scalar modular form
preserves this independence. The remaining scalar products are nonzero.
For the minus block, (7) gives independence of `V₂,W₄`; the same scalar
independence handles the two coefficients multiplying `V₂` in dimension 24.
Every parameter is therefore zero.

Rank–nullity then gives nonzero null vectors of the 5-by-6 and 7-by-8 matrices;
injectivity makes the corresponding six-tuples nonzero, and once the targets
`isGlobalSolution_candidate8` and `isGlobalSolution_candidate24` are proved they are
global analytic solutions. For the linear-algebra part of the shortest existence proof
in Lean, the explicit null vectors and the normalizations of the corresponding
coefficient vectors suffice; the rank of the matrices and injectivity are not needed to
use them. Their proofs remain of independent interest.

This does not assert that every global analytic solution lies in these families.
Because the cusp-order bounds hold if and only if the listed coefficients vanish (§3, §4),
the one-dimensionality of the null spaces proves uniqueness within the finite
parametrizations. It does not by itself prove uniqueness among all global analytic
solutions, all solutions of the sample equations, or all radial Schwartz functions.

## 7. What remains to reach the paper's coefficient theorems

The remaining steps of this argument are:

1. Prove the modular and theta identities, holomorphy, expansions at the cusp,
   and nonvanishing of the discriminant used above.
2. Prove that each row of `C₈`, `C₂₄` is the Laurent coefficient it represents, and
   that the six functions given by the explicit null vectors satisfy the paper's
   gluing laws and cusp-order bounds, with `[𝔮⁰] p̃₁ = -360` and `-196560`.
3. Prove that the coefficient synthesis map defined in Lean takes values in
   Schwartz functions and is injective, and identify the Fourier sampling
   operator with the moment operator.
4. Prove the reconstruction of coefficients from a global analytic solution. The
   first four components give Laurent coefficients in `q_coeff`: a cusp bound `𝔮^κ`
   on `a_j`, `j ≤ 3`, together with `q_coeff² = e^{2π} 𝔮`, gives `c_{j,m} = 0` for
   `m < 2κ` and for `m ≢ 2κ (mod 2)`, so the coefficients are indexed by the modes.
   Weighted summability (below) puts the vector in `ℓ²`. The Cauchy transforms have
   the required traces and jumps, the terms from circles around the endpoints
   vanish, and the moment equations follow, hence by step 3 the sample equations.
   This is Lemma 6.1 and the reverse direction of Lemma 11.2 in the paper. It
   includes the difference between unrestricted zeroth moments in dimension 24 and
   vanishing zeroth moments in dimension 8.
5. Prove, by (16) and step 4, that the extracted coefficient vectors have
   normalizations `180π` and `98280π`, and rescale them to normalization 1.
6. For uniqueness in the whole `ℓ²` coefficient space, prove continuation at the
   endpoints and the construction of a global analytic solution from a kernel
   vector, then use the vanishing arguments of Proposition 8.1 and Lemma 11.4,
   or prove a classification of all global analytic solutions. The rank
   computation in the finite-dimensional families is not such a classification.
7. For the bounded inverse, construct separately the explicit compact
   regularizer on arbitrary coefficient vectors and prove coercivity. An
   abstract projection onto the known kernel is not the construction specified
   in the paper.
8. Obtain Cohn–Elkies certificates whose functions equal those of the existing
   certificates, by transferring the sign inequalities from the existing functions.
   An independent proof of the signs is a separate research problem. Uniqueness
   among all radial Schwartz functions still depends on Fourier interpolation
   unless another proof is given.

In step 4, the holomorphy of the first four components on the whole upper half-plane
makes the recovered coefficient series holomorphic on `|q_coeff| < exp(π)`, apart from
the specified finite principal parts. Cauchy's coefficient estimate then gives weighted
absolute summability for every `1 < r < exp(π)`, as in the paper; for an arbitrary
kernel vector the same conclusion needs step 6. The Lean proof must include the change
from `𝔮` to `q_coeff`; a bound in `𝔮` alone is not the stated coefficient bound.

## 8. Suggested modules and the libraries used

These modules are proposed; they do not yet exist:

| Module | Required mathematical content |
|---|---|
| `ThetaCovariants` | Theta quartics from the existing definitions; (3), (5), and (7); analytic/holomorphic laws. |
| `DerivativeBlocks` | Normalize `D₀` versus `D_τ`; prove (1)–(2) and equivalence to the laws for the six functions. |
| `FiniteCuspData` | Laurent coefficients of the displayed modular expressions; the bounds on orders at the cusp. |
| `ModularFamily8` / `ModularFamily24` | Define the functions and explicit null vectors; prove (10)–(16); `λ = 1`. |
| `SolutionToCoefficients` | Extraction of Laurent coefficients and the Cauchy reconstruction of coefficients from a global analytic solution, as needed for existence. |
| `CoefficientUniqueness` | Continuation for the whole kernel, and vanishing of scalar modular forms of low weight from Mathlib. |

Use Mathlib's modular forms and finite-dimensional linear algebra at the current
pin. The earlier production file `DimensionFormulas` contains admissions, so
importing it does not replace a proof of a dimension statement. This
alternative proof of existence does not need a general dimension formula for
modular forms: for its linear-algebra part, the displayed polynomial identities and
explicit null vectors suffice; the analytic steps of §7 are still required.

The existing production theta files may be reused once they are migrated as the
root roadmap prescribes. The absence of `sorry` from the text of a single file
does not show that its results are proved, since they may depend on admissions
in the files it imports. When the implementation is merged, record its imports,
the assumptions reported by the compiled audit, and the current pinned build.

For finite calculations, prefer exact rational equalities proved in Lean by its
algebraic tactics, and connect each matrix entry with the Laurent coefficient it
represents; checking the matrix alone is not enough.

## 9. Relation to the geometric target

The paper's Proposition 7.1 and Lemma 11.3 compute
`χ(𝓔_d) = h⁰(𝓔_d) - h¹(𝓔_d) = 1`. The argument above proves existence of
specific global analytic solutions. Even combined with a uniqueness proof giving `h⁰ = 1`, it
does not prove `h¹ = 0` without additional geometry.

A direct formalization of the cited argument of Candelori–Franc must account for
the compactified modular orbifold, its central and elliptic stabilizers, the
cusp extension, determinant line bundle, and an applicable Riemann–Roch
theorem. Candelori–Franc §5 uses GAGA for proper Deligne–Mumford stacks to
transport the analytic bundle to the algebraic weighted projective line
`P(4,6)`. An analytic or more specialized argument may need less foundational
work, but requires its own proof. This geometric development is not needed for the
coefficient theorem: the explicit null vectors above give existence, and the vanishing
argument (§7, step 6) gives uniqueness.

In the core targets, the space of global analytic solutions is the explicit space
of six-tuples of holomorphic functions satisfying the two gluing laws and the
bounds on cusp orders. Its identification with `H⁰(𝓔_d)` of the orbifold bundle belongs
to the separate geometric target, and "section" in this note means only a
section of that bundle. The construction in this note therefore does not depend
on a formalization of orbifolds.

## Sources and reproducible checks

- [Hexagon 2610.00330v1: paper](https://hexagonmath.org/pdf/2610.00330v1), especially
  §6–§8 for the laws for the six functions, cusp bounds, correspondence and vanishing;
  §10 for the 24-dimensional comparison; and §11 for the 8-dimensional changes.
- [Exact TeX source of version 1](https://hexagonmath.org/api/v1/works/2610.00330v1/source?path=magic-8-24.tex).
- [Candelori–Franc, *Vector valued modular forms and the modular orbifold of
  elliptic curves*](https://arxiv.org/pdf/1506.09192), §5 and Theorem 6.1, for
  the geometric proof of existence, which this note leaves to the geometric target.
- Pinned production reuse sources at `bad3de916074748eb88b7d1ee6dbf9494361ad17`:
  [Jacobi theta transformations](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/bad3de916074748eb88b7d1ee6dbf9494361ad17/SpherePacking/ModularForms/JacobiTheta/Basic.lean),
  [Jacobi and discriminant identities](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/bad3de916074748eb88b7d1ee6dbf9494361ad17/SpherePacking/ModularForms/JacobiTheta/JacobiIdentity.lean),
  and the [normalized derivative](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/bad3de916074748eb88b7d1ee6dbf9494361ad17/SpherePacking/ModularForms/Derivative.lean).
- [`scripts/check_modular_identities.py`](../../scripts/check_modular_identities.py), which
  checks exactly:
  (a) the covariance of `W₄` under `rhoS`, `rhoT`, the determinant formula (6), and
  `det² = 576Δ`, as polynomial identities in `a, b` and `x, y`, and the group relations
  of `rhoS`, `rhoT`;
  (b) symbolically, `det S_frm = -4`, the two cocycle relations of the `6 × 6` gluing
  matrices, and the block splitting;
  (c) the derivative-block identity (1)⇒(2) for `k = -4, -12`, taking the differentiated
  transformation laws of `F`, `D F`, `D² F`, `B`, `D B` as substitution rules;
  (d) the entries of (10) and (14), computed from the expansions in `𝔮` of `E₄`, `E₆`,
  `Δ`, `θ₂⁴`, `θ₄⁴` truncated at `𝔮^{1/2}`-order 8 (three terms of each Eisenstein
  series) by extracting the listed Laurent coefficients as linear forms in the
  parameters, and compared with the displayed matrices;
  (e) that the displayed rational vectors are null vectors, and that the ranks are 5
  and 7;
  (f) `[𝔮⁰] p̃₁`, hence `λ/π = 180, 98280`, and the finite correction coefficients.
  It proves no analytic statement (see the status paragraph).

Run it with `uv run --with sympy python -I scripts/check_modular_identities.py`.  The expected
output, recorded on 2026-11-22 with SymPy 1.14.0, is:

```text
Theta covariant polynomial identities passed
Six-component rational group relations and block splitting passed
Ordinary-derivative block identities passed
d=8: shape=(5, 6), rank=5, lambda=180*pi; all cusp and finite-coefficient checks passed
d=24: shape=(7, 8), rank=7, lambda=98280*pi; all cusp and finite-coefficient checks passed
```

followed by the two cusp matrices and the two rational null vectors displayed above.  All the
analytic facts listed above, and their Lean proofs, remain roadmap targets.
