# Validation status

On the pinned Lean 4.36.0-rc2 toolchain, `lake exe cache get` followed by `lake build` elaborates
every target signature locally; the only warnings are the intentional `sorry` markers in the
target-signature files. CI runs the same elaboration and audit checks.

What has been checked in this repository:

- `python3 scripts/check_roadmap.py` passes;
- the Lean, TauCeti, Mathlib, and Sphere-Packing pins agree across the toolchain, Lake files,
  README, and provenance record;
- the committed Lake manifest contains the exact TauCeti revision and the Mathlib revision resolved
  by that TauCeti snapshot;
- every local link in the roadmap's own Markdown documents resolves, including the registered
  sibling roadmap documents;
- every Lean file under `SphereCetiRoadmap/` is `Pinned.lean` or a registered target file, and
  `SphereCetiRoadmap.lean` imports every registered target file;
- the target files, including those of registered sibling roadmaps, contain no theorem whose
  stated conclusion is merely `True`, and end with final newlines;
- the target-signature files contain 254 intentional `sorry` commands;
- the three target files of the sibling roadmap contain 103 intentional `sorry` commands in the
  `coefficient-magic` roadmap;
- the full Lean elaboration passes locally:

```bash
lake exe cache get
lake build
```

The GitHub workflow runs the static consistency check and the complete classified-source build
and compiled audit, restoring Mathlib from its cache and Tau Ceti from its public Lake artifact
service.  Elaboration fixes must preserve the mathematical target boundaries rather than
weaken them merely to satisfy the parser or typechecker.

## Compiled admission policy

The separate `SphereCetiRoadmap` library contains the target modules; the `SphereCeti` library
remains admission-free. The integration audit inventories 594 compiled declarations (86 in
`Pinned`, 508 in `Suggested`), including 335 with transitive `sorryAx` dependencies, and no lint
findings. The 254 textual `sorry` commands above are a different count: generated declarations
and dependents also enter the compiled admission ledger.

The 2026-11-10 dependency update moves TauCeti from `271e1af` (Lean 4.36.0-rc1, Mathlib
`2cabef9`) to `83769e4` (Lean 4.36.0-rc2, Mathlib `1b1ccf4`).  On the unchanged target file the
newer graph breaks only three Layer 0 `#check` lines, all TauCeti renames, and with those renamed
the inventory and admission ledger are exactly those of the rc1 pin.  The update then replaces
the targets that TauCeti now supplies:

- nine declarations are deleted: the eight `ThetaSeries` stand-ins (`thetaSeries_neg_inv`,
  `thetaForm`, `coe_thetaForm`, `qExpansion_thetaForm_coeff`, `thetaForm_eq_E₄`,
  `representationNumber_two_rank_eight`, `thetaForm_rank_24`, `coe_thetaForm_rank_24_rootless`),
  now typed `example`s against TauCeti, and `Leech.kissingNumber_integralLattice`, now an
  `example` proved by `TauCeti.kissingNumber_leechLattice`;
- `E8.even_unimodular_rank_eight_unique` is proved from TauCeti's classification and leaves the
  ledger;
- `IntegralPresentation.isIntegral_real`, `ratModelIsometry`, and `ratModelIsometry_single` are new
  bridge targets to TauCeti's rational model, and enter the ledger.  The `@[simp]` lemma
  `ratModelIsometry_single` has a `simp` example checking that it fires inside a sum;
- `scripts/check_roadmap.py` checks uses, not mere mentions: each TauCeti theta API must be applied
  in the proof of a `sorry`-free `example` in `section ThetaSeries`, and `isEven_real` and
  `isUnimodular_real` must be proved from TauCeti's `ratModel` comparisons transported along
  `P.ratModelIsometry`, which must be typed as an isometry into `ZLattice.ratModel`;
- `IntegralPresentation.isEven_real` and `isUnimodular_real`, the three `Theta` corollaries,
  `E8.theta_eq_E4`, `Leech.shellCard_four`, and `Leech.theta_eq_E4_cubed_sub_720_Delta` are now
  short proofs from TauCeti results and the remaining bridge targets.  They lose their textual
  `sorry` but stay in the ledger through those targets;
- five compiler-generated declarations without a `sorryAx` dependency are new: the equation lemmas
  `Theta.latticeTheta.eq_1`, `Theta.E4.eq_1`, and `Theta.rootCard.eq_1`, a match auxiliary of
  `E8.even_unimodular_rank_eight_unique`, and a proof auxiliary of `ratModelIsometry`.

The ledger therefore loses ten entries and gains three (341 to 334), and the textual count drops
from 268 to 253.  The audit's linter set, including Mathlib's default `tacticAlt` linter, is
unchanged by the update.

Statement corrections after the 2026-11-17 mathematical review on PR #1 keep every count: 253
textual `sorry` commands, 593 declarations, 334 admissions.  Equal counts do not validate changed
statements; these corrections need mathematical review in their own right:

- the central-pair Fourier identity `Contour.fourier_centralComponent` now assumes the inversion
  law with the negated sign, because `z ↦ -1/z` reverses the orientation of the central segment
  relative to `verticalRay`.  The four `…Kernels_law_centralRay` targets carry the negated
  eigenvalue, and the six-piece assemblies are unchanged;
- the review's proposed sign change in `E8.magicProfile` is not adopted.  With `b` defined by the
  contour convention of Viazovska's (52), `g = (πi/8640) a - (i/(240π)) b` is the function of
  (62): Theorem 4's printed `+` agrees with (58) but not with (52)–(53).  The docstring of
  `E8.magicProfile` records the coefficient check, and MIGRATION K5 follows.  The `-1` kernels
  use the corrected `J₆` sign of (52);
- `Leech.magic_zero_iff` becomes `Leech.magic_zero_iff_of_two_le_norm`, stated for `‖x‖ ≥ 2`, the
  scope of the published proof.  The ledger entry is renamed.  `E8.magic_zero_iff` and both
  Fourier-side zero sets keep their global statements.

The real-isometry adapter gains a pointwise target, `IntegralPresentation.realIsometryOfIsometry_basis`:
on each basis vector of the source presentation, the real isometry agrees with the given TauCeti
isometry in the target presentation's coordinates.  `realIsometry_maps_carrier` alone does not
determine the extension (for `ℤ ⊂ ℝ`, the identity and negation have the same image).  The new
target adds one textual `sorry`, one declaration, and one admission: 254, 594, and 335.

## The coefficient-construction roadmap

The sibling roadmap `SphereCetiRoadmap/CoefficientMagic/` adds three modules and leaves the
modules above unchanged: `Pinned` and `Suggested` keep their 86 and 508 declarations and their
12 and 323 admissions.  The audit now inventories 884 compiled declarations, including 494 with
transitive `sorryAx` dependencies, and no lint findings:

| Module | Declarations | Admissions |
|---|---:|---:|
| `SphereCetiRoadmap.Pinned` | 86 | 12 |
| `SphereCetiRoadmap.Suggested` | 508 | 323 |
| `SphereCetiRoadmap.CoefficientMagic.Suggested` | 232 | 110 |
| `SphereCetiRoadmap.CoefficientMagic.Geometry` | 18 | 12 |
| `SphereCetiRoadmap.CoefficientMagic.Comparison` | 40 | 37 |

What the counts mean for these modules:

- in `CoefficientMagic.Suggested`, five definitions have `sorry` bodies (`synth`, `momentOp`,
  `ofGlobalSolution`, `toGlobalSolution`, `solution`), each with its defining equations stated as
  separate targets, and four have `sorry` proofs of membership or closure inside real data
  (`sampleKernel`, `globalSolution`, `Witness.section8`, `Witness.section24`).  Every other
  admission is a theorem target or a dependent of one.  The declarations without admissions are
  the definitions with real bodies, their generated lemmas, and a few immediate facts such as
  `Case.dim_pos` and `mem_sampleKernel`.  The `example`s are proved; among them are the exact
  rational identities `cuspMatrix8 *ᵥ witness8 = 0` and `cuspMatrix24 *ᵥ witness24 = 0`;
- in `CoefficientMagic.Comparison`, the only textual `sorry` commands are the two targets
  `magic_e8_eq` and `magic_leech_eq`.  The other 35 admissions are proofs from those two and from
  targets of the original roadmap (the sign inequalities, real-valuedness, and zero sets), and
  from `magic_zero` and `fourier_magic_zero`.  They are in the ledger because their dependencies
  are;
- in `CoefficientMagic.Geometry`, the twelve admissions are the twelve matrix identities.

The statements were reviewed against the source paper and `MODULAR_EXISTENCE.md` on 2026-11-22,
with exact SymPy and high-precision numerical checks of the gluing matrices, the correction
jets, the theta and discriminant identities, and the transformation laws of both candidate
families for random parameters.  That review found no false statement.  It is a check by the
authors of this roadmap, not a substitute for mathematical review of the pull request, and
neither it nor `scripts/check_modular_identities.py` is a proof.

The contour measures and Cauchy transforms, the endpoint continuation, the concrete
regularizer, the row-by-row identification of the cusp matrices, and the orbifold bundle with
its Euler characteristic have no Lean declaration and so no ledger entry.  The coverage table in
`SphereCetiRoadmap/CoefficientMagic/README.md` lists them.

`policy/audits.json` proposes the exact 494-entry ledger for human review with these roadmaps.
The profile’s `phase = "roadmap"` and `roadmap_approved = true` describe the state proposed
for landing; checking out the PR does not approve that policy. The authoritative gate continues
to use its already-approved tooling and policy. Initial adoption of the admission policy requires
human review, separately from successful candidate validation. No automation is enabled here.

```bash
python3 scripts/check_roadmap.py
lake env python3 -I scripts/check_audits.py
```
