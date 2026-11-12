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
- every local link in the roadmap's own Markdown documents resolves;
- the target files contain no theorem whose stated conclusion is merely `True`, and end with final
  newlines;
- the target-signature files contain 253 intentional `sorry` commands;
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
remains admission-free. The integration audit inventories 593 compiled declarations (86 in
`Pinned`, 507 in `Suggested`), including 334 with transitive `sorryAx` dependencies, and no lint
findings. The 253 textual `sorry` commands above are a different count: generated declarations
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

`policy/audits.json` proposes the exact 334-entry ledger for human review with this roadmap.
The profile’s `phase = "roadmap"` and `roadmap_approved = true` describe the state proposed
for landing; checking out the PR does not approve that policy. The authoritative gate continues
to use its already-approved tooling and policy. Initial adoption of the admission policy requires
human review, separately from successful candidate validation. No automation is enabled here.

```bash
python3 scripts/check_roadmap.py
lake env python3 -I scripts/check_audits.py
```
