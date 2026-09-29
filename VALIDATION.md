# Validation status

On the pinned Lean 4.35.0-rc3 toolchain, `lake exe cache get` followed by `lake build` elaborates
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
- the target-signature files contain 286 intentional `sorry` commands;
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
remains admission-free. The integration audit inventories 624 compiled declarations, including
363 with transitive `sorryAx` dependencies, and no lint findings. The 286 textual `sorry`
commands above are a different count: generated declarations and dependents also enter the
compiled admission ledger.

The Lean 4.35.0-rc3 upgrade adds one compiler-generated proof declaration without a `sorryAx`
dependency; all previously inventoried declarations retain the same axiom dependencies, and
the upgrade leaves the admission list unchanged. The audit configuration also includes Mathlib's
new default `tacticAlt` linter, which checks the marking of alternative tactic syntax.

`policy/audits.json` proposes the exact 363-entry ledger for human review with this roadmap.
The profile’s `phase = "roadmap"` and `roadmap_approved = true` describe the state proposed
for landing; checking out the PR does not approve that policy. The authoritative gate continues
to use its already-approved tooling and policy. Initial adoption of the admission policy requires
human review, separately from successful candidate validation. No automation is enabled here.

```bash
python3 scripts/check_roadmap.py
lake env python3 -I scripts/check_audits.py
```
