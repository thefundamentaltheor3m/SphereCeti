# Validation status

On the pinned toolchain, `lake exe cache get` followed by `lake build` elaborates every target
signature, locally and in CI; the only warnings are the intentional `sorry` markers in the
target-signature files.

What has been checked in this repository:

- `python3 scripts/check_roadmap.py` passes;
- the Lean, TauCeti, Mathlib, and Sphere-Packing pins agree across the toolchain, Lake files,
  README, and provenance ledger;
- the committed Lake manifest contains the exact TauCeti revision and the Mathlib revision resolved
  by that TauCeti snapshot;
- every local link in the owned roadmap Markdown documents resolves;
- the target files contain no theorem whose stated conclusion is merely `True`, and end with final
  newlines;
- the target-signature files contain 282 intentional `sorry` commands;
- the full Lean elaboration passes, locally and in CI:

```bash
lake exe cache get
lake build
```

The GitHub workflow runs the static contract check and the complete classified-source build
and compiled audit, restoring Mathlib from its cache and Tau Ceti from its public Lake artifact
service.  Elaboration fixes must preserve the mathematical target boundaries rather than
weaken them merely to satisfy the parser or typechecker.

## Compiled admission policy

The separate `SphereCetiRoadmap` library contains the target modules; the `SphereCeti` library
remains admission-free. The integration audit inventories 619 compiled declarations, including
359 with transitive `sorryAx` dependencies, and no lint findings. The 282 textual `sorry`
commands above are a different count: generated declarations and dependents also enter the
compiled admission ledger.

`policy/audits.json` proposes the exact 359-entry ledger for human review with this roadmap.
The profile’s `phase = "roadmap"` and `roadmap_approved = true` describe the state proposed
for landing; checking out the PR does not approve that policy. The authoritative gate continues
to use its already-approved tooling and policy. Admission-policy bootstrap requires human
review, separately from successful candidate validation. No automation is enabled here.

```bash
python3 scripts/check_roadmap.py
lake env python3 -I scripts/check_audits.py
```
