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
- every local Markdown link resolves;
- the target files contain no theorem whose stated conclusion is merely `True`, and end with final
  newlines;
- the target-signature files contain 231 intentional `sorry` commands;
- the full Lean elaboration passes, locally and in CI:

```bash
lake exe cache get
lake build
```

The GitHub workflow runs the static contract check and then the same `lake build`, restoring
Mathlib from its cache and Tau Ceti from its public Lake artifact service, and is green on this
dependency pin.  Elaboration fixes must preserve the mathematical target boundaries rather than
weaken them merely to satisfy the parser or typechecker.
