# Validation status

The roadmap was originally drafted in an environment without `lean`, `lake`, or `elan`, so the
authoring environment could not run the pinned Lean elaborator.  The target files have since been
elaborated: on the pinned toolchain, `lake exe cache get` followed by `lake build` completes
successfully, with the only warnings being the intentional `sorry` markers in the target-signature
files.

What has been checked in this repository:

- `python3 scripts/check_roadmap.py` passes;
- the Lean, TauCeti, Mathlib, and Sphere-Packing pins agree across the toolchain, Lake files,
  README, and provenance ledger;
- the committed Lake manifest contains the exact TauCeti revision and the Mathlib revision resolved
  by that TauCeti snapshot;
- every local Markdown link resolves;
- the target files contain no theorem whose stated conclusion is merely `True`;
- all generated files have final newlines;
- the target-signature files contain 112 intentional `sorry` occurrences;
- the full Lean elaboration passes locally:

```bash
lake exe cache get
lake build
```

The GitHub workflow runs the static contract check followed by the same `lake build`.  Any future
elaboration fixes should preserve the mathematical target boundaries rather than weaken them merely
to satisfy the parser or typechecker.
