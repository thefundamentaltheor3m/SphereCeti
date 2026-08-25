# Validation status

The roadmap was originally drafted in an environment without `lean`, `lake`, or `elan`, and without
outbound Git access, so the authoring environment could not run the pinned Lean elaborator or build
TauCeti.  The full `lake build` of the target-signature files is pending on this branch.

What has been checked in this repository:

- `python3 scripts/check_roadmap.py` passes;
- the Lean, TauCeti, Mathlib, and Sphere-Packing pins agree across the toolchain, Lake files,
  README, and provenance ledger;
- the committed Lake manifest contains the exact TauCeti revision and the Mathlib revision resolved
  by that TauCeti snapshot;
- every local Markdown link resolves;
- the target files contain no theorem whose stated conclusion is merely `True`;
- all generated files have final newlines;
- the target-signature files contain 112 intentional `sorry` occurrences.

What remains to be checked locally and by CI:

```bash
lake exe cache get
lake build
```

The GitHub workflow runs the static contract check followed by `lake build`.  Until that workflow is
green, the signatures should be described as **compile-oriented**, not as verified to elaborate.
Any first elaboration fixes should preserve the mathematical target boundaries rather than weaken
them merely to satisfy the parser or typechecker.
