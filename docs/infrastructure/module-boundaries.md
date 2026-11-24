# Lean library and roadmap boundaries

This boundary adapts TauCeti's practice of enumerating every source module before auditing
the library. The design source is
[TauCeti's source inventory](https://github.com/TauCetiProject/TauCeti/blob/8671bee98125933c56b9b00a08ded873b77dd23b/scripts/source-modules.sh)
at commit `8671bee98125933c56b9b00a08ded873b77dd23b`, path `scripts/source-modules.sh`.
The new Python implementation uses Lean's own header parser and adds separate roadmap,
tooling, and fixture classes. The broader upstream attribution and planned ports are in
[the infrastructure plan](../../INFRASTRUCTURE-PLAN.md).

| Sources | Class | Permitted local imports |
|---|---|---|
| `SphereCeti.lean`, `SphereCeti/**/*.lean` | Library | Library |
| `SphereCetiRoadmap.lean`, `SphereCetiRoadmap/**/*.lean` | Roadmap | Library, roadmap |
| `scripts/**/*.lean` | Tooling | Library, roadmap, tooling |
| `tests/fixtures/**/*.lean` | Fixture | All four classes |

Dependency sources under `.lake/packages/` and the selected Lean toolchain's `src/lean/` are
outside this local boundary. Other external sources inherited through `LEAN_SRC_PATH` are
rejected. The exact dependency graph remains pinned.
Unknown Lean source locations are errors, including nested sources not imported by either root.
Symlinked Lean sources/directories and invalid module filenames are rejected. Only root `.git`,
`.lake`, and `.venv` directories are excluded. These are generated/dependency locations, not
places for project source.

Run from the project root:

```bash
lake env python3 scripts/check_modules.py --json
lake env python3 -m unittest discover -s tests -p 'test_*.py'
lake build SphereCeti SphereCetiRoadmap
```

`lake build` also selects both libraries. The checker invokes `lean --src-deps` on every
classified file; it does not approximate Lean import syntax with a regular expression.
Every local import edge is checked, so indirect library-to-roadmap imports are also rejected.
The tests create disposable source projects and exercise the real Lean header reader.

This check does not elaborate proofs, audit axioms, or create a security sandbox.
The ordinary CI tests the candidate checker. [#6](trusted-build.md) adds trusted tooling and
isolation; [#8](compiled-audits.md) adds compiled axiom/module audits, lint, and builds of the
complete inventory. Run `lake env python3 -I scripts/check_audits.py` for that combined gate.

Add proofs under `SphereCeti/<Topic>/` and import topic modules directly. Do not edit
`SphereCeti.lean`: each library's `<Library>.*` glob in `lakefile.toml` (Lake's `andSubmodules`)
builds every module below it. The inventory and compiled audit come from the source tree, not from
the root's imports, so a module the root does not import is still built and checked. The root
keeps its existing re-exports, so `import SphereCeti` still works downstream, and is otherwise
frozen. `scripts/check_roadmap.py` keeps both globs and the root's import list fixed, and the
trusted gate and auto-approval decision route any root edit to human review.
The library imports only pinned dependencies and other admission-free library modules.
Roadmap declarations may depend on the library. Use the roadmap as the proof specification.

For the roadmap PR, move its target files to `SphereCetiRoadmap/Suggested.lean` and
`SphereCetiRoadmap/Pinned.lean`, and import them from `SphereCetiRoadmap.lean`. Retain declaration
namespaces `SphereCeti.Suggested` and `SphereCeti.Pinned`. Do not add forwarding imports in the
library. Keep the Pinned model frozen and delete it at the existing A2 production handoff.
The default build remains both libraries; the roadmap's static contracts and admission ledger
are integrated separately without changing target statements.
