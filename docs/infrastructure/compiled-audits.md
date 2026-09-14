# Complete compiled audits (#8)

**Adapted from the TauCeti contributors' audit and lint infrastructure**, pinned at
`TauCetiProject/TauCeti@b743b607ce3e9742b18026ad79082e5d15badff5`:

- [Axioms.lean](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/Axioms.lean)
  supplies the defining-module ownership and transitive axiom-audit design.
- [ModuleSystem.lean](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/ModuleSystem.lean)
  supplies compiled `isModule` inspection and safe copying before freeing mmap regions.
- [HeaderStyle.lean](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/HeaderStyle.lean),
  [lint-env.sh](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/lint-env.sh), and
  [lint-style.sh](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/lint-style.sh)
  supply complete-inventory lint, private-level docstring inspection, linter-set calibration,
  and explicit baseline/nolint governance.
- [sandbox-build.sh](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/sandbox-build.sh)
  supplies the approved build/audit sequence and silent library-build requirement.

The [source ledger](../../tools/upstream-lock.toml) records these Apache-2.0 sources and local
destinations. Attribution is retained in the adapters and the [license](../../LICENSE).
TauCeti's environment entrypoint credits importGraph's Kim Morrison and Paul Lezeau;
SphereCeti uses the same Lean CoreM/import APIs. No TauCeti mathematical object is redefined.

## Running the gate

```bash
lake env python3 -I scripts/check_audits.py
lake env python3 -I scripts/check_audits.py --report /tmp/sphereceti-audits.json
lake env python3 -m unittest discover -s tests -p 'test_*.py'
```

The runner first uses #4's native Lean-header inventory. It explicitly builds every library
and roadmap module, including nested files absent from either root's import closure. It also
elaborates all classified tooling and committed fixture modules in dependency order; their
`main` functions are not executed. Unclassified sources and forbidden local import edges fail
before the build. Tools and fixtures are compiled but are not claimed as admission-free mathematics.

The approved `scripts/Audit.lean` then loads all inventoried library and roadmap modules at
Lean's **private** olean level. That includes private declarations, theorem/definition bodies,
and docstrings that exported-only imports can hide. Every declaration is selected by its
defining module, regardless of namespace, visibility, or declaration kind. `Lean.collectAxioms`
collects its transitive dependencies through types and values. SphereCeti uses exact sets rather
than TauCeti's shared Boolean optimization because the roadmap ledger needs exact attribution.

Actual compiled `isModule` flags and direct import lists are checked too. A comment containing
`module` cannot satisfy this check. Import rejection is independent of whether a declaration
uses an imported target. Missing/duplicate module records, a changed linter set, malformed
reports, missing output, compiler failures, and audit-driver errors are failures.

## Approved policy and roadmap interface

[`policy/audits.json`](../../policy/audits.json) is loaded from the **approved tooling copy**,
not from the candidate's adjacent policy file. The existing scope gate protects this file,
audit scripts, and the rest of the infrastructure. In the trusted workflow the entire sequence
runs inside #6's credential-free sandbox using `/gate/scripts/check_audits.py`.
Ordinary CI exercises proposed tooling for human review; it does not approve that tooling.

The library allowlist is exactly `propext`, `Classical.choice`, and `Quot.sound`. The
`axiom_exceptions` array is initially empty. Any deliberate exception must name one module,
declaration, and axiom, with a reason; every transitive dependent needs its own explicit entry.
An exception is not a proof-completion claim.

Roadmap `sorryAx` dependencies require exact `(moduleName, name, reason)` entries in
`roadmap_admissions`. The roadmap integration proposes exact admission entries for human review; the infrastructure
baseline has an empty ledger.
It cannot authorize library admissions or arbitrary roadmap axioms. Missing entries and
entries whose declarations no longer depend on `sorryAx` both fail. This makes a changed
admission set an explicit review event. When integrating PR #1:

1. Move the target sources according to the existing migration plan, preserving declarations.
2. Elaborate and inspect the compiled JSON report, which lists every owned declaration and
   its actual axiom dependencies even when the policy verdict fails.
3. Review exact ledger entries for intentional target admissions, including any generated or
   transitive declarations that use them. Do not infer the ledger from a textual `sorry` count.
4. Run the existing roadmap contract checker from PR #1 alongside this gate. #8 supplies the
   compiled validation interface; it does not install or rewrite the mathematical roadmap.

Zero owned declarations are permitted only for modules listed in `empty_modules`. The three
current exceptions name the imports-only scaffold modules individually. A new empty module
needs policy review; a module that gains declarations reports its old exception as stale.
No dummy theorem was added merely to make the audit count nonzero.

## Lint and exception handling

The environment pass uses the pinned Mathlib/Batteries default linter set, including slow
linters, minus `docBlame`. It invokes the linter API and records structured findings; diagnostic
text never determines the linter or declaration key. The exact sorted set is recorded in
policy, so dependency changes cannot silently drop or add linters.

Following TauCeti, a direct private-level docstring scan replaces `docBlame`; it requires docs
for definitions, inductives, opaques, and axioms, with the same private/auto/instance/projection
exemptions. Theorems do not acquire a new docstring requirement. Runtime sentinels check
visibility of standard docstrings and imported persistent nolint entries; fixture tests check
both documented and undocumented module-system definitions.

`lint_baseline` and `nolint_allowlist` start empty. Entries require exact module, declaration,
linter, and reason. Persistent `@[nolint]` applications are inventoried independently, including
private declarations and multi-name forms. Candidate suppressions cannot authorize themselves.
Fixed baseline entries produce ratchet reminders; they do not let new violations through.

Mathlib's copyright/Authors checks and text-style linters run over every library and roadmap
source, including the roots and unimported files, with fixed defaults and no candidate style
exception file. Text-style failures are fatal. Final newlines are required. After the compiled
audit, `lake build --iofail` replays library build diagnostics so library warnings or information
messages fail. Roadmap admission warnings remain confined to roadmap elaboration.

The scaffold root now uses `module`, and the old diagnostic `#check` was removed from Basic.
These are build-hygiene changes; they add no mathematical declarations and change no target types.

## Limits and evidence

The Lean/TauCeti/Mathlib dependency graph stays on rc1. On this pin, `native_decide`
produces private per-theorem axioms (`…._native.native_decide.ax_…`), which the allowlist
rejects just like any other nonstandard axiom. The runtime audit imports compiled
artifacts after source elaboration, at Lean's conventional audit trust level 1024; it checks
ownership, metadata, and axiom dependencies, not independent kernel rechecking of arbitrary
hand-forged oleans. Lint loads environment extensions and can execute initializers. As in
TauCeti, this is not a proof-verification boundary against deliberately hostile native code
that forges artifacts or sabotages the audit process. The #6 sandbox confines execution;
its separate scope verdict and human policy review remain necessary. No merge automation is enabled.

Regression fixtures exercise unimported admissions, new axioms, definition/type dependencies,
private declarations, foreign namespaces, `native_decide`, unused forbidden imports, compiled
module flags, documentation, environment/style lint, nolint suppression, candidate policy
changes, complete tooling/fixture elaboration, malformed reports, and exact roadmap ledgers.
Hosted CI additionally runs the complete immutable candidate pipeline and these audits inside
the real sandbox. A textual admission count remains informational, never proof-completion evidence.
