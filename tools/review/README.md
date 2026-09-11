# Inactive TauCetiReview import (I05)

**The review engine, rubrics, reference material, and upstream tests are the work of the
[TauCetiReview contributors](https://github.com/TauCetiProject/TauCetiReview), imported from
[`afb424e`](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b).**
Their [Apache-2.0 license](LICENSE) and embedded credits are retained. The naming reference
retains its Mathlib attribution. SphereCeti contributes the inactive import boundary, test
harness, and source mapping.

This directory is source for the [infrastructure plan](../../INFRASTRUCTURE-PLAN.md#i05--import-the-review-engine-and-rubrics-inactive).
It is not an installed review command. All eight imported script launchers exit before imports
or argument handling; `cli.main()` and `archive.sync()` also refuse execution. The SphereCeti
CLI still provides only `doctor` and `status`, and all automation switches remain off.
Internal engine functions remain importable for the upstream fake-provider tests. These
entry-point guards prevent accidental activation; they are not a sandbox for arbitrary Python.

## Review the import

The first commit in I05 copies the source bytes; the following commit contains SphereCeti's
changes. [import-manifest.json](import-manifest.json) lists all 57 source/destination pairs,
the exact upstream revision, Git modes, upstream SHA-256 hashes, and final imported hashes.
Every upstream test, rubric, reference, and fixture is unchanged. Only the eight launcher
modules differ from upstream. The root [source lock](../upstream-lock.toml) records this
component as imported.

| Pinned upstream paths | Local destination | Treatment |
| --- | --- | --- |
| `runner/` | `runner/` | Internal layout retained; the small changes below are marked `SphereCeti` |
| `rubrics/`, including references | `rubrics/` | Verbatim |
| `tests/` | `tests/` | All 16 test scripts, verbatim |
| `.github/workflows/{merge-only,merge-sweep,review}.yml` | `fixtures/workflows/` | Verbatim historical fixtures required by `test_sweep.py`; never active workflows |
| `LICENSE`, `REVIEWING.md`, `SECURITY.md` | Same names | Verbatim upstream license and documentation |
| `README.md` | `UPSTREAM-README.md` | Historical upstream overview |
| `pyproject.toml` | `upstream-pyproject.toml` | Reference only; no installed upstream console scripts |

The remaining upstream workflows and repository administration files are not imported.
The copied upstream documentation describes TauCeti's operation and includes upstream command
examples; it is not SphereCeti configuration or an instruction to install or activate them.

The local changes are:

- Disable all eight script launchers before imports, plus callable `cli.main()` and
  `archive.sync()`. No review, posting, queue, merge, cost-report, or archive command is exposed.
- Require an explicit target repository in the old CLI, engine, and scoreboard CLI; clear
  the default code/roadmap repositories and archive destination. The disabled archive commit
  identity is SphereCeti's, and no TauCeti App identity is assumed.
- Fail when publishing identity cannot be read, instead of falling back to TauCeti's bot.
  Clear the queue reservation actor default. Authenticated App support belongs to I07.
- Remove the old CLI's mutable `main` fallback for missing engine/rubric resources.
  Exact upstream source links and the historical schema/marker vocabulary retain TauCeti names.

Provider adapters, contests, shadow runs, budgeting, rendering, and verdict semantics remain
upstream's. In particular, the legacy scoreboard rules are preserved for their regression
tests; they do **not** authorize SphereCeti merges. The common rubric still describes TauCeti's
project context. I06 must supply SphereCeti's approved evidence and context before any real
review; I07 must authenticate records and publishing identities before reviews can qualify.

## Rubric order

The engine retains the upstream order: correctness, reuse, scope, attribution, api-design,
generality, placement, naming, documentation, proof-quality. The first four can block under
their rubric rules; a block normally halts a round. See the unchanged
[rubric guide](rubrics/README.md) and [shared protocol](rubrics/_common.md).

## Validate without providers or publishing

From the SphereCeti repository root:

```bash
python3 -I scripts/run_review_tests.py
python3 -m unittest discover -s tests -p test_review_import.py
```

The harness runs all 16 upstream scripts, including the prompt-reference tests, in separate
interpreters. Each gets a disposable source tree, home, temporary directory, and credential-free
environment. The historical workflow fixtures are staged under `.github/workflows` only in
that disposable tree. Python audit hooks reject subprocesses, process execution, and sockets,
including attempts caught by the tests themselves. Provider and GitHub interactions are mocked
by the unchanged upstream tests; there is no inference spend or publishing. This detects
accidental external calls in these cooperative tests, not hostile test code.

SphereCeti's six additional tests check the import mapping, exact rubric order, inactive
launchers, disabled sync, missing identity/resources, and the offline guard itself. CI runs
both suites. Root packaging continues to exclude this source import; installed engine and
rubric resources are I06's responsibility.
