# TauCetiReview import and local adapter

**The review engine, rubrics, reference material, and upstream tests are the work of the
[TauCetiReview contributors](https://github.com/TauCetiProject/TauCetiReview), imported from
[`afb424e`](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b).**
Their [Apache-2.0 license](LICENSE) and embedded credits are retained. The naming reference
retains its Mathlib attribution. SphereCeti contributes the inactive import boundary, test
harness, source mapping, and local advisory adapter.

This directory supplies the engine and resources for the [local review adapter](../../docs/infrastructure/local-review.md). All eight imported script launchers exit before runtime imports or argument handling; the legacy
`runner/cli.py` main and `archive.sync()` also refuse execution. The SphereCeti CLI provides
`doctor`, `status`, and `review`, including record inspection and explicit policy-gated
posting; all shipped automation switches remain off. The later `runner/sandbox_check.py`
diagnostic needs no credential, model, or GitHub access and is reached through
`sphereceti review-check-sandbox`, which calls its `diagnose()` in a fresh interpreter. See [review records](../../docs/infrastructure/review-records.md).
Internal engine functions remain importable for the upstream fake-provider tests. These
entry-point guards prevent accidental activation; they are not a sandbox for arbitrary Python.

## Review the import

The first commit in [PR #9](https://github.com/thefundamentaltheor3m/SphereCeti/pull/9) copies the source bytes; the following commit contains SphereCeti's
changes. [import-manifest.json](import-manifest.json) (schema 2) lists all source/destination
pairs, the exact upstream revision, Git modes, upstream SHA-256 hashes, and final imported
hashes. A row's optional `commit` names a later upstream revision whose bytes it carries; its
optional `adapted` list names later merged upstream PRs ported onto the afb424e bytes. Every
upstream rubric, reference, and fixture is unchanged. The root
[source lock](../upstream-lock.toml) records this component as imported.

Later upstream fixes adapted after the original import (see
[Codex sandbox diagnostic](../../docs/infrastructure/local-review.md#codex-sandbox-diagnostic)):

| TauCetiReview PR | Merged commit | Local files |
| --- | --- | --- |
| [#194](https://github.com/TauCetiProject/TauCetiReview/pull/194) credential-free sandbox diagnostic | [`51149da`](https://github.com/TauCetiProject/TauCetiReview/commit/51149da792cd8b28aba617f118d1ae01aefbe501) | `runner/reviewers.py` (package-relative import), `runner/sandbox_check.py`, `tests/test_sandbox_check.py` |
| [#196](https://github.com/TauCetiProject/TauCetiReview/pull/196) Codex launcher `PATH` and private `TMPDIR` | [`8cb4374`](https://github.com/TauCetiProject/TauCetiReview/commit/8cb4374133d429627c31d9835bfe6fc9d71771e9) | `runner/reviewers.py`, `runner/sandbox_check.py`, `tests/test_{codex_fallback,reviewer_env,sandbox_check}.py` |

`runner/sandbox_check.py`, `tests/test_codex_fallback.py`, and `tests/test_reviewer_env.py` are
the 8cb4374 bytes. #196's inspection-failure narrowing is not ported: it amends a detector
from TauCetiReview #193 that this import does not contain. Its REVIEWING.md text and the
`tauceti-review-check-sandbox` console script are replaced by `sphereceti review-check-sandbox`.

| Pinned upstream paths | Local destination | Treatment |
| --- | --- | --- |
| `runner/` | `runner/` | Internal layout retained; the small changes below are marked `SphereCeti` |
| `rubrics/`, including references | `rubrics/` | Verbatim |
| `tests/` | `tests/` | All 16 test scripts, verbatim or at the later revisions above, plus `test_sandbox_check.py` |
| `.github/workflows/{merge-only,merge-sweep,review}.yml` | `fixtures/workflows/` | Verbatim historical fixtures required by `test_sweep.py`; never active workflows |
| `LICENSE`, `REVIEWING.md`, `SECURITY.md` | Same names | Verbatim upstream license and documentation |
| `README.md` | `UPSTREAM-README.md` | Historical upstream overview |
| `pyproject.toml` | `upstream-pyproject.toml` | Reference only; no installed upstream console scripts |

The remaining upstream workflows and repository administration files are not imported.
The copied upstream documentation describes TauCeti's operation and includes upstream command
examples; it is not SphereCeti configuration or an instruction to install or activate them.

The local changes are:

- Disable all eight script launchers before imports, plus callable `cli.main()` and
  `archive.sync()`. No legacy review, posting, queue, merge, cost-report, or archive command is exposed.
- Require an explicit target repository in the old CLI, engine, and scoreboard CLI; clear
  the default code/roadmap repositories and archive destination. The disabled archive commit
  identity is SphereCeti's, and no TauCeti App identity is assumed.
- Fail when publishing identity cannot be read, instead of falling back to TauCeti's bot.
  Clear the queue reservation actor default. The record adapter checks GitHub API user/App IDs; App setup remains separate.
- Move one test from `tests/test_sandbox_check.py`, which executes `/bin/sh`, to
  `tests/test_review_sandbox.py` at the repository root, where subprocesses are permitted.
- Remove the old CLI's mutable `main` fallback for missing engine/rubric resources.
  Exact upstream source links and the historical schema/marker vocabulary retain TauCeti names.

Provider adapters, contests, shadow runs, budgeting, rendering, and verdict semantics remain
upstream's. In particular, the legacy scoreboard rules are preserved for their regression
tests; they do **not** authorize SphereCeti merges. The original common rubric still describes TauCeti's project context. The adapter uses the
explicit `project/_common.md` and `project/scope.md` overlays in its effective prompt copy, with
a separate content digest. The separate record adapter authenticates publishing identities from GitHub API metadata.

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

The harness runs all 17 imported upstream scripts, including the prompt-reference tests, in separate
interpreters. Each gets a disposable source tree, home, temporary directory, and credential-free
environment. The historical workflow fixtures are staged under `.github/workflows` only in
that disposable tree. Python audit hooks reject subprocesses, process execution, and sockets,
including attempts caught by the tests themselves. Provider and GitHub interactions are mocked
by the unchanged upstream tests; there is no inference spend or publishing. This detects
accidental external calls in these cooperative tests, not hostile test code.

SphereCeti's six additional tests check the import mapping, exact rubric order, inactive
launchers, disabled sync, missing identity/resources, and the offline guard itself. CI runs
both suites. Root packaging includes the engine, rubrics, project overlays, source manifest, and license.
Fresh-installation tests exercise the local adapter with a fake provider; upstream workflows
and test scripts are not runtime package resources.
