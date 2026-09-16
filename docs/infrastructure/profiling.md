# Advisory exact-revision profiling

**Adapted from the [TauCeti contributors](https://github.com/TauCetiProject/TauCeti),
Apache-2.0, at [b743b60](https://github.com/TauCetiProject/TauCeti/tree/b743b607ce3e9742b18026ad79082e5d15badff5).**
The pinned sources are
[`scripts/perf/manifest.py`](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/perf/manifest.py),
[`measure.py`](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/perf/measure.py),
[`report.py`](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/perf/report.py),
[`test_perf.py`](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/perf/test_perf.py),
[`test_profile_workflow.py`](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/test_profile_workflow.py), and
the [`pr-profile.yml` workflow](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/.github/workflows/pr-profile.yml).
The source/destination and adaptation ledger is `tools/upstream-lock.toml`.

## Review and dependency boundary

Read the foundation’s immutable Git gate and sandbox contract first, then `profiling.py`,
`profile_runner.py`, and the tests. This is the final infrastructure layer before roadmap #1.

This is local, opt-in tooling. There is no profiling publisher, required status, scheduled
workflow, GitHub mutation, or provider call. The CI addition runs only a disposable fixture.
All automation switches retain their previous settings. Profiling does not establish a
theorem's correctness, audit success, review approval, or merge eligibility. Roadmap files
are labeled separately from library files without changing their statements or layout.

## Commands

Use an installed CLI whose Python files match the exact selected tooling commit `T`.
`B` is an exact base-branch tip, `H` the exact candidate head. The measured base is their
unique Git merge base; the plan records all four revisions. Supply full commit SHAs.

```bash
sphereceti profile-plan --repo /path/to/git-repo --tooling "$T" --base "$B" --head "$H"
sphereceti profile-run --repo /path/to/git-repo --tooling "$T" --base "$B" --head "$H" \
  --workspace /path/to/new-profile-run \
  --toolchain /path/to/lean-4.34.0-rc1 \
  --dependencies /path/to/prepared/.lake/packages
```

`profile-plan` reads Git objects and prints JSON without executing Lean, contacting GitHub,
or requiring dependencies. Uncommitted working-tree edits are irrelevant. It enumerates
all changed library/roadmap Lean paths from trees, so no GitHub file-list cap applies.
Renames are deliberately an old-path removal plus a new-path addition, with no guessed
cost ratio between differently named modules. Unsupported module names, symlinks,
submodules, ambiguous merge bases, missing configuration, and more than 32 modules fail.

`profile-run` requires Linux, GNU time, #6's exact pinned bubblewrap, a functioning namespace
sandbox, the matching Lean toolchain, and operator-prepared dependency checkouts/builds.
Prepare those dependencies using the existing trusted-build instructions. Their tracked
sources must be clean at the exact manifest commits. Built dependency artifacts retain
#6's trusted-input assumption: the profiler does not prove their correspondence to source.
Keep their directory stable throughout the run. It is mounted read-only and shared between
the two private source trees; no dependency copy or cache download occurs.

Lake configuration must match `T` byte-for-byte on **both** measured sides. Toolchain or
dependency bumps require a separate measurement policy; this command rejects them.
The installed profiler source must also match `T`; selecting a revision is an operator
choice, not evidence of approval on GitHub. The toolchain version and binary hashes are
recorded. The original source repository is never checked out or modified.

## Measurement and output contract

Each side is materialized from immutable ordinary Git blobs without checkout filters or
candidate helpers. A sandboxed Lake prebuild constructs that side's selected modules and
their dependency cone. Each selected source is then passed directly to Lean (`-j1`) inside
the same sandbox, forcing re-elaboration even if its `.olean` is cached. Sources keep their
original paths. Each side uses its own environment; old sources are not elaborated against
the head environment. Removed files get a base-only measurement, added files a head-only one.

Host GNU time wraps each sandbox invocation with an empty environment. Raw CPU counters
are outside every sandbox mount, and elapsed time comes from the host monotonic clock.
Candidate stdout/stderr are discarded; they cannot forge counters or Actions commands.
Sandbox-written logs and build files are never collected by host code. This avoids importing
upstream's heartbeat-log collector and artifact-invalidation paths. Dependency and toolchain
mounts must be disjoint from the new workspace, so they cannot expose its counters.

The run writes `plan.json`, `raw/*.time`, `report.json`, and `report.md`, retaining its two
prepared trees for inspection. The report binds each sample to its plan digest, exact source
revision, and fresh run ID. Duplicate, unexpected, or cross-run samples are rejected.
Missing measurements, prebuild errors, timeouts, invalid/negative/nonfinite counters, and
failed elaboration remain errors; partial counts never enter a comparison. Startup errors
return an error diagnostic and may leave only a partial workspace. Existing workspaces are
never resumed or overwritten. Keep/clean only the run directory you own.

Successful measurements use TauCeti's CPU thresholds: a modified file is flagged only at
both ≥1.5× base and +30 CPU seconds; an added file at ≥150 CPU seconds. These flags do not
change the successful command exit code. Measurement errors return nonzero. A valid empty
diff reports `no_changes`; it is distinct from absent data. Reports use linked seven-character
GitHub revision labels and include both CPU and wall time.

CPU includes Lake/sandbox startup. It is a noisy single sample, sensitive to the host,
dependency artifacts, and environmental state. The report records these limits; it offers
no cross-run comparison or deterministic heartbeat/instruction claim. No upstream required
`perf` status, comment publication, queue behavior, or hard performance acceptance gate is ported.

## Bounds and validation

The runner serializes sides and samples, limits each prebuild to 900 seconds, each sample
to 300 seconds, and the measurement phase to 1,800 seconds. The timeout kills the host
wrapper process group; bwrap's private PID namespace tears down candidate descendants.
The timed direct Lean invocation uses one thread. Prebuilds use Lake's normal scheduling.
CPU/memory/process/disk quotas remain the execution host's responsibility: run this only
inside the same bounded runner/container allocation as trusted builds. The CLI does not
provide a cgroup allocator. Budget workspace output and retain a disk reserve before starting.

`tests/test_profiling.py` adapts upstream threshold, exact-source, and timeout cases and
adds revision/run binding, missing-data, package-tool matching, source-path, and counter tests.
The old symlinked-output/deletion cases become an absent host artifact-reader/deleter plus
read-only dependency isolation. Fresh wheel/source tests run `profile-plan` from a foreign
directory. CI's `scripts/test_profiling_smoke.py` runs the full profiler on two tiny exact Lean
revisions, checks credential isolation and dependency immutability, and exercises an explicit
failed elaboration. It never skips missing or mismatched bubblewrap isolation.
It also profiles a disposable comment-only change to the existing bootstrap module against
the real pinned TauCeti/Mathlib dependency graph, sharing CI's prepared artifacts read-only.
