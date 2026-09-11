# Trusted candidate builds (#6)

**Adapted from the TauCeti contributors' work**, particularly
[TauCeti's PR workflow](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/.github/workflows/pr-build.yml),
[configuration attestation](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/attest-pr-config.sh),
[attestation tests](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/test_attest_pr_config.py),
[sandbox build](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/sandbox-build.sh), and
[bubblewrap regression tests](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/test_bwrap_pin.py).
Every link names commit `b743b607ce3e9742b18026ad79082e5d15badff5`.
These sources are Apache-2.0; the [license](../../LICENSE) and attribution headers are retained.
The [source ledger](../../tools/upstream-lock.toml) records destinations and modifications.
The shell attestation and its tests are adapted source; the Python gate, launcher, and workflow
are SphereCeti-specific implementations of that design. Credit for the isolation design,
package/binary pin, and probe requirements belongs to TauCeti.

## Three inputs and two verdicts

The `Trusted candidate` workflow handles PRs targeting `main` after #6 lands there.
It has three distinct inputs:

- **T:** `github.workflow_sha`, the approved base workflow revision. Checkout, policy,
  configuration, sandbox launcher, checker, and build command all come from T.
- **H:** the full PR head SHA recorded in the event. The gate fetches that exact commit,
  reads every tree entry, and materializes raw Git blobs without checkout filters or
  `export-ignore`. Advancing a branch cannot change H during the run.
- **D:** T's unchanged `lake-manifest.json`, `lean-toolchain`, and both possible Lakefile
  spellings. Host preparation builds only T, verifies dependency checkout revisions and
  clean tracked sources, rechecks configuration, then moves dependencies into H's fresh `.lake`.
  Candidate root build artifacts and Lake configuration caches are never restored.

A separate job, with no checkout or candidate execution, posts `trusted-build` and
`trusted-scope` statuses to H. Only that job has `statuses: write`. The build job has
`contents: read`, no persisted checkout credential, and no status/merge token.
The two contexts are intentionally distinct from the existing unprivileged `build` check.
A successful build does not authorize automation or establish mathematical correctness.

The gate compares H against its exact merge base with the event's base SHA for scope, but
compares configuration against **T**, even if the merge base is older. In #6, any dependency
or Lakefile change prevents candidate execution and needs human review. A human can review
and land such a change through ordinary CI; there is no automatic bump exception.
Missing commits, invalid configuration, empty diffs, incomplete Git reads, and unsupported
source entries fail closed. Git trees supply the whole diff, so no GitHub files API page limit
or rename heuristic can hide a protected deletion.

## Scope and review

`SphereCeti/**/*.lean` is potentially mathematical, except the protected `Basic.lean`,
`Pinned.lean`, and `Suggested.lean` contracts. Root aggregators, roadmap targets and documents,
config, tooling, rubrics, workflows, and unknown paths are protected. `STATUS.md` and
`PROGRESS.md` are report paths and still require human review. Every changed path, including
both sides of a rename and mode changes, participates; mixed changes take the restrictive route.

A `mathematical` scope result additionally requires every path to match an allowlist from T's
policy. The shipped allowlist is empty, so **every current PR receives `human_review`** and a
non-success `trusted-scope` status, even when its Lean build succeeds. Neither classification
nor any policy switch in #6 triggers a merge. Candidate policy cannot authorize itself.

Infrastructure PRs test proposed tooling in the existing unprivileged `pull_request` workflow.
That result lets humans review the change; it does not make the proposed tooling authoritative.
The trusted workflow deliberately does not run for stacked PRs targeting unapproved feature
branches. Once a stack is rebased/retargeted onto approved main, the trusted path applies.
The initial #6 PR can test its components in CI but cannot run itself as approved tooling.
Branch protection is unchanged; activating new required contexts is a separate human decision.
In particular, do not require `trusted-scope` for all human infrastructure PRs.

## Sandbox boundary

The launcher verifies the exact Ubuntu 24.04 bubblewrap package/binary pin recorded in
[`bubblewrap.json`](../../tools/ci/bubblewrap.json). The installer grants user namespaces to
that binary through its AppArmor profile. Namespace creation is mandatory, with no fallback
for user, network, PID, IPC, UTS, or cgroup isolation; nested user namespaces are disabled.
As in the pinned TauCeti implementation, candidate symlinks must not influence mount setup.
The complete immutable tree rejects symlinks, submodules, control-character paths, and tracked
`.git`, `.lake`, `.venv`, or `lake-packages` before any host candidate operation.

The launcher itself receives an empty environment. A synthetic read-only root exposes system
runtime files, the approved toolchain, T at `/gate`, and H at `/project`. Only H's newly created
`.lake` is a writable project mount; `/tmp` and `/dev` are private. Host home, runner command
files, host processes, and host network are absent. The build executes T's checker and build
script, never H's helper scripts. Candidate Lean remains arbitrary code inside this boundary.

Before execution, probes require a working sandbox and verify distinct namespaces, empty
PID-1 environment, denied host-network access, an invisible host canary, denied writes to the
root/tools/source/system mounts, a working `.lake` write, and blocked nested namespaces.
A failed or unavailable probe stops before any candidate build. Candidate stdout/stderr is
buffered and emitted with Actions command processing suspended; the resume token is generated
only after the process exits. The build has a 30-minute timeout and the job a 45-minute timeout.
Output/resource exhaustion fails the run rather than yielding a successful verdict.

This is the pinned TauCeti bubblewrap boundary, not a virtual machine or a claim to contain
kernel exploits. #8 will add complete compiled-module/axiom and lint audits. #6 runs the
existing source/import boundary check and the two named Lake targets; it does not yet audit
compiled axioms or force every unimported inventory entry to elaborate. The mathematical
roadmap and the Lean rc1/TauCeti/Mathlib pins are unchanged.

## Validation and diagnosis

```bash
lake env python3 -m unittest discover -s tests -p 'test_*.py'
python3 -I scripts/validate_dependencies.py
```

Git-fixture tests cover immutable heads, protected/mixed diffs, candidate tool/policy edits,
config substitution, large diffs, renames, stale bases, raw materialization, and rejected tree
entries. Attestation tests retain and adapt TauCeti's regression cases. Launcher tests check
credential isolation arguments, approved command selection, output handling, and fail-closed
startup/probes/pin validation.

CI on Ubuntu 24.04 also installs the exact binary and runs
`python3 -I scripts/test_sandbox_smoke.py --toolchain "$(lean --print-prefix)"`.
This mandatory positive smoke performs the real probes and builds disposable Lean fixtures
using T's script despite a failing candidate helper and a host credential canary.
CI then runs `scripts/test_trusted_build_smoke.py`, which exercises the complete checkout
through raw materialization, configuration attestation, dependency staging, and the sandbox.
That CI-only script consumes the checkout's dependency cache after the ordinary build;
it tests proposed tools without posting authoritative statuses. Neither smoke silently skips
unsupported hosts. Locally, a pin mismatch or unavailable network/user namespace is a failed sandbox
prerequisite; do not bypass it to run candidate code on the host.

`trusted_gate.py` and `run_sandbox.py` are internal entrypoints requiring explicitly selected
inputs. Passing a local directory or a SHA to them does not establish that it is approved;
the workflow establishes T. This build layer does not invoke providers or publish reviews.
