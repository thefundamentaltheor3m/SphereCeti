# CLI prototype validation

This is the infrastructure validation record. The roadmap's `VALIDATION.md` remains limited to
its mathematical target statements, dependencies and admission audit.

## Combined prototype before the branch split

These results describe the original uncommitted prototype over roadmap commit `39d382b`, not
main's scaffold or any one extracted infrastructure branch:

- On 2026-11-12, a full regression run passed 417 tests, followed by the final 140-test smoke
  after three additional authoring/cleanup regressions and the diagnostic changes.
- The 2026-11-17 review independently ran all 420 tests on that final combined tree, plus the
  default offline smoke, roadmap static checks and whitespace checks; all passed.
- Fresh wheel/source installation and the read-only GitHub queue check passed on 2026-11-12.
  A disposable source copy with review/posting enabled, a nonempty reviewer allowlist and synthetic
  producer IDs passed both the 140-test smoke and wheel/source installation checks. These were
  fixture tests, not live review activation. The reviewer did not rerun these optional stages.
- Timeout regressions cover detached descendants, unrelated process isolation and unsupported-host
  refusal. The helper requires Linux child-subreaper, `/proc` and pidfd support.
- The local sandbox did not pass: this host's bubblewrap bytes differ from the approved pin.
  Positive sandbox and complete candidate-build validation still require the approved CI host.

No provider calls, live review posts, merges or repository-setting changes were made. The original
prototype did not change Lean targets, dependency pins, admission policy, automation policy or
workflows. Its tracked and untracked files are preserved in a stash and a file backup before the
split; `roadmap/initial` stays at the same commit with a clean worktree.

## Independent branches from main

The three branches start from `b81807e`, preserving its scaffold state, unapproved roadmap and
Lean 4.34 dependency line. `deps/lean-4.36-rc2-tauceti-83769e4` separately upgrades that scaffold;
its build/audit results belong to the dependency PR. Branch-specific test counts differ from
the combined prototype because each branch carries only its own implementation and regressions.

On `infra/cli-smoke`, the default smoke passes 115 fixture tests. The independent Python suite
passes 379 tests with `ELAN_TOOLCHAIN=leanprover/lean4:v4.34.0-rc1`, excluding only the 14
`CompiledAuditsTest` cases that require a materialized dependency cache. Fresh wheel and source
installation checks pass via `--package`; neither `--online` nor the sandbox stage was rerun
for this branch split. The separate dependency branch supplies the compatible build/audit check.

The [rollout guide](rollout.md) separates the dependency landing, PR #1 rebase, infrastructure
landing and live review/merge canaries. A saved v2 worker survey remains unauthenticated advisory
input; replay never grants execution or merge authority. The generic GitHub Actions bot ID is
insufficient without the exact workflow/run and PR revision bindings.
