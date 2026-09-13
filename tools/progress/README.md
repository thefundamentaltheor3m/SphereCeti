# Inactive TauCetiProgress source import

This import prepares the source and regression baseline for the reporting adapter. Source
import and local adaptation remain separate review units in the serialized infrastructure stack.

**Credit: [TauCetiProgress contributors](https://github.com/TauCetiProject/TauCetiProgress),
Apache-2.0, pinned at [880e8b9](https://github.com/TauCetiProject/TauCetiProgress/tree/880e8b9737973bfbd8f1f214f4ac2ded67f5b856).**
Their source-window selection, published-documentation reader, report validation, prompts, and
regression tests form this baseline. [LICENSE](LICENSE) and [UPSTREAM-README.md](UPSTREAM-README.md)
are verbatim upstream files. The latter describes historical TauCeti behavior, not enabled
SphereCeti commands or deployment instructions.

## Review the source, then the boundary

The first commit copies 32 files verbatim. The second adds the inactive boundary and local checks.
[import-manifest.json](import-manifest.json) records the exact repository, commit, source paths,
Git modes/blob IDs, upstream SHA-256, and adapted SHA-256 for every file.

| Pinned upstream path | Local path | Treatment |
| --- | --- | --- |
| `progress/` | `progress/` | Source and prompts; seven modules have explicit refusal guards |
| `tests/` | `tests/` | All 11 test scripts, runner, and HTML fixture unchanged |
| `.github/scripts/collect.py` | `fixtures/collect.py` | Script/main entry refused; helpers retained for fixture tests |
| `LICENSE` | `LICENSE` | Unchanged Apache-2.0 license |
| `README.md` | `UPSTREAM-README.md` | Unchanged historical documentation |
| `pyproject.toml` | `upstream-pyproject.toml` | Unchanged historical packaging reference |

No upstream workflows are imported. `cli.py` refuses direct execution and its due/plan/apply/announce
commands; `apply.py` refuses its orchestration and subprocess helper; `announce.py` refuses
publication; `gh.py`, `docs.py`, and `zulip.py` refuse their live transports; `zulip.from_env`
refuses before reading credentials; `gate.main` refuses invocation. GitHub refusal uses upstream's
`GhError` so existing optional-identity fallback behavior remains testable.

These are explicit inactive entry points, not a sandbox for arbitrary Python. Pure helpers and
fixture-oriented APIs remain callable, including local Git history readers and injected Docs
openers. No installed `progress` command or global `progress` package is provided. The separate
`sphereceti-progress-sources` package exposes only a resource accessor, `source_root()`, for the
source bundle. Upstream defaults are retained as historical source, not SphereCeti configuration.

## Check locally

From the repository root, with Python 3.11+, Git, and uv 0.10.4:

```sh
python3 -B -m unittest discover -s tests -p 'test_progress_import.py' -v
python3 -I scripts/run_progress_tests.py
uv lock --project tools/progress --check
uv build tools/progress
python3 -I scripts/test_progress_package.py
```

The harness runs all 11 unchanged upstream scripts (232 checks), each in a fresh interpreter and
disposable Git fixture. It clears inherited credentials/configuration, disables Git transport,
hooks, signing and external diff drivers, and denies sockets, non-fixture subprocesses, and writes
outside the fixture. An attempted forbidden operation fails the run even if the script catches
it. Upstream's `/nonexistent` cache sentinel is modeled with `PermissionError`, without touching
that host path. The audit hook catches accidental calls in cooperative tests; it is not a
hostile-code isolation boundary. Tests use canned documentation and fake publication clients.

Fresh wheel and source installs verify every imported resource hash from a foreign working
directory, including original prompts, tests and license, and check that no command is installed.
The separate `Progress sources` workflow runs these checks with read-only repository permissions.
Package tooling may download build dependencies; regression scripts do not contact external services.

## Review and packaging boundary

Review the faithful source import separately from the reporting adaptation. Reporting #14
combines these unchanged resources with #13's documentation evidence and bundles them from
the same source tree in the root distribution. The standalone source-package build and
manifest/fresh-install checks remain useful import validation. Historical launchers stay inactive.

See [tracking issue #23](https://github.com/thefundamentaltheor3m/SphereCeti/issues/23) for review order, prerequisites and landing status. All infrastructure lands before roadmap #1.
