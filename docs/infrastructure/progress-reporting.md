# Progress reporting adapter

The preceding stack layers supply the Progress sources and documentation evidence. This
adapter bundles and consumes those resources from the same checkout.

**Credit: [TauCetiProgress contributors](https://github.com/TauCetiProject/TauCetiProgress),
Apache-2.0, at [880e8b9](https://github.com/TauCetiProject/TauCetiProgress/tree/880e8b9737973bfbd8f1f214f4ac2ded67f5b856).**
The adapter executes the original [file renderers/validators](https://github.com/TauCetiProject/TauCetiProgress/blob/880e8b9737973bfbd8f1f214f4ac2ded67f5b856/progress/files.py)
and [first-parent window algorithms](https://github.com/TauCetiProject/TauCetiProgress/blob/880e8b9737973bfbd8f1f214f4ac2ded67f5b856/progress/window.py),
and carries forward the [plan/cadence](https://github.com/TauCetiProject/TauCetiProgress/blob/880e8b9737973bfbd8f1f214f4ac2ded67f5b856/progress/plan.py)
and [prose-context](https://github.com/TauCetiProject/TauCetiProgress/blob/880e8b9737973bfbd8f1f214f4ac2ded67f5b856/progress/context.py)
design. Original prompts, license, source and all 11 regression scripts remain unchanged in #12's
bundle. Its operational launchers and transports remain inactive.

The root wheel bundles `tools/progress` from the same checkout. Source distributions include
that tree too, so rebuilding a wheel never fetches a second SphereCeti revision. The upstream
commit and import manifest remain pinned; draft evidence binds the manifest digest instead
of a historical SphereCeti packaging commit. Regenerate older local drafts before validation.
Review the source import and documentation evidence before the adapter and its packaging
integration. Both prerequisites are ordinary ancestors in the serialized stack.

At runtime, `progress_sources.py` verifies the fixed manifest digest and all 32 resource hashes,
then loads only `files.py` and `window.py` in private module namespaces. The window algorithms
receive a restricted read-only Git process transport with timeouts, no inherited credentials,
no replacement objects/lazy network fetching, and external helpers disabled. No global `progress`
package is installed. The provenance ledger records the same-tree resource integration.

## Local workflow

Install the project with its bundled sources with `uv sync --locked`. Use a local source checkout
with the documented commits available and a generated `docs/` tree from #13 as fixture input.
The source checkout's `HEAD` is the report baseline. Drafts are written to a new directory outside
that checkout; the commands never update its roadmap, reports, branches, or GitHub state.

```sh
uv run --locked sphereceti progress plan --repo /path/to/checkout \
  --evidence-dir /path/to/publication/docs --from <full-initial-cursor> --json

uv run --locked sphereceti progress prompt --repo /path/to/checkout \
  --evidence-dir /path/to/publication/docs --from <full-initial-cursor>

uv run --locked sphereceti progress prepare --repo /path/to/checkout \
  --evidence-dir /path/to/publication/docs --from <full-initial-cursor> \
  --prose /tmp/report-prose.json --output /tmp/report-draft --json

uv run --locked sphereceti progress validate --repo /path/to/checkout \
  --evidence-dir /path/to/publication/docs --draft /tmp/report-draft --json
```

`report-prose.json` has exactly `status` and `progress` text fields plus `citations`, a list of at
most five declaration names from the plan's context. The prompt gives the prose bounds and
project-specific instructions before the original TauCeti reference prompts. Supply prose yourself
or through a separately chosen writing tool; this adapter invokes no model or provider. The
renderer owns framing, cursors, PR numbers, classifications and links. Prose cannot supply HTML,
reserved markers or arbitrary links. Validation checks format and evidence bindings, not the truth
of free prose; a human still reviews it.

The output contains `plan.json`, `prose.json`, `prompt.txt`, and exactly two proposed changes under
`changes/`: replaceable `STATUS.md` and append-only `PROGRESS.md`. It is a reviewable local artifact,
not publication. Validation regenerates the expected bytes and rereads current source/evidence;
a changed plan, stale cursor, altered context, changed report baseline, or extra path is refused.
To check an actual candidate Git commit, add `--candidate <full-candidate-sha>` to `validate`.
That commit must descend from the plan baseline, change exactly the two root report files, and
match the validated bytes. README/roadmap edits, symlinks, executable reports and unrelated paths
are rejected. No command commits or copies the draft into the checkout.

## Evidence and window contract

The adapter understands #13's declaration-reference schema, not a guessed Lean source parser:

- Read `SOURCE_SHA` before and after the declaration index, audit and module pages. Require exact
  cursor bytes and a consistent snapshot. Reject redirects, oversize responses, malformed/duplicate
  JSON, unexpected repositories, changed dependency pins and missing declaration anchors.
- Bind the index to the compiled audit digest. Require complete declaration coverage, module
  ownership, exact axiom sets, matching counts and the expected target/library classification.
- End the window at the actually documented revision, even when local `HEAD` is newer. Require
  it to be in local history. An ahead, missing or rewritten cursor fails instead of skipping work.
- Initialize the first window only with an explicit full `--from` revision. Subsequent windows use
  the last `PROGRESS.md` cursor; a contradictory override is refused. Require status/progress
  agreement, contiguous windows and no repeated PRs.
- Use TauCetiProgress's first-parent PR selection. PR numbers come from accepted commit subjects;
  they are reporting attribution, not API authentication of pull requests. Local fixtures carry
  no publication authority.
- Include compiled declarations in changed modules as context. The schema lacks declaration
  positions, so the adapter does not claim that every such declaration was introduced in the
  window. No approximate declaration parser or line-attribution guess is substituted.
- Measure the minimum reporting interval from the last commit that touched `PROGRESS.md`, not
  its display timestamp or a local model run. `no_changes` and `not_due` do not advance a cursor.

The current repository is a roadmap package. All plans have `production_evidence: false`, an empty
`achievements` list, and an explicit missing-production-evidence entry. Roadmap declarations remain
targets even without admissions; admission-dependent library glue retains its label. Draft framing
states that these are not proved production milestones. #13's current scaffold has zero owned
declarations; this is represented honestly rather than filled with invented achievements.

## Published reads and activation

`policy/reporting.toml` is accepted project policy, packaged with the adapter. Its `docs_url` is
empty by default; a normal `progress plan` reports missing published evidence and exits with status
1 without querying Git. `--evidence-dir` enables an explicitly untrusted fixture preview, never a
substitute for published evidence. Operator preferences and cwd files cannot override the accepted
endpoint or source identity.

After #13 is actually deployed, a reviewed policy change can set its plain HTTPS documentation
base URL. The reader fetches it anonymously and follows its actual cursor, not the latest Git
branch or deployment time. Production milestones still require a separately approved production
documentation adapter; a self-asserted `production_evidence: true` is rejected by this schema.

`publication_allowed` remains false even with a configured read endpoint. The existing automation
reporting switch remains off. There is no reporting push/post command, notification workflow,
provider invocation, or automatic cadence scheduler in this PR. Code installation, evidence
publication, human-reviewed report changes and automation activation remain distinct steps.

## Validation and review tracks

```sh
uv run --locked python -B -m unittest discover -s tests -p 'test_progress_adapter.py' -v
uv run --locked python -I scripts/run_progress_tests.py
uv lock --check
uv build
python3 scripts/test_package.py
```

The upstream harness runs all 11 unchanged scripts (232 checks) offline in disposable Git fixtures.
Adapter regressions cover published-revision lag, malformed evidence, classification/link forgery,
local drafts, cadence, byte-exact appends, stale state and real candidate-path scope. Fresh wheel and
source installs exercise the CLI from a foreign cwd with conflicting local configuration.

All infrastructure lands before roadmap #1. The live landing map belongs in the
infrastructure tracking issue, not in this guide.
