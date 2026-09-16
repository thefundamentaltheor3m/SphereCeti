# Durable review archive

**Adapted from the [TauCetiReview contributors](https://github.com/TauCetiProject/TauCetiReview),
Apache-2.0, at [afb424e](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b):**
[`runner/archive.py`](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/runner/archive.py)
supplies the immutable outbox, redaction, compressed blobs, retry, and readback design;
[`runner/review.py`](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/runner/review.py)
supplies the licensed per-run producer;
[`runner/post.py`](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/runner/post.py)
supplies the separation of review publication and archival failure. The imported engine,
manifest, and legacy disabled sync launcher are unchanged.

[TauCetiData](https://github.com/TauCetiProject/TauCetiData) remains the planned source for
later evaluation tooling. Its pinned `schema/`, `scripts/`, and `docs/` at
[e8e9154](https://github.com/TauCetiProject/TauCetiData/tree/e8e915472b02875f9a3864492616662c0c902876)
have unresolved reuse terms. This PR copies none of its code, schemas, records, or history.
The versioned JSON schema and SQLite tables here are independently authored SphereCeti adapters.

## Review boundary

This layer consumes the preceding authenticated review-envelope contract and licensed
producer. Review capture, the immutable journal, and sync confirmation before Worker execution.

## Local use

Every executed `sphereceti review` now stages the upstream per-run archive privately and
queues a metadata-only SphereCeti projection before optional comment publication. Dry runs
and record inspection do not enqueue. `result.json` reports `archive.state`, record path,
observed run count, and whether text was included. An archive failure records `state: error`;
it neither changes a review verdict nor undoes a posted comment. Retain the output and retry:

```bash
sphereceti archive enqueue --output /path/to/completed-review --json
sphereceti archive preview --json
sphereceti archive sync --json                 # local preview, no network
sphereceti archive rebuild --output /tmp/reviews.sqlite --json

# Explicitly opt in to archiving redacted rendered review prose locally.
sphereceti archive enqueue --output /path/to/completed-review --include-text --json

# Explicit remote sync, denied by the shipped policy before any network request.
sphereceti archive sync --apply --json
```

All commands accept the existing `--operator-config` preference file. Storage is below
`storage/OWNER__REPOSITORY/archive/`: `journal/` keeps local immutable copies, `outbox/` holds
pending copies, and `.lock` coordinates enqueue/drain. Output, journal, and outbox are private
operator-owned directories. They must not be writable by another local user or provider.
Files use exclusive immutable installation and file/directory fsync. Symlinks and special
files are rejected. Interrupted staging fails closed; re-enqueue the retained review output
to repair a partial batch. No retention/garbage-collection command deletes the journal.

## Fields, text, and authority

`records/<sha256>.json` contains a versioned archive record, a per-execution UUID and UTC finish
time, #11's review metadata, observed run facts, and an optional redacted-text hash. The review
metadata retains repository/PR, exact head/base/diff-base/tooling revisions, dependency,
engine/rubric/tooling/policy/context/description digests, completion/mode/advisory status,
verdicts, contest watermarks, and original body/record digests. Enqueue verifies the original
rendered envelope and matching local result before discarding its prose by default.

The [evaluation extension](evaluation.md) adds v2 records with exact run start times and
explicit request/context/budget facts. V1 records remain readable; older readers reject v2
and need an approved tooling upgrade. The branch anchor remains v1.

Run records retain provider/model/rubric identifiers, upstream run ID, prompt policy and
prompt hash, price-table identifier, duration, known numeric token fields, recorded cost and
estimated-cost flag. Attempts retain their own model, elapsed time, exit code, numeric usage,
and cost facts. Attempt spend must not be added to a run total again. Missing usage or cost
stays unknown; absent producer records do not claim zero spend or complete accounting.
Cached/skipped rubrics may have no new run. Unknown producer fields are omitted; unknown
SphereCeti schema fields are rejected. Raw stderr, session IDs, provider replies, tool traces,
diffs, filesystem paths, and submitted-by prose are never copied into the public projection.

Optional text is only the rendered review body, without the encoded envelope. The adapter
redacts known credential patterns and home-directory usernames before hashing/compression.
Redaction cannot detect every private fact: inspect prose before using `--include-text`.
`blobs/aa/<sha256>.gz` hashes the redacted UTF-8 bytes and uses reproducible gzip headers.
Remote text publication additionally requires approved `publish_text = true`.

These are analytics copies, not authenticated GitHub receipts or merge inputs. Content hashes
prove integrity, not who ran inference. The live #11 reader still obtains publisher identity,
comment freshness, and contests directly from GitHub. Archive sync does not replay or edit
review comments, persist publication receipts, or grant authority to local files.

## Publication and state branches

The fixed destination is the configured SphereCeti repository's existing `review-data`
branch. Executable code and policy stay on `main`; `reviews` remains reserved for operational
review state. This PR does not upload the local engine ledger, provider caches, or credentials
to either branch. Operational-state publication belongs to the later worker integration.

An operator must separately provision a data-only branch with this exact canonical anchor
(one line, sorted keys, no spaces, followed by a newline):

```json
{"branch":"review-data","repository":"thefundamentaltheor3m/SphereCeti","schema":"sphereceti.archive/v1"}
```

Save it as `ARCHIVE.json`. Do not copy source files or a SQLite database into that branch.
This PR creates no live branches, workflows, credentials, or repository settings.

Remote writes require explicit `--apply`, `policy/archive.toml`'s `enabled = true`, and
`policy/automation.toml`'s `posting = true`. Both ship false. The publisher compares installed
modules, engine resources, profile, source lock, and policies with the exact remote-main Git
tree before uploading and immediately before updating the archive ref. Candidate files,
working-directory config, or operator preferences cannot enable publication. Install the
approved version after any policy change. Credentials remain in the parent `gh` process;
the provider environment never receives them.

The publisher reads branch tips and exact Git tree/blob objects through the fixed github.com
API; it does not clone state history or check out any archived files. It rejects missing
anchors/branches, truncated inventories, non-regular files, unknown paths/schemas, bad hashes,
unreferenced/missing blobs, and conflicting facts for one execution ID. Current bounds are
2,000 files, 1 MiB per file/decompressed blob, and 64 MiB total; exceeding them requires a
reviewed scaling change, not silent truncation.

New immutable objects form a commit with the observed archive tip as its parent. GitHub's
[non-force reference update](https://docs.github.com/en/rest/git/refs#update-a-reference)
rejects a concurrent divergent tip. The adapter re-reads and retries at most three times,
preserving both writers' entries. An ambiguous update response triggers readback; only exact
confirmed bytes permit draining. Concurrently queued records, including those sharing a blob
with the submitted batch, remain pending. Journal copies remain after success. Administrative
force-pushes/deletions are outside this append-only protocol; branch protection is a separate
setup action. GitHub does not provide an atomic transaction across main-policy reads and the
archive ref update, so activation must account for that final revocation race.

## Derived database and validation

`rebuild` validates the complete selected local tree before creating a new SQLite file
outside the archive/state directories. `--source` can select a separately obtained archive
snapshot instead of the journal. Invalid input never becomes a partial successful database.
`records` tracks each immutable projection; `executions` and `runs` count a repeated enqueue
or optional-text variant only once per execution. Distinct executions retain separate costs.
Unknown costs are SQL NULL. Original numeric facts and evidence remain in JSON columns;
SQLite is replaceable, derived, and never included in publication.

Tests use fake providers and a disposable real Git object store behind the GitHub API seam.
They cover source/schema forgery, field filtering, text opt-in, decompression bounds, duplicate
accounting, outages, ambiguous success, concurrent branch advancement, shared-blob drain races,
policy revocation, and installed-tooling mismatch. Fresh wheel/source installations exercise
capture, preview, rebuild, and disabled sync outside the checkout. No test invokes paid
inference or writes to GitHub.
