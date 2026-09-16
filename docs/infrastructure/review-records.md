# Review records, authentication, and explicit posting

**Adapted from the [TauCetiReview contributors](https://github.com/TauCetiProject/TauCetiReview)
at [afb424e](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b),
Apache-2.0:** [`runner/post.py`](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/runner/post.py)
supplies the separate publication phase and confirmed-write discipline;
[`runner/merge_from_scoreboard.py`](https://github.com/TauCetiProject/TauCetiReview/blob/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/runner/merge_from_scoreboard.py)
supplies the scoreboard/supersession design. SphereCeti adds exact evidence binding,
API identity checks, strict parsing, and its own contest/replacement rules. The original
import and upstream tests remain unchanged in [#9](https://github.com/thefundamentaltheor3m/SphereCeti/pull/9).
The adapter extends [#10](https://github.com/thefundamentaltheor3m/SphereCeti/pull/10).

## Commands and activation boundary

```bash
# Local review: creates result.json, advisory.md, record.json, and record.md.
sphereceti review 9 --provider codex --budget-usd 5

# Inspect current records through GitHub without invoking a provider or posting.
sphereceti review 9 --read-records --json

# Explicitly review and publish, only when approved repository policy permits it.
sphereceti review 9 --provider codex --budget-usd 5 --post
```

`--post` is incompatible with dry runs and locally supplied source references. The approved
remote-main policy must enable `posting`; a candidate policy or operator preference cannot
enable it. The shipped policy still has `posting = false` and no authorized reviewers.
No publishing occurs during tests or installation. No code in this PR merges anything,
creates Apps, grants permissions, or changes branch protection.

The CLI runs providers in the existing isolated engine subprocess. Publishing and record
inspection run in the parent, with GitHub credentials absent from the engine/provider
environment. The GitHub client fixes the hostname to `github.com`, requires complete paginated
comment responses, and treats API errors as errors. It never falls back to an empty queue.
Provider-specific isolation limits remain those documented for the [local adapter](local-review.md).

## What a record attests

`review_records.py` renders one strict versioned envelope at the start of a comment. It carries
repository/PR, head, integration base, diff base, dependency digest, full tooling revision,
installed tooling digest, effective engine/rubric/policy digests, review-context and PR-description digests,
completion, execution mode, ten verdicts, and per-rubric contest watermarks. The content ID
binds those fields and the exact rendered summaries/findings. Provider prose is escaped so it
cannot inject another machine marker. Duplicate fields/markers, unknown schemas, bad types,
and altered rendered bodies are rejected; there is no legacy-table fallback. Oversized
records fail instead of publishing truncated evidence.

A local file is only an attestation proposal. A content hash provides integrity, not identity
or proof that inference ran. A trusted publisher is responsible for the attestation it posts.
Readers obtain the comment's immutable user ID, App ID, type, location, and timestamps from
GitHub's API; body text and display names cannot supply these facts.

Approved `authorized_reviewers` entries use `user:12345` or `app:12345`. An App entry requires
both an API-reported Bot author and matching `performed_via_github_app.id`. A user-to-server
App token represents its user, not the designated bot. These identities follow GitHub's
[issue-comment API](https://docs.github.com/en/rest/issues/comments) and
[App user authentication model](https://docs.github.com/en/apps/creating-github-apps/authenticating-with-a-github-app/authenticating-with-a-github-app-on-behalf-of-a-user).
Authorization is always checked against the current approved policy; removing an identity
revokes its records' authority. App installation/token setup remains an operator action.

Only a complete normal/manual review with matching installed tooling, approved context,
all required documents, and unchanged candidate configuration can propose a non-advisory
record. Partial, errored, shadow, reply-only, prospective, and missing-context results remain
advisory. Publication by an unauthorized identity also cannot qualify, even if the body
claims completeness. Every local result and publication receipt retains `merge_eligible: false`.

## Freshness and publication

Immediately before POST, the parent refreshes remote references and materializes exact source
objects again. It compares all effective evidence, base/head, and policy bindings, checks that
posting is still permitted, and verifies that the reviewed tooling is an ancestor of approved
main. A changed policy, integration base, head, or evidence stops publication. A final reference
read follows materialization. The GitHub API has no atomic head-conditioned issue-comment POST;
a subsequent race can leave a stale comment, but a reader's current-state check rejects it.

An unrelated main-branch mathematics commit does not change the effective policy/tooling
content digest. An older recorded tooling revision remains usable only when GitHub confirms
it is an ancestor of current approved main and all effective bindings still match. Changed
conventions, README/specification, PR description, source locks, dependencies, tools, or audit policy invalidate
the affected record. Provider choice is not a repository policy change.

The poster creates a new issue comment and reads it back. Only an exact body, confirmed ID,
correct repository/PR, and unedited API timestamps produce a receipt. It never edits another
reviewer's comment, publishes the old TauCeti scoreboard marker, or runs a model during
publication. Before a write, an exact unedited authorized record can be adopted after an
ambiguous earlier POST. Independent machines can still produce cosmetic duplicates; the
same content ID does not reset contests or change the decision. Local artifacts survive a
publication failure. Durable outbox/archive synchronization is a separate planned PR.

## Replacement reviews and contests

A newer complete non-advisory record supersedes the same publisher's earlier decision at the
same head. A different publisher cannot erase that publisher's blocker. Advisory/partial
records cannot supersede authorized decisions. An edited or malformed authorized record is
a barrier to reusing older approval; append a fresh complete record to replace it. Publication
never PATCHes records. GitHub administrators can delete comments; this layer has no immutable
archive and relies on the live API inventory, with durable history belonging to the archive PR.

A PR author or currently authorized reviewer can contest a known record by posting an issue
comment beginning with this marker and then the contest text:

```text
<!--sphereceti-contest:v1 {"comment":12345,"record":"FULL_RECORD_CONTENT_ID","rubric":"correctness"}-->
Please reconsider the finding because ...
```

The comment ID identifies the specific publisher's record, even if another publisher attests
to identical content. The parent obtains author identity and comments from GitHub; outsider, edited, unknown-record,
and other-head contests do not qualify. A valid contest prevents that publisher's review
from being safe until a subsequent complete record demonstrates that the relevant rubric
adjudicated its comment ID. A new same-head record alone does not clear the contest.

For `--post`, the adapter supplies API-identified contests to the existing engine's author-reply
path and uses manual mode when contests exist. The engine's `last_reply_seen` watermarks enter
the record. Local `--reply-file`/`--replies-json` inputs remain available for advisory work but
cannot be supplied alongside `--post`. Subset or budget-truncated runs remain advisory even
when they adjudicate one contest. Human replies contain untrusted prose, not policy.

## Review evidence is one input

`--read-records` returns `review_safe` and concrete denial reasons. It checks approved current
context, full records, API authorization, staleness, supersession, and contests. It always
returns `merge_eligible: false`: trusted build/scope producer checks, the compiled audits from
[#8](https://github.com/thefundamentaltheor3m/SphereCeti/pull/8), branch protection, and path
eligibility are inputs to the later shared merge-decision PR. A green record does not claim
that the mechanical checks passed. Infrastructure/specification changes still require humans.

See [tracking issue #23](https://github.com/thefundamentaltheor3m/SphereCeti/issues/23) for review order, prerequisites and landing status. All infrastructure lands before roadmap #1.

## Validation

Pure regression tests cover schema/body forgery, API user/App identity, every stale binding,
policy revocation, unapproved tooling, advisory modes, edited records, per-publisher replacement,
and authenticated contests. Fake-GitHub/fake-provider CLI tests exercise explicit publication,
read-only inspection, policy denial before inference, and head advancement before POST. Both
fresh wheel and source installations exercise the same paths outside the checkout. No tests
invoke paid inference or publish real GitHub comments.
