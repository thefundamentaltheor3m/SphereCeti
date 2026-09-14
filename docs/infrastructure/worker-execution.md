# One worker review round and cooperative leases

This is independently authored SphereCeti code under [Apache-2.0](../../LICENSE). The general
maintenance/targeting requirements were informed by the
[TauCetiWorker contributors' README at `27c234a`](https://github.com/kim-em/TauCetiWorker/blob/27c234a5722cfe557279aa47fbfd8e51450481a6/README.md).
No Worker code, prompts, assets or tests are copied. Execution calls the existing
[TauCetiReview engine at `afb424e`](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b),
Apache-2.0, credited to its contributors: `runner/review.py`, `runner/ledger.py`, `runner/post.py`
and the installed rubrics. Imported source bytes and their manifest stay unchanged.

## Review order and prerequisites

The preceding stack layers supply authenticated review records, archive capture and Worker
planning. This layer adds guarded execution; evaluation and bounded loops build on it.
Review `worker_execution.py`, `worker_leases.py`, the guard/capture changes to `local_review.py`,
and `worker_state.py`. Combined tests exercise the real shared engine with fake providers.

The mathematical roadmap's prose and target statements remain unchanged; substantive proofs
belong in production. All infrastructure lands before roadmap #1.

## Command boundary

```bash
sphereceti worker run --pr 9 --json                  # fresh plan only
sphereceti worker run --pr 9 --execute --worker-id alice \
  --provider claude --budget-usd 5 --max-call-cost 1 --json
# Optional publication flags on an executed round:
# --post-review       publish through the existing authenticated review adapter
# --publish-state     append a bounded outcome receipt to an initialized reviews branch
sphereceti worker sync --receipt /path/to/run/worker-result.json --json
```

All shipped automation switches are false. `run --execute` reports `disabled` without network
or provider calls until the installed policy permits both `review_generation` and `posting`.
Posting permission is needed even without `--post-review`, because coordination uses issue
comments. It is not sufficient on its own: the prepared approved policy must also permit
both, the installed executable/resources must match approved `main`, and the current GitHub
user's immutable ID must be in `authorized_reviewers`. This first adapter supports GitHub
user credentials, not autonomous App installation credentials. No policy, App, branch
protection, repository access grant or deployment is activated by landing this PR.

The supported executable stage is **one review round**. Maintenance recommendations remain
visible, but rebase, CI/dependency repair, progress and review-response code repair have no
execution adapter. Selecting unsupported work stops the round, with no fallback to a
lower-priority PR. There is no persistent loop, fleet manager, dashboard, fork authoring or
area specialization. Mathematical authoring remains unavailable until separately approved
production integration; the optional single-roadmap frontier remains planning-only.

`--pr` has #21's strict narrowing rules. Execution always surveys live GitHub state; there
is no snapshot-to-execution option. A run without `--execute` only plans. `--post-review` and
`--publish-state` require explicit execution. Provider/auth/budget and materialized source-store
options are forwarded to the existing reviewer; execution cannot select prospective tooling,
local-unverified heads, shadow runs, arbitrary rubrics or local contest files.

## Evidence, spending and cancellation

The worker guard runs inside the review adapter, after exact sources and policy have been
prepared and while its shared local store lock is held. It checks planned head/base against
that prepared evidence, rejects configuration changes into the human route, and re-reads the
PR's open/draft status, canonical destination, head, base, title/body and approved main.
Missing mathematical context keeps infrastructure reviews advisory under the existing
record rules; it does not authorize authoring. CI summaries remain planner hints, never a
trusted CI or merge decision. The worker does not replace the merge gate.

Before any lease write, the existing provider/budget validation runs. No provider is chosen
implicitly beyond explicit operator preferences. Authorized current review records and
contests are assessed by the shared engine's existing code. A current approval needs no new
review; an existing negative, stale or malformed selected decision with no contest is sent
to the author/human route. Authenticated contests can trigger one full-rubric reconsideration.
The selected decision/contest set is checked again after lease acquisition. This conservative
adapter does not automatically repair or dismiss a disputed decision.

Provider execution uses the same isolated bridge, exact context, ten rubrics, case files and
shared daily ledger as `sphereceti review`. A worker ID does not create a fresh budget/store.
The cap is local to that operator's configured storage, not a globally enforced billing cap.
The guard rechecks source/policy and lease ownership before launch, every 30 seconds while
waiting, after the provider finishes, and through the existing publication revalidation.
API failure, lease loss, expiry or source drift stops further dispatch/publication; an owned
provider process group still running is terminated. A request already in flight may consume
credits before cancellation. SIGINT and SIGTERM take the owned-process cleanup path. The bridge retains its 30-minute
timeout and five-second kill escalation. HTTP calls retain the shared adapter's 60-second timeout, so cancellation is not
instantaneous when a check itself is waiting on GitHub.

A normal result writes `worker-result.json` beside the shared evidence/record artifacts.
Interrupted rounds retain an explicitly incomplete receipt, an error review/archive record and
completed-attempt accounting. Cancellation or lease loss before publication blocks publication;
a write already submitted requires readback reconciliation. The shared ledger/artifacts remain;
no successful outcome is invented. Review errors return nonzero. A failed optional state
sync is reported separately and does not erase the completed local review or posted record.

## Cooperative lease protocol

Leases are immutable comments on the **same targeted PR**. The marker is
`sphereceti-worker-lease:v1`; comments bind repository, PR, review stage, exact head/base/tooling,
API user identity, worker ID, random claim ID, sequence, predecessor comment and expiry.
No contributor write-access grants or separate claims repository are needed.

- Only policy-authorized API identities participate; body login claims have no authority.
  Edited, misplaced, malformed or incomplete authorized lease histories stop coordination.
- Acquisition posts a five-minute lease, reads the exact body/identity back, then re-reads
  competitors. The earliest active acquisition by API comment ID wins. A losing worker
  releases its own confirmed claim and does not dispatch.
- The heartbeat renews with an append-only successor when at most two minutes remain. A
  renewal must follow its own unexpired predecessor; expired leases cannot be resurrected.
- Completion, failure and cancellation attempt an append-only release. An uncertain release
  is recorded explicitly and the bounded lease expires. An unconfirmed acquisition is never
  retried automatically or treated as permission to launch.
- Different exact revisions have separate claims; old workers detect drift on their next
  guard check. Persistent intentions and mathematical task assignments are separate concepts.

These are cooperative duplicate-work reduction, **not strict exclusion**. Concurrent reads,
visibility delays and an in-flight request can still overlap. Strict exclusion would need a
trusted serialized broker. Leases never establish review acceptance or merge authority.

## Operational `reviews` state

`--publish-state` and `worker sync` append a small immutable receipt to the configured
`reviews` branch. State publication needs repository write access through the already
approved operator; lack of access leaves the local receipt available. This does not grant
that access to other contributors. `sync` retries just the explicit receipt, without a
provider or lease acquisition. It checks current approved identity/policy against installed
resources and verifies the recorded acquisition through GitHub. It can preserve a historical
outcome after a head change; that outcome is still only an operator assertion of what ran.

The branch must be **separately initialized** with the single ordinary UTF-8 JSON file
`sphereceti-state.json`:

```json
{"schema":"sphereceti.worker-state/v1","repository":"thefundamentaltheor3m/SphereCeti","branch":"reviews"}
```

The publisher does not create branches. It rejects a missing/mismatched anchor, unexpected
paths, symlinks and truncated trees. Receipts occupy `runs/<sha256>.json`. Git object IDs,
content-addressed paths and readback are checked; identical retries are adopted. Writes
preserve the existing tree, use the observed parent commit and a non-forced ref update, and
reject concurrent advancement. A race can leave unreachable Git objects but never forces
replacement; retry the explicit receipt after refreshing. A timed-out write is unconfirmed
until a later explicit readback/adoption succeeds.

Only schema, repository, PR, head/base/tooling, completion state, API owner ID, claim and
acquisition comment ID are published. Local paths, worker names, prompts, provider prose,
credentials and budgets are excluded. These records are operational cache/history, **never**
accepted reviews, contests, mathematical completion evidence or inputs to the live merge gate.
They do not replace the separate `review-data` archive/evaluation track.

This supplies the guarded-review milestone of the independent Worker. Operational activation,
unsupported repair stages, fleet/dashboard features and the future production-authoring
adapter remain explicit follow-up work, not features claimed by this PR.
