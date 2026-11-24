# Intentions: advisory claims on proof targets

An intention is an issue that says "I am proving this declaration". If two people start the same
proof, they find each other. People proving different lemmas proceed side by side. Intentions
are **advisory** coordination between human contributors. They are not part of review records,
the merge decision or merge eligibility, and a PR for a claimed target is still reviewed and
merged on its merits.

The design follows TauCeti's intention workflow
([`1-intention.yml`](https://github.com/TauCetiProject/TauCetiRoadmap/blob/5879d83848be0cfa2f9cac7799e6d0eedb18789b/.github/ISSUE_TEMPLATE/1-intention.yml)
and [`intentions.yml`](https://github.com/TauCetiProject/TauCetiRoadmap/blob/5879d83848be0cfa2f9cac7799e6d0eedb18789b/.github/workflows/intentions.yml)
at TauCetiRoadmap 5879d83) and the `claim` / `disclaim` vocabulary of
[leanprover-community/intentions](https://github.com/leanprover-community/intentions/tree/7d751169354e55ffceb32a9c7622038243772935).
SphereCeti implements it independently (`scripts/intentions.py`) with only the workflow's own
token. It copies no code.

## For contributors

1. Check the [open PRs](https://github.com/thefundamentaltheor3m/SphereCeti/pulls) and the
   [open intentions](https://github.com/thefundamentaltheor3m/SphereCeti/issues?q=is%3Aissue+is%3Aopen+label%3Aintention).
2. If nobody is working on your target, open a **New issue → Intention (one proof target)**.
   Claim **one lemma or declaration**, not a whole roadmap item or layer. For example, the
   counting, averaging, separation and periodicity lemmas all advance D5, and each is a
   separate intention.
3. Comment on the issue, on the comment's first line:

| Comment | Effect |
|---|---|
| `claim` | Assigns you for 30 days. |
| `claim 3 weeks` · `claim 10d` · `claim 2 months` | A custom length, from 1 to 90 days (a month is 30 days). |
| `claim …` again, as the holder | Renews from now. |
| `unclaim` (or `disclaim`) | Releases your claim. A repository owner, member or collaborator can release anyone's claim. |

Anything after the first line is an ordinary note. The bot replies with the effective expiry
date. While someone else's claim is active, a `claim` is refused with their name, expiry and a
link to their claim, so you can coordinate on the issue. A daily job releases expired claims with
a comment, and the previous holder can claim again. Close the issue when the proof lands or the
plan changes.

## How it works

`.github/workflows/intentions.yml` runs `scripts/intentions.py` from the default branch:

- **Triggers:** an `issue_comment` with `comment` mode, and a daily schedule or a manual dispatch
  with `sweep` mode.
- **Credentials and permissions:** the job token only, with `issues: write` and `contents: read`.
  There is no Project board, App or personal token.
- **What runs:** only the script from the default branch, a sparse checkout without persisted
  credentials. No pull-request code is checked out or run.
- **Comment text:** read from the event file as data. It is never interpolated into a command.
- **What is acted on:** comments by a `User` on an open issue labelled `intention`. The workflow
  skips pull-request conversations and bots. The script then reads the issue **live** and acts
  only if it is still open and still labelled. It never uses the assignees or labels in the
  event payload, which can predate a concurrent claim.

### The claim state, and why concurrent jobs are safe

The source of truth is the sequence of **marker comments written by `github-actions[bot]`**,
replayed in comment-ID order (`fold` in the script). Markers in anyone else's comments are
ignored. The replay applies these rules:

- A `claim` or `renew` marker is accepted when the target is free, when it is already held by
  the same person, or when the current claim had expired by the marker's `created_at`.
- A `release` marker applies only to the current holder.
- An `expire` marker applies only if the holder and expiry it `observed` are still current and
  that expiry has passed. If a renewal lands first, the expiry is void.

Every job uses the same compare-and-set steps:

1. Decide from the live issue and the replayed markers. An obvious refusal, such as an active
   claim by someone else, is answered without writing a marker.
2. Write the marker. Its text states the expected result: "alice claimed this intention until…".
3. Re-read all comments and replay them.
4. Make the assignees match the result: the holder is assigned, and earlier claimants are not.
5. If its own marker was not accepted, post a correction. A losing claimant is told who holds the
   claim, until when, and with a link. A sweep that lost to a renewal says the claim was renewed.

Comment IDs give one total order, so every job that replays the same comments reaches the same
answer. Two people claiming at once cannot both hold the target: whoever's marker is first wins,
and the other gets a correction. This holds even when both events said "no assignees".

The workflow deliberately has **no concurrency group**. GitHub keeps only one pending job per
group and cancels it when a newer one arrives, which can drop a command. Separate groups would also
leave the sweep unserialized against claims. Without a group, every comment gets its own job and
an answer.

The assignees are a mirror of the replayed state, not the source of truth. Every job and the daily
sweep put the mirror right. A maintainer who unassigns someone by hand should also comment
`unclaim`; otherwise the next job assigns the holder again. GitHub assigns only collaborators and
people who have commented on the issue. A claimant has just commented, so this normally succeeds.
If GitHub declines, the claim is still recorded, and a reply says so.

```text
<!--sphereceti-intention:v1 {"action":"claim","comment":123,"expires":"2026-12-15T12:00:00Z","holder":"alice","holder_id":11}-->
alice claimed this intention until **2026-12-15** (UTC). …
```

- **Actions and fields:**
  - `claim` and `renew` carry `holder`, `holder_id`, `expires` and the command's `comment` ID.
  - `release` carries `released` (the holder) and `by` (who released it).
  - `expire` carries `released` and `observed` (the expiry it acted on).
  - `release` and `expire` set `holder` and `expires` to `null`.
- **Timestamps:** UTC, in `YYYY-MM-DDTHH:MM:SSZ`. A marker's own time is its API `created_at`.
- **Reading the current claim:** replay the markers. `intentions.fold(comments)` returns the holder
  and expiry. A holder whose expiry has passed is shown as expired until the sweep writes the
  release.

## Machine-readable issue format

The CLI lookup and other tools read intentions without the board. An intention is an open
issue with the `intention` label. Its body is the issue form rendered by GitHub. Each field is a
`### <label>` heading followed by its value, with `_No response_` for an empty optional field.
The headings are the contract. They map to stable form ids:

| Heading | Form id | Content |
|---|---|---|
| `### Target declaration` | `target` | A fenced `lean` block: the declaration name or precise statement (required). |
| `### Roadmap item or layer` | `roadmap_item` | One line, e.g. `D5, layer 4` (required). |
| `### Parent PR` | `parent_pr` | One line, e.g. `#105` (optional). |
| `### Intended module` | `module` | One line, e.g. `SphereCeti/Packing/PeriodicDensity.lean` (required). |
| `### Expected duration` | `duration` | One line, informational only (optional). |

`scripts/intentions.py` provides `parse_intention(body)`, which returns these five keys, with
`None` for an empty field. The claim holder and expiry come from replaying the bot markers with
`fold`, as described above, and the assignees mirror them. A test pins the form's ids and labels
to the parser, so renaming a heading fails the suite. Change both together.

## Label

The form applies the `intention` label, which a maintainer creates once:

- name: `intention`
- colour: `c5def5`
- description: `Advisory claim on one proof target: comment claim, claim 3 weeks or unclaim`

## Why not the upstream action

[leanprover-community/intentions](https://github.com/leanprover-community/intentions) keeps
state on a GitHub Projects v2 board. It needs:

- a board with a `Status` single-select field (`Unclaimed`, `Claimed`, `In Progress`, optionally
  `In Review` and `Completed`);
- a `Claim Expires` text field, and optionally `Claim Note`;
- a credential that can write that board, because the job token cannot write Projects v2. That is
  either a GitHub App (Projects read/write; an App ID variable and a private-key secret) or a
  fine-grained PAT with Projects read/write.

SphereCeti does not use a board, and its owner is a user account. The advisory need is "who is on
this target, and until when". That fits in assignees plus a marker comment, written with the token
every workflow already has. This also keeps one fewer long-lived credential away from the
repository. The cost is no board view and no automatic PR linkage. The issue list filtered by the
`intention` label, and its assignees, serve as the board.
