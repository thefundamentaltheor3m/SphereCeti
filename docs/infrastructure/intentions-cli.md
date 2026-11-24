# Intentions: what is underway, and claiming a target

Modelled on TauCetiWorker's [intentions board](https://github.com/TauCetiProject/TauCetiWorker/blob/590c3a2a43a162b2ced728a7288ec84f4bde6ab1/tauceti_worker/intentions.py):
an **intention** is an open issue that claims a proof target. It is advisory coordination between
contributors, issue-backed, and never part of review or merge eligibility. The implementation is
independently written.

## `sphereceti intentions` (read-only)

Lists open intentions beside every open proof PR (a PR that adds or modifies a module under
`SphereCeti/`), with each PR's touched modules and the declarations it adds, grouped by roadmap
item (else by module). Work started before intentions existed therefore shows up too.

```text
Work underway in thefundamentaltheor3m/SphereCeti (observed 2026-11-24T14:40:02Z): 1 intention(s), 47 open proof PR(s)
Roadmap item D5:
  intention #200 claimed by alice until 2026-12-08: EuclideanSpace.periodicRepetition_card
  PR #112 by CBirkbeck "Average a finite point set over translates of a coordinate box (Layer " · SphereCeti/MeasureTheory/Measure/Haar/BoxAveraging.lean · adds EuclideanSpace.norm_le_of_mem_centeredBox, EuclideanSpace.exists_encard_mul_volume_centeredBox_le, ...
  PR #105 by CBirkbeck "Count the points of a finite set in the translates of a set (Layer 3, " · SphereCeti/MeasureTheory/Group/LIntegral.lean · adds MeasureTheory.lintegral_encard_inter_vadd, ...
Register an intention: https://github.com/thefundamentaltheor3m/SphereCeti/issues/new?template=intention.yml&labels=intention
```

`--json` prints `sphereceti.intentions/v1`: `intentions` (number, url, title, holders, state
`claimed`/`unclaimed`/`expired`, expires, declarations, modules, items, parent_pr),
`pull_requests` (number, url, title, author, draft, head, modules, declarations, declared with
each module, items, layers, and `incomplete` for files whose diff GitHub omitted), `groups`
and `register_url`.

## `sphereceti intend TARGET`

`TARGET` is a Lean declaration name, a module (`SphereCeti/A/B.lean` or `SphereCeti.A.B`) or a
roadmap item (`D5`, or `Layer 3`); `--kind` overrides the guess. `--item` and `--module` say where
a declaration belongs, so related work can be shown.

- **Already claimed:** the exact declaration is in an open, unexpired intention, or is added by an
  open PR (equal names, or equal up to a namespace one side did not spell out:
  `lintegral_encard_inter_vadd` matches `MeasureTheory.lintegral_encard_inter_vadd`, but
  `encard_inter_vadd` matches nothing). The claim and its link are printed. A module or item is
  claimed only by an intention for the whole module or item.
- **No exact claim found:** never "free". A PR from before intentions can prove the same result
  under another name, which no name match finds. The command lists related open PRs and
  intentions (same module or roadmap item) first, then offers registration. Distinct lemmas
  under the same item are related, never claimed: #105, #112, #119 and #120 all advance D5.
- Expired claims are shown as expired and do not block.

**Registering.** With no exact claim, `--register` (or answering `y` on a terminal) creates the
intention issue under your own `gh` identity, in the issue form's format, and prints its URL.
`--dry-run` shows the issue and creates nothing. `--parent-pr N` and `--expires YYYY-MM-DD`
(default 14 days) fill those fields. Registration is post-then-confirm, as for review claims:

1. It re-reads open intentions immediately before creating the issue; an exact claim that
   appeared meanwhile is shown with its link and nothing is written.
2. After creating the issue it reads them again. If an earlier open intention claims the same
   target, this one lost the race: the command comments `Duplicate of #N` on its own new issue,
   closes it, and prints the winner's link. It never touches anyone else's issue.

Two contributors registering different lemmas of the same item both succeed. The token is used
only to create the issue and, after a lost race, to comment on and close that same issue.

Exit codes: 0 for a lookup or a registration, 1 when registration was refused (claimed
meanwhile or a lost race), 2 when GitHub could not be read. A failed read never reports "no
exact claim" and never registers.

## The issue format (shared with the intention issue form)

An intention is an open issue labelled `intention`, or whose body has the form's headings (a
contributor without triage rights cannot label an issue created through the API). Its body is the
issue form's rendering, `### <label>` sections in this order; the field ids prefill the form:

| Field id | Label (heading) | Value |
|---|---|---|
| `declarations` | Declarations | fully qualified Lean names, one per line |
| `roadmap_item` | Roadmap item | a MIGRATION PR id such as `D5` |
| `module` | Module | `SphereCeti/A/B.lean` |
| `parent_pr` | Parent PR | `#123` |
| `expires` | Claim expires | `YYYY-MM-DD` (UTC, end of day) |

Unanswered fields read `_No response_`. Assignees are the claimants: an unassigned intention is
registered but unclaimed (it still blocks the exact declaration until it expires or closes).

## How a PR's declarations and roadmap item are read

For each `.lean` file under `SphereCeti/` that a PR adds or modifies, the command reads the file at
the PR head and the diff's added lines, and records every `theorem`, `lemma`, `def`, `abbrev`,
`structure`, `class`, `instance` or `inductive` that starts on an added line (attributes and
`private`/`protected`/`noncomputable` modifiers allowed). Names are qualified by the enclosing
`namespace` blocks of the whole head file; `_root_.` escapes them; anonymous instances are skipped;
comments and docstrings are ignored. A PR's roadmap items come from its title's
`(Layer N, X ...)`, else from `PR X` citations in its body (e.g. `MIGRATION [PR D5]`).

## Reuse before spending model time

`sphereceti.intentions.lookup(project, target, item=..., module=...)` is the same check as a
function. It returns `verdict` (`claimed` or `no_exact_claim`), `claimed` and `related`, and
raises when GitHub cannot be read. The planner and the authoring handoff of #31 would call it
for each candidate declaration before dispatching a model: skip a `claimed` target, pass the
`related` list into the prompt as work to avoid duplicating, and register an intention (with
`register`) before starting, so concurrent authors see the claim.
