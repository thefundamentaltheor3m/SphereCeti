# Intentions: what is underway, and claiming a target

An **intention** is an open issue that claims one proof target. The issue form, the `claim` /
`unclaim` workflow, the holder and expiry markers and the format are defined by #134: see
[intentions](intentions.md). This guide covers the read-only lookup and registration from the
CLI. The lookup is modelled on TauCetiWorker's
[intentions board](https://github.com/TauCetiProject/TauCetiWorker/blob/590c3a2a43a162b2ced728a7288ec84f4bde6ab1/tauceti_worker/intentions.py),
independently written. Intentions are advisory and never part of review or merge eligibility.

## `sphereceti intentions` (read-only)

Lists open intentions beside every open proof PR (a PR that adds or modifies a module under
`SphereCeti/`), with each PR's touched modules and the declarations it adds, grouped by roadmap
item (else by module). Work started before intentions existed therefore shows up too.

```text
Work underway in thefundamentaltheor3m/SphereCeti (observed 2026-11-24T14:40:02Z): 1 intention(s), 47 open proof PR(s)
Roadmap item D5:
  intention #200 claimed by alice until 2026-12-24: EuclideanSpace.periodicRepetition_card
  PR #112 by CBirkbeck "Average a finite point set over translates of a coordinate box (Layer " · SphereCeti/MeasureTheory/Measure/Haar/BoxAveraging.lean · adds EuclideanSpace.norm_le_of_mem_centeredBox, EuclideanSpace.exists_encard_mul_volume_centeredBox_le, ...
  PR #105 by CBirkbeck "Count the points of a finite set in the translates of a set (Layer 3, " · SphereCeti/MeasureTheory/Group/LIntegral.lean · adds MeasureTheory.lintegral_encard_inter_vadd, ...
Register an intention: https://github.com/thefundamentaltheor3m/SphereCeti/issues/new?template=intention.yml&labels=intention
```

`--json` prints `sphereceti.intentions/v1`: `intentions` (number, url, title, holders, state
`claimed`/`unclaimed`/`expired`, expires, target, declarations, modules, items, layers,
roadmap_item, duration, parent_pr),
`pull_requests` (number, url, title, author, draft, head, modules, declarations, declared with
each module, items, layers, and `incomplete` for files whose diff GitHub omitted), `groups`
and `register_url`.

## `sphereceti intend TARGET`

`TARGET` is a Lean declaration name, a module (`SphereCeti/A/B.lean` or `SphereCeti.A.B`) or a
roadmap item (`D5`, or `Layer 3`); `--kind` overrides the guess. `--item` and `--module` say where
a declaration belongs, so related work can be shown.

- **Already claimed:** the exact declaration is the target of an open intention (claimed, or
  registered but not yet claimed) whose claim has not expired, or is added by an open PR (equal names, or equal up to a namespace one side did not spell out:
  `lintegral_encard_inter_vadd` matches `MeasureTheory.lintegral_encard_inter_vadd`, but
  `encard_inter_vadd` matches nothing). The claim and its link are printed. An intention names
  one declaration (#134), so a module or roadmap item is never claimed as a whole.
- **No exact claim found:** never "free". A PR from before intentions can prove the same result
  under another name, which no name match finds. The command lists related open PRs and
  intentions (same module or roadmap item) first, then offers registration. Distinct lemmas
  under the same item are related, never claimed: #105, #112, #119 and #120 all advance D5.
- Expired claims are shown as expired and do not block.

**Registering.** With no exact claim, `--register` (or answering `y` on a terminal) creates the
intention issue under your own `gh` identity, in #134's exact body layout (the target in a
```` ```lean ```` block) with the `intention` label, then comments `claim` (or
`claim <duration>` with `--duration "3 weeks"`) as you, so #134's workflow assigns you; claims
last 30 days by default. A declaration target with `--item` and `--module` is required, as the
form requires them; `--parent-pr N` fills that field. `--dry-run` shows the issue and creates
nothing. Registration is post-then-confirm, as for review claims, and counts both issue targets
and claims:

1. Immediately before creating, it re-reads open intentions. An open intention with the same
   target, claimed or only registered, is shown with its link and nothing is written. One whose
   claim has expired is claimed in place (a `claim` comment) instead of duplicated.
2. After creating the issue it reads them again. If an earlier open intention has the same
   target, this one lost the race: the command comments `Duplicate of #N` on its own new issue,
   closes it, posts no `claim`, and prints the winner's link. It never touches anyone else's issue.

Two contributors registering different lemmas of the same item both succeed. The contributor's
token is used only to create the issue and comment `claim`, and after a lost race to comment on
and close that same issue.

Exit codes: 0 for a lookup or a registration, 1 when registration was refused (claimed
meanwhile or a lost race), 2 when GitHub could not be read. A failed read never reports "no
exact claim" and never registers.

## Reading #134's format

An intention is an open issue labelled `intention`, or whose body has the form's required
headings (a contributor without triage rights cannot label an issue created through the API).
`parse_fields` mirrors #134's `scripts/intentions.py:parse_intention`: `### Target declaration`
(`target`, a fenced `lean` block naming one declaration), `### Roadmap item or layer`
(`roadmap_item`, e.g. `D5, layer 4`), `### Parent PR` (`parent_pr`), `### Intended module`
(`module`) and `### Expected duration` (`duration`), with `_No response_` read as empty. A test
pins the mirror to #134's rendered-form fixture and, once #134's script is present, compares the
two parsers. The declaration is the name in the target block (`theorem A.b ...`, or a bare name).

The holder and expiry are #134's: the issue's assignees plus the latest
`<!--sphereceti-intention:v1 {...}-->` marker comment by `github-actions[bot]` (type Bot); markers
by anyone else are ignored. A marker whose holder is still assigned and whose `expires` has not
passed means claimed; a passed expiry not yet swept means expired; an open intention without such
a claim is "registered, unclaimed" and still blocks its exact target. Prefilled form links use
#134's ids (`target`, `roadmap_item`, `module`, `parent_pr`, `duration`) with `template=intention.yml`.

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
