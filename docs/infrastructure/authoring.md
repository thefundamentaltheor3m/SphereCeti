# Local authoring handoffs

`sphereceti author plan` prepares one bounded production task for an external author tool.
It reads exact objects from two explicit, fully materialized local Git repositories. It never
fetches, invokes a provider, executes source code, creates a checkout, or publishes anything.
Working-tree edits do not affect the evidence; a clean working tree is not required.
The current scaffold has no installed, approved target file. Use an explicitly selected local
revision containing the configured roadmap sources; the command never treats PR #1 or its
contents as approved. Tests create their own fixture targets and do not depend on that PR landing.

```bash
sphereceti author plan \
  --roadmap-repo /path/to/SphereCeti --roadmap FULL_ROADMAP_SHA \
  --implementation-repo /path/to/Sphere-Packing-Lean --implementation FULL_PRODUCTION_SHA \
  --reference README.md#exact-existing-heading \
  --task 'State one small helper needed by this target, preserving its hypotheses.' \
  --allow-path SpherePacking/Helper.lean \
  --max-changed-lines 100 --time-limit-minutes 30 \
  --output /tmp/sphereceti-author-handoff
```

Both revisions must be full commit SHAs already present locally. A branch, abbreviated SHA,
missing commit or promisor/partial-clone store is rejected. The reference must resolve to a
heading in the configured roadmap document at the specified revision. The configured target
statement file must also exist. The report records their blob IDs and SHA-256 digests, a bounded
roadmap excerpt, and the existing contents' digests for allowed production files. New files are
explicitly identified. Sources must contain ordinary files, without symlinks or submodules.

The destination always comes from the installed project profile, currently
`thefundamentaltheor3m/Sphere-Packing-Lean`. Caller-directory profiles, candidate profiles and
operator preferences cannot redirect it. Local Git objects do **not** authenticate that either
store belongs to its named repository or that its revision is approved/current. Every report
therefore declares `authority: local_unverified`, unverified identity/approval/prerequisites,
`executable: false`, `publication_allowed: false` and `merge_eligible: false`.

Choose one task and one to eight explicit `.lean` or `.md` file paths. Directories, globs,
traversal, hidden/reserved paths, `AGENTS.md`, executable files and Lake configuration are
excluded. The proposed budget is 1–500 changed lines and 1–120 minutes (defaults 200 and 30).
These bounds describe the intended work; no author process runs and no runtime limit is
enforced by the exporter. A digest binds the complete proposal and its source evidence.

JSON is always printed to stdout. `--output` additionally creates `plan.json` and `brief.md`
in a new directory outside both source repositories. Existing directories/files, parent traversal
and symlinked parents are rejected. Without `--output`, the command writes no artifacts. No authoring policy
switch is enabled by generating a plan.

Use the brief with the contributor's chosen author tool. Before execution, independently
verify source identities, approved specification and prerequisite completion, and prepare an
isolated production checkout with appropriately isolated credentials. Preserve the stated
targets and exact source attribution. Validate any resulting patch with production's applicable
build and proof/admission audits. Source export does not accept a patch, establish task ownership,
certify completion, or authorize a commit/PR, review publication or merge. Those require separate
adapters and the existing authenticated review/CI/merge boundaries.

The production-authoring requirements remain in the
[architecture plan](../../INFRASTRUCTURE-PLAN.md#worker-and-shared-reviewer). Automated mathematical
authoring is still unimplemented; diagnostics report local handoff preparation separately.

Validation uses disposable Git repositories and no external service:

```bash
python3 -B -m unittest discover -s tests -p 'test_authoring.py' -v
```
