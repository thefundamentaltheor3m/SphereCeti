# SphereCeti

SphereCeti is preparing a roadmap and target-signature package for sphere packing in dimensions
8 and 24. The mathematical roadmap is being reviewed in
[PR #1](https://github.com/thefundamentaltheor3m/SphereCeti/pull/1); substantive proofs remain in
[Sphere-Packing-Lean](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean).

**Our infrastructure adapts the work of the TauCeti contributors:**
[TauCeti](https://github.com/TauCetiProject/TauCeti),
[TauCetiRoadmap](https://github.com/TauCetiProject/TauCetiRoadmap),
[TauCetiReview](https://github.com/TauCetiProject/TauCetiReview),
[TauCetiWorker](https://github.com/kim-em/TauCetiWorker),
[TauCetiProgress](https://github.com/TauCetiProject/TauCetiProgress), and
[TauCetiData](https://github.com/TauCetiProject/TauCetiData).
The [infrastructure plan](INFRASTRUCTURE-PLAN.md) records their roles, exact candidate source
snapshots, and the focused PR sequence. Imports retain source attribution and applicable licenses.

## Build boundaries

```bash
lake env python3 -I scripts/check_audits.py
lake build
```

The default build checks both `SphereCeti` (the admission-free scaffold/adapters) and
`SphereCetiRoadmap` (currently an empty target aggregator). This separation does not change the
production proof home. See [module boundaries](docs/infrastructure/module-boundaries.md) for
the source inventory, tests, limitations, and the integration steps for PR #1.

The [trusted candidate build](docs/infrastructure/trusted-build.md) adapts TauCeti's pinned
sandbox and configuration attestation. It uses approved tools, builds an immutable PR head,
and reports build and scope separately; all current changes require human review.
[Compiled audits](docs/infrastructure/compiled-audits.md) check every module, transitive axiom
dependencies, lint, and the roadmap admission ledger.

## Project diagnostics

```bash
uv run --locked sphereceti doctor --offline
uv run --locked sphereceti status --json
```

The installed CLI packages project identity, policy, and the upstream source ledger. These
commands report the scaffold's state; worker and automated review/merge capabilities remain disabled.
See [CLI configuration and installation](docs/infrastructure/cli.md).

The [TauCetiReview import](tools/review/README.md) preserves its engine, ten ordered rubrics,
and upstream tests. `sphereceti review N --dry-run` verifies the exact proposed PR, selected
context, and dependency sources without invoking a provider. An explicitly configured provider
can produce a [local advisory review](docs/infrastructure/local-review.md).
[Review records](docs/infrastructure/review-records.md) bind that evidence to API-verified
publication identities. `review N --read-records` inspects them without inference; explicit
`--post` requires approved posting policy, which remains disabled. The legacy launchers remain disabled.

The [durable review archive](docs/infrastructure/review-archive.md) keeps completed review
metadata and numeric run facts in a local journal/outbox. `sphereceti archive preview` and
`archive rebuild --output /tmp/reviews.sqlite` are provider-free; remote sync remains disabled.

The [evaluation tools](docs/infrastructure/evaluation.md) summarize recorded costs, apply
explicit dated price snapshots, compare compatible fresh shadow arms, and retain local human
labels. `sphereceti evaluation costs --json` is offline and never invokes a provider.

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
