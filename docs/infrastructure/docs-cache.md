# Documentation and cache operations

Documentation and cache operations use the compiled audits from the foundation. This layer
precedes the reporting adapter in the serialized stack. Pages and storage remain unconfigured
until an operator completes the setup below.

**Credit: [TauCeti contributors](https://github.com/TauCetiProject/TauCeti), Apache-2.0, at
[b743b60](https://github.com/TauCetiProject/TauCeti/tree/b743b607ce3e9742b18026ad79082e5d15badff5).**
The design adapts these exact sources:

- [Pages workflow](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/.github/workflows/pages.yml): stamp the generated tree with its actual documented revision; deploy on a separate runner.
- [CI staging](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/.github/workflows/ci.yml) and [cache publisher](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/.github/workflows/publish-lake-cache.yml): stage native Lake archives without secrets; upload data from a fresh runner.
- [Nightly verification](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/.github/workflows/nightly-verify.yml) and [comparator](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/compare-build-outputs.py): keep source correctness separate from advisory cache comparison.
- [Public map probe](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/scripts/lake_cache_probe.py) and [storage documentation](https://github.com/TauCetiProject/TauCeti/blob/b743b607ce3e9742b18026ad79082e5d15badff5/docs/cache-infrastructure.md): exact revision-map URLs and independent read/upload endpoints.

[The source ledger](../../tools/upstream-lock.toml) records these paths and the adaptations.
SphereCeti's Lean/TauCeti dependency pins remain unchanged. The upstream website, statistics,
roadmap text, notification workflows, and deployment credentials are not imported.

## Build and review

From a clean, committed checkout with pinned dependencies installed:

```sh
python3 -B -m unittest discover -s tests -p 'test_publication.py' -v
lake env python3 -I scripts/build_publication.py --output /tmp/sphereceti-publication
python3 -I scripts/publication.py verify /tmp/sphereceti-publication "$(git rev-parse HEAD)"
```

Use a fresh output directory. The driver verifies dependency source revisions before and after
building; runs #8's complete compiled audits; then renders names, axiom dependencies, and source
links from the compiled declaration inventory. It does not infer declarations from Lean text.
The initial reference is deliberately a declaration/axiom catalog, not doc-gen4's full type and
comment rendering. It introduces no documentation dependency into the pinned mathematical graph.

The generated tree includes:

| File | Meaning |
| --- | --- |
| `docs/SOURCE_SHA` | Exactly the documented Git commit plus newline; never inferred from deployment time |
| `docs/declarations.json` | Repository, revision, pinned dependencies, audit digest, declaration classification and stable page links |
| `docs/library/index.html` | Audited library declarations, explicitly not a production proof-completion claim |
| `docs/targets/index.html` | Roadmap target signatures, including admitted targets; never advertised as proved milestones |
| `docs/audit.json` | Compiled inventory and the audit verdict used to generate this reference |
| `cache/outputs.jsonl` | Pinned Lake-format mappings for explicit library `:olean` targets |
| `cache/*.ltar` | Exactly the native archives selected by those mappings |
| `publication.json` | Cross-job identity and SHA-256 manifest of the docs and cache files |

Roadmap declarations remain targets even if they have no `sorryAx`. Library declarations that
rely on an approved admission exception remain labeled admission-dependent. The JSON states
`production_evidence: false`: this repository is not Sphere-Packing-Lean. The Progress adapter
must consume this schema explicitly, distinguish targets from achievements, and require approved
production documentation before reporting production milestones. A successful build artifact is
not evidence that a site was deployed. The authoritative deployed cursor is the site's
`SOURCE_SHA`, read together with its matching declaration index; no best-effort Git branch cursor
is introduced.

The cache includes only explicitly selected, audited library targets. Roadmap, tool, fixture,
dependency and native executable targets are excluded. The mappings use the existing package's
platform-dependent scope: `thefundamentaltheor3m/SphereCeti`,
`x86_64-unknown-linux-gnu`, and `leanprover/lean4:v4.34.0-rc1`. Configuration that would change
that scope is refused until the publisher is updated. The existing anonymous pinned TauCeti cache
consumer and source fallback are unchanged; this PR does not silently enable consumption of the
new SphereCeti cache.

## Credential boundary and setup

`Documentation and cache` builds previews on PRs and accepted `main`, and exercises a separate
fresh source build. Both build jobs have read-only repository permissions, no publication secrets,
and checkout credentials disabled. Publications additionally require accepted `main` and explicit
repository variables. No PR build can enter either publisher job.

Pages deployment runs only the pinned `deploy-pages` action on a fresh runner with Pages/OIDC
permissions. The cache job checks out only reviewed publication helpers and toolchain pins from
the exact accepted commit. It validates the bounded data bundle, installs the pinned toolchain
without loading the project, then invokes the direct pinned Lake binary from an empty directory.
Only that upload step receives the cache key. It neither extracts nor imports the archives. The
later credential-free step requires byte-for-byte readback of the exact public revision map.
A public-read outage leaves publication unconfirmed; it does not undo the successful source build.

The build producer and accepted workflow/helpers remain trusted to select the intended outputs.
Manifest hashes bind bytes across the jobs; they do not prove that an arbitrary producer performed
an audit. Protect infrastructure changes and the deployment environments accordingly.

Activation is a separate operator step, not performed by this PR:

1. Configure GitHub Pages to use Actions, restrict the `github-pages` environment to `main`, and
   set `SPHERECETI_PAGES_ENABLED=true` only after reviewing the generated artifact.
2. Create a dedicated SphereCeti cache store and the `sphereceti-cache` environment, restricted
   to `main`. Restrict upload authority to that store. Do not borrow TauCeti upload credentials.
3. Set repository variables `SPHERECETI_CACHE_ARTIFACT_ENDPOINT`,
   `SPHERECETI_CACHE_REVISION_ENDPOINT`, and their `_PUBLIC` equivalents to plain HTTPS endpoints.
   Their paths must implement Lake's S3 artifact/revision contract. The publisher refuses TauCeti's
   domain and requires `SPHERECETI_CACHE_KEY` (Lake's `access-key-id:secret-access-key` format)
   in the deployment environment.
4. Set `SPHERECETI_CACHE_ENABLED=true` only after storage and environment review. Enabling a switch
   with missing or malformed configuration fails publication visibly.
5. After deployment, inspect the public `SOURCE_SHA`, matching declaration JSON, and cache map.
   The map URL includes `/thefundamentaltheor3m/SphereCeti/pt/x86_64-unknown-linux-gnu/tc/`
   followed by the escaped toolchain and exact revision. Do not infer publication from a green build.

## Nightly source verification and optional comparison

`Nightly source verification` runs daily at 03:37 UTC on `main`, and supports manual dispatch on
`main`. `--source` requires empty project build/cache directories and sets
`LAKE_RESTORE_ARTIFACTS=false` and `LAKE_NO_CACHE=true` throughout compilation and audits. It
rebuilds every classified SphereCeti source, including unimported modules, tools and fixtures.
Pinned Lean/Mathlib/TauCeti dependencies remain bootstrap inputs; the claim is independent
SphereCeti source elaboration, not a source rebuild of the entire toolchain/dependency closure.
The same command is exercised on every PR by `source-rebuild-check`.

A separate job optionally downloads the exact SphereCeti revision map and archive bytes for
comparison. It never extracts or executes reference artifacts. `agreement`, `divergent`, and
`inconclusive` are separate advisory outcomes. Missing endpoints, outages, malformed responses,
or incomplete downloads are inconclusive; they cannot become agreement by compiling a fallback.
A byte difference is not automatically a theorem failure or evidence of corruption, because
reproducibility is a separate question. Each run compares one exact revision, not all historical
cache contents. The source job's failure remains a failure regardless of comparison status.

Local checks use small fixtures and the existing dependency cache. Hosted jobs have 40-minute
normal / 120-minute source limits. No local full dependency rebuild is required. Before running
one, budget disk and CPU separately; this work used under 1 GiB of additional local space and
kept at least 10 GiB free.

## Landing and activation

All infrastructure lands before roadmap #1. See the
[tracking issue](https://github.com/thefundamentaltheor3m/SphereCeti/issues/23) for the current
review sequence. Documentation publication and cache uploads require separate activation.
