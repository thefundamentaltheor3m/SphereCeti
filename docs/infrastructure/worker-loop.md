# Work overview and bounded review loops

Independently authored under SphereCeti's Apache-2.0 license. Behavioral credit:
[TauCetiWorker contributors' README at 27c234a](https://github.com/kim-em/TauCetiWorker/blob/27c234a5722cfe557279aa47fbfd8e51450481a6/README.md),
which describes a default work overview and repeated rounds. No upstream Worker implementation,
prompts or tests are copied. The shared review engine remains pinned to
[TauCetiReview afb424e](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b).

Run `sphereceti` with no arguments for a read-only work plan from a fresh GitHub survey.
It invokes no provider and writes no GitHub state. Missing authentication or incomplete evidence
is an error. `sphereceti status --offline --json` remains the network-free diagnostics command.
There is one roadmap and no area-specialization control.

```sh
sphereceti
sphereceti worker run --loop --max-rounds 3 --pr 8,9 --json
sphereceti worker run --loop --max-rounds 3 --interval-seconds 60 \
  --pr 8,9 --execute --provider claude --budget-usd 5 --max-call-cost 1 --json
```

Without `--execute`, a loop previews once and stops. Execution requires the same approved
policy, installed tools, API identity, provider settings and lease guards as a single round.
All shipped switches remain off. Publication still requires its explicit flags.

`--max-rounds` is mandatory with `--loop`, from 1 to 20. The interval is 10–3600 seconds,
default 60. Every round gets a fresh, fully validated survey and reapplies strict targeting.
Within one invocation, a PR head/base already assessed is removed only from review candidates;
maintenance retains priority. This can defer a description-only change or new contest until
the next invocation. A changed head/base can be reconsidered with fresh evidence. No persistent
completion claim or separate budget ledger is created.

The loop stops on unavailable work, disabled policy, partial/error outcomes, unconfirmed state
publication or the round limit. API errors and cancellation propagate without automatic retry.
SIGINT/SIGTERM also stop the interval wait; an active round retains its existing owned-process
cleanup and accounting. Each completed round retains its normal local receipt/archive facts.
The loop's final JSON summarizes outcomes; it does not run a daemon or install a service.

Bounds are on rounds, not a hard total wall-clock deadline. Each round keeps the existing
provider timeout and shared daily budget, including provider charges that may arrive after
cancellation. No provider fallback, quota probing, repair execution or mathematical authoring
is introduced. Production authoring/repair has its own milestone in [tracking issue #23](https://github.com/thefundamentaltheor3m/SphereCeti/issues/23).

Tests use fake providers/APIs and injected interval waits. They cover disabled policy before
survey, cancellation between rounds, strict stop bounds, repeat suppression, maintenance
priority, shared accounting and installed-package command behavior. This PR follows #22;
archive/evaluation and operations need no additional dependency for the loop itself.
