# SPDX-License-Identifier: Apache-2.0
"""A deliberately pessimistic dollar bound for one live review round.

The shared engine's live estimate prices each rubric's reported tokens at the model's flat,
newest base rates, and it charges that estimate to the local daily ledger only after the
rubric's attempts have finished. The analytics price the same tokens at the long-context tier
when a request crosses its threshold. Neither is a ceiling: nothing in SphereCeti or the
imported engine limits how many model requests one attempt makes or how large each one is.

This module answers a narrower question: if a round stayed within stated request limits that
the code does not enforce, what is the most it could cost? The answer is what those assumptions
would imply, not a budget to set, and it is only as good as the assumptions. It prices
every request as if it were as large as allowed, entirely billed at the dearest input-side rate
in the model's price table (cache writes cost more than fresh input there), plus the largest
output at the dearest output rate, and multiplies by every request, attempt and rubric the
engine can dispatch. Pure functions only: no provider, network or ledger access.
"""
from __future__ import annotations

from dataclasses import dataclass
import json
import math

# Every per-token input-side rate a window or its long-context tier can carry. Reported cache
# reads are billed at a `cache_read` rate; any other input token may be fresh or a cache write.
INPUT_SIDE = ("input", "cache_write", "cache_write_5m", "cache_write_1h")
RUBRIC_COUNT = 10  # sphereceti.local_review.RUBRICS; `worker run` always requests all ten.
# review.run_rubric: one attempt plus one retry; an unpinned Codex model may instead be
# reconfirmed and then retried on the fallback model, which is three attempts.
PINNED_ATTEMPTS = 2
UNPINNED_CODEX_ATTEMPTS = 3


@dataclass(frozen=True)
class RequestLimits:
    """Per-request token ceilings and the number of model requests in one attempt.

    None of these is enforced by SphereCeti or engine code. They are assumptions, and every
    bound derived from them holds only if the provider and Codex actually stay within them."""
    max_input_tokens: int
    max_output_tokens: int
    max_requests_per_attempt: int

    def __post_init__(self):
        for name in ("max_input_tokens", "max_output_tokens", "max_requests_per_attempt"):
            value = getattr(self, name)
            if type(value) is not int or value <= 0:
                raise ValueError(f"{name} must be a positive integer")


# Unenforced illustrative assumptions for gpt-6.1-sol. Input: the 872,000-token
# `max_context_window` in codex-cli 0.171.0's bundled catalog (`codex debug models --bundled`),
# the largest window Codex will configure for the model; its default `context_window` is 500,000
# and compaction is only a soft limit. Output: an assumed 128,000 tokens, not stated by that
# catalog. Requests: an assumed 50 model requests per attempt, counting tool-loop turns, Codex's
# own transport retries and any sub-agent requests. No code holds an attempt to any of these.
CANARY_LIMITS = RequestLimits(max_input_tokens=872_000, max_output_tokens=128_000,
                              max_requests_per_attempt=50)


def _tiers(windows):
    for window in windows:
        yield window
        if isinstance(window.get("long_context"), dict):
            yield window["long_context"]


def _max_rate(windows, keys):
    rates = [tier[key] for tier in _tiers(windows) for key in keys if key in tier]
    if not rates:
        raise ValueError(f"price table carries none of {keys}")
    return max(rates)


def _flat(windows):
    """The engine's live estimate rates: the newest window's base tier (pricing._current_window)."""
    window = max(windows, key=lambda w: w["effective"])
    return window["input"], window.get("cache_read", window["input"]), window["output"]


def _cents_up(amount):
    return math.ceil(round(amount * 100, 6)) / 100


@dataclass(frozen=True)
class CostBound:
    """Conservative dollar bounds for one engine invocation (one worker round)."""
    models: tuple
    rubrics: int
    attempts_per_rubric: int
    limits: RequestLimits
    input_rate: float      # USD per million tokens, applied to every input token
    output_rate: float     # USD per million tokens, applied to every output token
    ledger_ratio: float    # most the true price of reported usage can exceed its ledger charge
    per_request: float
    per_attempt: float
    per_rubric: float
    per_round: float
    ledger_per_rubric: float  # most one rubric can add to the local ledger under these limits

    @property
    def reservation(self) -> float:
        """The per-rubric reservation the assumed limits imply, rounded up to cents.

        The engine compares ledger spend plus its per-call reservation with the budget before
        each rubric and never again until that rubric's attempts have all finished, so only a
        reservation this large would cover a whole rubric under the assumptions."""
        return _cents_up(self.per_rubric)

    def spend_ceiling(self, budget: float, max_call_cost: float, spent_today: float = 0.0) -> float:
        """The most one round can cost when the budget acts as a stop threshold.

        A rubric starts only while ledger spend plus `max_call_cost` is at most `budget`, so the
        rubrics finished before the last one started have ledger charges summing to at most
        `budget - max_call_cost - spent_today`; their true price is at most `ledger_ratio` times
        that. The last rubric started may then cost up to `per_rubric`, and no round runs more
        than `rubrics` rubrics. Assumes reported usage covers every request of an attempt."""
        room = budget - spent_today - max_call_cost
        if room < 0:
            return 0.0
        return min(self.per_round, self.ledger_ratio * room + self.per_rubric)

    def overshoot(self, budget: float, max_call_cost: float, spent_today: float = 0.0) -> float:
        """How far the round's true price can land above the budget's remaining headroom."""
        headroom = max(0.0, budget - spent_today)
        return max(0.0, self.spend_ceiling(budget, max_call_cost, spent_today) - headroom)

    def ledger_overshoot(self, max_call_cost: float) -> float:
        """How far the local ledger can end above the budget: one rubric beyond its reservation."""
        return max(0.0, self.ledger_per_rubric - max_call_cost)


def attempts_per_rubric(provider: str, codex_model_pinned: bool) -> int:
    """Model attempts review.run_rubric can dispatch for one rubric."""
    return UNPINNED_CODEX_ATTEMPTS if provider == "codex" and not codex_model_pinned else PINNED_ATTEMPTS


def round_cost_bound(price_windows: dict, models, limits: RequestLimits = CANARY_LIMITS, *,
                     attempts: int = PINNED_ATTEMPTS, rubrics: int = RUBRIC_COUNT) -> CostBound:
    """Bound a round's cost from the dated price table (`prices.json`'s `models` mapping).

    Every request is priced at its maximum input, all billed at the dearest input-side rate any
    window or long-context tier of the given models carries, plus its maximum output at the
    dearest output rate; that is the long-context tier, above the threshold or not. A round is
    `rubrics` rubrics of `attempts` attempts of `max_requests_per_attempt` requests. List every
    model an attempt may use (an unpinned Codex model also needs its fallback)."""
    models = tuple(models)
    if not models or type(attempts) is not int or attempts <= 0 or type(rubrics) is not int or rubrics <= 0:
        raise ValueError("bound requires at least one model and positive attempts and rubrics")
    missing = [m for m in models if not price_windows.get(m)]
    if missing:
        raise ValueError(f"unpriced model(s) {missing}")
    windows = [w for m in models for w in price_windows[m]]
    input_rate = _max_rate(windows, INPUT_SIDE)
    output_rate = _max_rate(windows, ("output",))
    # A reported cache read is billed at its tier's cache-read rate (input, where none is listed).
    cache_rate = max(tier.get("cache_read", tier["input"]) for tier in _tiers(windows))
    ratio = max(max(input_rate / i, cache_rate / c, output_rate / o)
                for i, c, o in (_flat(price_windows[m]) for m in models))
    per_request = (limits.max_input_tokens * input_rate + limits.max_output_tokens * output_rate) / 1e6
    ledger_request = max(limits.max_input_tokens * max(i, c) + limits.max_output_tokens * o
                         for i, c, o in (_flat(price_windows[m]) for m in models)) / 1e6
    per_attempt = limits.max_requests_per_attempt * per_request
    per_rubric = attempts * per_attempt
    return CostBound(models=models, rubrics=rubrics, attempts_per_rubric=attempts, limits=limits,
                     input_rate=input_rate, output_rate=output_rate, ledger_ratio=ratio,
                     per_request=per_request, per_attempt=per_attempt, per_rubric=per_rubric,
                     per_round=rubrics * per_rubric,
                     ledger_per_rubric=attempts * limits.max_requests_per_attempt * ledger_request)


def installed_price_windows() -> dict:
    """The installed engine's dated price table, the same bytes the engine bills from."""
    from .review_resources import review_files
    return json.loads(review_files()["runner/prices.json"])["models"]
