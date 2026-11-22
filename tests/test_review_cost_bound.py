"""The conservative review cost bound under unenforced limits, against the engine's price paths."""
import json
from pathlib import Path
import sys
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools/project"))
sys.path.append(str(ROOT / "tools/review"))  # the engine as a package, never ahead of tests
from sphereceti import local_review  # noqa: E402
from sphereceti.review_cost_bound import (CANARY_LIMITS, RUBRIC_COUNT, RequestLimits,  # noqa: E402
                                          attempts_per_rubric, installed_price_windows,
                                          round_cost_bound)
from runner import reviewers  # noqa: E402
from runner.costs import cost_from_window, price_window  # noqa: E402

PRICES = installed_price_windows()
SOL61 = "gpt-6.1-sol"


def live_estimate(model, inp, cached, out):
    """The engine's live estimate: run_codex's own arithmetic on one fake Codex turn."""
    usage = {"input_tokens": inp, "cached_input_tokens": cached, "output_tokens": out}
    stdout = "\n".join(json.dumps(e) for e in (
        {"type": "item.completed", "item": {"type": "agent_message", "text": "done"}},
        {"type": "turn.completed", "usage": usage}))
    with patch.object(reviewers, "sh", return_value=SimpleNamespace(returncode=0, stdout=stdout, stderr="")):
        return reviewers.run_codex("prompt", ".", model, {})["cost_usd"]


def analytics(model, inp, cached, out, day="2026-11-21"):
    return cost_from_window(price_window(PRICES, model, day), inp, cached, out)


def one_request(model, inp, out):
    """The rule for exactly one request of this size: one request, attempt and rubric."""
    return round_cost_bound(PRICES, (model,), RequestLimits(inp, out, 1), attempts=1, rubrics=1)


class CostBoundTests(unittest.TestCase):
    def test_price_table_is_the_installed_engine_table(self):
        self.assertEqual(PRICES, json.loads((ROOT / "tools/review/runner/prices.json").read_text())["models"])
        self.assertEqual(RUBRIC_COUNT, len(local_review.RUBRICS))

    def test_synthetic_long_context_request_orders_live_analytics_and_bound(self):
        # PR #35's discrepancy: 300k fresh input and 1k output.
        self.assertAlmostEqual(live_estimate(SOL61, 300_000, 0, 1_000), 0.61)
        self.assertAlmostEqual(analytics(SOL61, 300_000, 0, 1_000), 1.215)
        # Every input token at the long-context cache-write rate, the dearest input-side rate.
        self.assertAlmostEqual(one_request(SOL61, 300_000, 1_000).per_round, 1.515)

    def test_rule_uses_the_long_context_tier_at_below_and_above_the_threshold(self):
        threshold = PRICES[SOL61][-1]["long_context"]["threshold"]
        self.assertEqual(threshold, 272_000)
        for inp in (200_000, threshold - 1, threshold, threshold + 1, 300_000, 872_000):
            bound = one_request(SOL61, inp, 1_000)
            self.assertAlmostEqual(bound.per_request, (inp * 5.0 + 1_000 * 15.0) / 1e6)
            for cached in (0, inp // 2, inp):
                charged = analytics(SOL61, inp, cached, 1_000)
                live = live_estimate(SOL61, inp, cached, 1_000)  # rounded to 1e-6 dollars
                self.assertGreaterEqual(bound.per_request, charged)
                self.assertGreaterEqual(charged + 1e-6, live)
                self.assertLessEqual(charged, bound.ledger_ratio * (live + 1e-6))
        # At the threshold analytics keeps the base tier (strict `>`); the bound does not.
        self.assertAlmostEqual(analytics(SOL61, threshold, 0, 0), threshold * 2.0 / 1e6)
        self.assertAlmostEqual(analytics(SOL61, threshold + 1, 0, 0), (threshold + 1) * 4.0 / 1e6)

    def test_rule_is_never_below_analytics_for_any_priced_model_or_date(self):
        for model, windows in PRICES.items():
            for window in windows:
                tier = window.get("long_context", {}).get("threshold", 200_000)
                for inp in (1, tier, tier + 1, 3 * tier):
                    for out in (1, 128_000):
                        bound = one_request(model, inp, out)
                        for cached in (0, inp):
                            self.assertGreaterEqual(bound.per_request + 1e-12,
                                                    cost_from_window(window, inp, cached, out), model)

    def test_assumed_limits_imply_these_sol61_bounds(self):
        bound = round_cost_bound(PRICES, (SOL61,))
        self.assertEqual(CANARY_LIMITS, RequestLimits(872_000, 128_000, 50))
        self.assertEqual((bound.input_rate, bound.output_rate, bound.ledger_ratio), (5.0, 15.0, 2.5))
        self.assertEqual((bound.rubrics, bound.attempts_per_rubric), (10, 2))
        self.assertAlmostEqual(bound.per_request, 6.28)
        self.assertAlmostEqual(bound.per_attempt, 314.0)
        self.assertAlmostEqual(bound.per_rubric, 628.0)
        self.assertAlmostEqual(bound.per_round, 6280.0)
        self.assertAlmostEqual(bound.ledger_per_rubric, 302.4)
        self.assertEqual(bound.reservation, 628.0)
        # A reservation covering a whole rubric, with room for ten, lands nothing above the threshold.
        self.assertEqual(bound.overshoot(10 * bound.reservation, bound.reservation), 0.0)
        self.assertEqual(bound.ledger_overshoot(bound.reservation), 0.0)
        # A small stop threshold still admits one worst-case rubric beyond it.
        self.assertAlmostEqual(bound.spend_ceiling(20, 2), 2.5 * 18 + 628)
        self.assertAlmostEqual(bound.overshoot(20, 2), 2.5 * 18 + 628 - 20)
        self.assertAlmostEqual(bound.ledger_overshoot(2), 300.4)

    def test_attempts_follow_the_engine_retry_and_fallback_paths(self):
        self.assertEqual(attempts_per_rubric("codex", True), 2)
        self.assertEqual(attempts_per_rubric("codex", False), 3)
        self.assertEqual(attempts_per_rubric("claude", False), 2)
        unpinned = round_cost_bound(PRICES, ("gpt-5.6-sol", "gpt-5.6-terra"), attempts=3)
        for model in unpinned.models:
            single = round_cost_bound(PRICES, (model,), attempts=3)
            self.assertGreaterEqual(unpinned.per_round, single.per_round)
            self.assertGreaterEqual(unpinned.ledger_ratio, single.ledger_ratio)

    def test_stop_threshold_ceiling(self):
        bound = round_cost_bound(PRICES, (SOL61,), RequestLimits(300_000, 1_000, 1))
        self.assertAlmostEqual(bound.per_rubric, 2 * 1.515)
        self.assertEqual(bound.spend_ceiling(1, 0.5, spent_today=0.6), 0.0)  # nothing may start
        self.assertEqual(bound.overshoot(1, 0.5, spent_today=0.6), 0.0)
        self.assertAlmostEqual(bound.spend_ceiling(1, 0.1), 2.5 * 0.9 + 3.03)
        self.assertAlmostEqual(bound.spend_ceiling(10**6, 0.1), bound.per_round)  # ten rubrics at most
        self.assertAlmostEqual(bound.ledger_overshoot(0.1), 1.12)
        self.assertEqual(bound.ledger_overshoot(1.22), 0.0)

    def test_invalid_inputs_are_rejected(self):
        with self.assertRaises(ValueError):
            round_cost_bound(PRICES, ("gpt-99-sol",))
        with self.assertRaises(ValueError):
            round_cost_bound(PRICES, ())
        with self.assertRaises(ValueError):
            round_cost_bound(PRICES, (SOL61,), attempts=0)
        for limits in ((0, 1, 1), (1, -1, 1), (1, 1, 1.5), (True, 1, 1)):
            with self.assertRaises(ValueError):
                RequestLimits(*limits)


if __name__ == "__main__":
    unittest.main()
