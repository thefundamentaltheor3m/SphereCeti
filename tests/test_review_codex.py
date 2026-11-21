"""Direct local reviews through the imported Codex adapter, with a fake Codex executable."""
import datetime
import json
from pathlib import Path
import sys
import tempfile
import tomllib
import unittest

from review_fixture import ReviewFixture

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools/project"))
from sphereceti.archive_store import snapshot, validate  # noqa: E402

# The fake Codex turn: 100k total input, of which 80k cache reads, and 1k output tokens.
NORMALIZED = {"input_tokens": 100000, "fresh_input_tokens": 20000, "cached_input_tokens": 80000,
              "cache_creation_input_tokens": 0, "output_tokens": 1000, "reasoning_output_tokens": 400}


def settings(argv):
    return [argv[i + 1] for i, arg in enumerate(argv[:-1]) if arg == "-c"]


def model(argv):
    return argv[argv.index("-m") + 1] if "-m" in argv else None


class CodexReviewTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="sphereceti-codex-test-")
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.fixture = ReviewFixture(self.root)

    def review(self, *extra, output="result"):
        process = self.fixture.run(output=output, extra=("--provider", "codex", "--rubrics", "correctness", *extra))
        self.assertEqual(process.returncode, 0, process.stderr + process.stdout)
        return json.loads(process.stdout)

    def test_subscription_login_is_seeded_alone_and_launcher_runtime_is_restored(self):
        self.fixture.codex_subscription()
        result = self.review("--auth", "subscription")
        self.assertEqual(result["verdicts"]["correctness"], "approve")
        self.assertEqual(result["evaluation_request"]["auth"], "subscription")
        [call] = self.fixture.codex_calls()
        # ChatGPT-login subscription: only auth.json is copied into a private CODEX_HOME; no API
        # key, no `codex login`, no personal instructions, and no other credential.
        self.assertIsNone(call["openai_key"])
        self.assertIn("FAKE-CHATGPT-LOGIN", call["auth"])
        rev = self.fixture.home / ".tauceti-rev"
        self.assertTrue(Path(call["codex_home"]).is_relative_to(rev))
        self.assertNotEqual(Path(call["codex_home"]), self.fixture.home / ".codex")
        self.assertEqual(call["leaked"], [])
        self.assertTrue(call["prompt_ok"])
        # TauCetiReview #196: inheritance stays disabled; only PATH and a private TMPDIR return.
        tmpdir = Path(call["tmpdir"])
        self.assertEqual(tmpdir.parent, Path(call["home"]))
        self.assertTrue(tmpdir.is_relative_to(rev))
        options = settings(call["argv"])
        self.assertIn("shell_environment_policy.inherit=none", options)
        policy = tomllib.loads("\n".join(s for s in options if ".set." in s))["shell_environment_policy"]
        self.assertEqual(set(policy["set"]), {"PATH", "TMPDIR"})
        self.assertEqual(policy["set"]["TMPDIR"], call["tmpdir"])
        self.assertEqual(policy["set"]["PATH"], self.fixture.env["PATH"])
        self.assertIn("read-only", call["argv"])
        self.assertEqual(list(rev.iterdir()), [], "per-attempt homes and temporary storage are removed")

    def test_missing_subscription_login_never_falls_back_to_personal_codex_home(self):
        (self.fixture.home / ".codex").mkdir()
        (self.fixture.home / ".codex/AGENTS.md").write_text("PERSONAL CODEX INSTRUCTIONS\n")
        process = self.fixture.run(extra=("--provider", "codex", "--rubrics", "correctness",
                                          "--auth", "subscription"))
        self.assertEqual(process.returncode, 1, process.stderr)
        self.assertEqual(json.loads(process.stdout)["completion"], "error")
        self.assertEqual(self.fixture.codex_calls(), [])


    def archived_runs(self):
        journal = self.root / "state/thefundamentaltheor3m__SphereCeti/archive/journal"
        return [(record, run) for record in validate(snapshot(journal), "thefundamentaltheor3m/SphereCeti")
                for run in record["runs"]]

    def spent_today(self):
        return self.fixture.ledger()["days"][str(datetime.date.today())]

    def test_explicit_sol61_subscription_review_is_admitted_and_estimated(self):
        self.fixture.codex_subscription()
        result = self.review("--auth", "subscription", "--codex-model", "gpt-6.1-sol")
        self.assertEqual(result["verdicts"]["correctness"], "approve")
        [call] = self.fixture.codex_calls()
        self.assertEqual(model(call["argv"]), "gpt-6.1-sol")
        self.assertIsNone(call["openai_key"])
        # Subscription runs carry no provider bill, so the shared daily budget is charged the
        # dated list-price estimate: (20k fresh x 2.00 + 80k cached x 0.10 + 1k out x 10.00) / 1M.
        self.assertAlmostEqual(self.spent_today(), 0.058)
        [(record, run)] = self.archived_runs()
        self.assertEqual(record["request"]["auth"], "subscription")
        self.assertEqual((run["provider"], run["model"]), ("codex", "gpt-6.1-sol"))
        self.assertTrue(run["cost_estimated"])
        self.assertAlmostEqual(run["cost_usd"], 0.058)
        self.assertEqual(run["usage"]["input_tokens"], 100000)  # raw Codex usage is retained
        # TauCetiReview #148: round totals use one comparable input convention across providers.
        [state] = self.fixture.ledger()["prs"].values()
        self.assertEqual(state["rounds"][-1]["tokens"], NORMALIZED)

    def test_default_codex_model_is_unchanged_and_bills_its_corrected_window(self):
        self.fixture.codex_subscription()
        self.review("--auth", "subscription")
        [call] = self.fixture.codex_calls()
        self.assertEqual(model(call["argv"]), "gpt-5.6-sol")
        # TauCetiReview #175's 2026-08-21 window: 4.00 input, 0.40 cached, 20.00 output.
        self.assertAlmostEqual(self.spent_today(), 0.132)

    def test_direct_review_attempt_deadline_stops_codex_and_its_child(self):
        self.fixture.codex_subscription()
        (self.fixture.bin / "codex-hang").write_text("all")
        result = self.review("--auth", "subscription", "--codex-model", "gpt-6.1-sol",
                             "--attempt-timeout", "2")
        [pids] = self.fixture.codex_pids()
        for pid in (pids["leader"], pids["child"]):
            path = Path(f"/proc/{pid}/stat")
            self.assertTrue(not path.exists() or path.read_text().rsplit(")", 1)[1].split()[0] == "Z", pid)
        self.assertEqual(len(self.fixture.codex_calls()), 1)
        self.assertEqual((result["stop_reason"], result["usage_unknown_rubrics"]),
                         ("usage_unknown", ["correctness"]))
        [(record, run)] = self.archived_runs()
        self.assertEqual(run["usage_status"], "unknown")
        self.assertNotIn("cost_usd", run)

    def test_attempt_deadline_must_be_whole_bounded_seconds(self):
        self.fixture.codex_subscription()
        for value in ("0", "1801"):
            process = self.fixture.run(output="result-" + value,
                                       extra=("--provider", "codex", "--rubrics", "correctness",
                                              "--auth", "subscription", "--attempt-timeout", value))
            self.assertNotEqual(process.returncode, 0)
            self.assertIn("--attempt-timeout", process.stdout + process.stderr)
        self.assertEqual(self.fixture.codex_calls(), [])

    def test_unpriced_model_is_still_rejected_before_inference(self):
        self.fixture.codex_subscription()
        process = self.fixture.run(extra=("--provider", "codex", "--rubrics", "correctness",
                                          "--auth", "subscription", "--codex-model", "gpt-99-sol"))
        self.assertEqual(process.returncode, 1, process.stderr)
        self.assertEqual(json.loads(process.stdout)["completion"], "error")
        self.assertEqual(self.fixture.codex_calls(), [])


if __name__ == "__main__":
    unittest.main()
