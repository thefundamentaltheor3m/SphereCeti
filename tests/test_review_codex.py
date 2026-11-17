"""Direct local reviews through the imported Codex adapter, with a fake Codex executable."""
import json
from pathlib import Path
import tempfile
import tomllib
import unittest

from review_fixture import ReviewFixture


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


if __name__ == "__main__":
    unittest.main()
