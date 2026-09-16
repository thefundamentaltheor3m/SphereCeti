"""End-to-end local reviews with disposable exact Git evidence and a fake provider."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from review_fixture import ReviewFixture, commit, git


class LocalReviewTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="sphereceti-adapter-test-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.fixture = ReviewFixture(self.root)

    def run_review(self, **kwargs):
        process = self.fixture.run(**kwargs)
        self.assertEqual(process.returncode, 0, process.stderr + process.stdout)
        return json.loads(process.stdout)

    def test_dry_run_names_exact_evidence_and_never_invokes_provider(self):
        result = self.run_review(extra=("--dry-run", "--keep-workspace"))
        self.assertEqual(result["tooling"], self.fixture.tooling)
        self.assertEqual(result["head"], self.fixture.head)
        self.assertEqual(result["diff_base"], self.fixture.tooling)
        self.assertEqual(result["completion"], "dry_run")
        self.assertFalse(result["merge_eligible"])
        self.assertFalse(result["tooling_approved"])
        self.assertTrue(all(e["authority"] == "prospective" for e in result["evidence"]))
        self.assertEqual(len(result["dependencies"]), 2)
        self.assertFalse(self.fixture.calls())
        self.assertTrue((self.root / "result/workspace/code/README.md").read_text().startswith("PROPOSED SENTINEL"))

    def test_full_review_uses_engine_and_remains_advisory(self):
        result = self.run_review()
        self.assertEqual(result["completion"], "complete", result)
        self.assertEqual(len(result["finished_rubrics"]), 10)
        self.assertEqual(len(self.fixture.calls()), 10)
        self.assertTrue(result["advisory"])
        self.assertFalse(result["merge_eligible"])
        self.assertNotIn("<!--tauceti-", (self.root / "result/advisory.md").read_text())
        self.assertFalse((self.root / "result/engine-request.json").exists())
        self.assertFalse((self.root / "result/workspace").exists())

    def test_missing_context_never_uses_candidate_as_approved_spec(self):
        git(self.fixture.repo, "checkout", "-q", self.fixture.tooling)
        (self.fixture.repo / "CONVENTIONS.md").unlink()
        self.fixture.tooling = commit(self.fixture.repo)
        (self.fixture.repo / "CONVENTIONS.md").write_text("CANDIDATE CONVENTIONS MUST NOT BECOME APPROVED")
        (self.fixture.repo / "README.md").write_text("PROPOSED SENTINEL")
        self.fixture.head = commit(self.fixture.repo)
        result = self.run_review(extra=("--dry-run",))
        self.assertIn("CONVENTIONS.md", result["missing_context"])
        self.assertNotIn("approved/CONVENTIONS.md", {e["path"] for e in result["evidence"]})
        self.assertFalse(result["merge_eligible"])

    def test_dirty_candidate_and_dependency_worktrees_do_not_change_evidence(self):
        (self.fixture.repo / "README.md").write_text("UNCOMMITTED CANDIDATE")
        (self.fixture.deps / "TauCeti/README.md").write_text("UNCOMMITTED DEPENDENCY")
        result = self.run_review()
        self.assertEqual(result["completion"], "complete")
        self.assertEqual(len(self.fixture.calls()), 10)

    def test_missing_exact_dependency_prevents_inference(self):
        missing = self.fixture.deps / "mathlib"
        git(missing, "update-ref", "-d", "refs/heads/master")
        # Point at an unrelated object database, without rewriting the selected dependency pin.
        self.fixture.packages[1]["rev"] = "f" * 40
        manifest = self.fixture.repo / "lake-manifest.json"
        git(self.fixture.repo, "checkout", "-q", self.fixture.tooling)
        data = json.loads(manifest.read_text())
        old = data["packages"][1]["rev"]
        data["packages"][1]["rev"] = "f" * 40
        manifest.write_text(json.dumps(data))
        profile = self.fixture.repo / "sphereceti.toml"
        profile.write_text(profile.read_text().replace(old, "f" * 40))
        self.fixture.tooling = commit(self.fixture.repo)
        (self.fixture.repo / "README.md").write_text("PROPOSED SENTINEL")
        self.fixture.head = commit(self.fixture.repo)
        process = self.fixture.run()
        self.assertNotEqual(process.returncode, 0)
        self.assertFalse(self.fixture.calls())

    def test_candidate_symlink_is_rejected_before_provider(self):
        (self.fixture.repo / "leak").symlink_to("/etc/passwd")
        self.fixture.head = commit(self.fixture.repo)
        self.assertNotEqual(self.fixture.run().returncode, 0)
        self.assertFalse(self.fixture.calls())

    def repin_dependency(self):
        revision = commit(self.fixture.deps / "TauCeti")
        git(self.fixture.repo, "checkout", "-q", self.fixture.tooling)
        for name in ("sphereceti.toml", "lake-manifest.json"):
            path = self.fixture.repo / name
            path.write_text(path.read_text().replace(self.fixture.packages[0]["rev"], revision))
        self.fixture.tooling = commit(self.fixture.repo)
        (self.fixture.repo / "README.md").write_text("PROPOSED SENTINEL")
        self.fixture.head = commit(self.fixture.repo)

    def test_exact_internal_dependency_links_are_preserved(self):
        directory = self.fixture.deps / "TauCeti/docs"
        directory.mkdir()
        (directory / "rules.md").symlink_to("../README.md")
        self.repin_dependency()
        report = self.run_review(extra=("--dry-run", "--keep-workspace"))
        link = self.root / "result/workspace/dependencies/TauCeti/docs/rules.md"
        self.assertTrue(link.is_symlink())
        self.assertTrue(link.read_text().startswith("EXACT DEPENDENCY FIXTURE"))
        self.assertEqual(report["dependencies"][0]["internal_links"], {"docs/rules.md": "../README.md"})

    def test_external_dependency_links_are_rejected(self):
        (self.fixture.deps / "TauCeti/link").symlink_to("/etc/passwd")
        self.repin_dependency()
        process = self.fixture.run(extra=("--dry-run",))
        self.assertEqual(process.returncode, 2)
        self.assertIn("symlink escapes", process.stderr)
        self.assertFalse(self.fixture.calls())

    def test_cyclic_dependency_links_are_rejected(self):
        (self.fixture.deps / "TauCeti/a").symlink_to("b")
        (self.fixture.deps / "TauCeti/b").symlink_to("a")
        self.repin_dependency()
        process = self.fixture.run(extra=("--dry-run",))
        self.assertEqual(process.returncode, 2)
        self.assertIn("ordinary file", process.stderr)
        self.assertFalse(self.fixture.calls())

    def test_partial_and_budget_limited_runs(self):
        partial = self.run_review(output="subset", extra=("--rubrics", "naming,correctness"))
        self.assertEqual(partial["completion"], "partial")
        self.assertEqual(partial["requested_rubrics"], ["correctness", "naming"])
        self.assertFalse(partial["merge_eligible"])
        budget = self.run_review(output="budget", extra=("--mode", "manual", "--budget-usd", "0.03", "--max-call-cost", "0.01"))
        self.assertEqual(budget["completion"], "partial")
        self.assertLessEqual(len(self.fixture.calls()), 3)

    def test_shadow_keeps_case_files_and_shares_daily_spend(self):
        self.run_review(output="normal")
        before = self.fixture.ledger()
        result = self.run_review(output="shadow", extra=("--shadow", "comparison", "--shadow-budget-usd", "1"))
        after = self.fixture.ledger()
        self.assertEqual(result["execution_mode"], "shadow")
        self.assertEqual(result["completion"], "partial")
        self.assertEqual(before["prs"], after["prs"])
        self.assertGreater(sum(after["days"].values()), sum(before["days"].values()))
        self.assertFalse(result["merge_eligible"])
        self.assertTrue(list((self.root / "shadow/shadow-archive").rglob("*.json")))

    def test_contested_finding_uses_upstream_reply_path(self):
        (self.fixture.bin / "mode").write_text("request_changes")
        self.run_review(output="finding", extra=("--rubrics", "correctness"))
        (self.fixture.bin / "mode").write_text("approve")
        reply = self.root / "reply.txt"
        reply.write_text("Please reconsider this fixture finding: the approved definition is unchanged.")
        result = self.run_review(output="reply", extra=("--mode", "reply", "--reply-rubric", "correctness", "--reply-file", str(reply)))
        self.assertEqual(result["verdicts"]["correctness"], "approve")
        self.assertEqual(result["completion"], "partial")
        # Upstream may then sweep the other previously absent rubrics after this reply clears.
        self.assertTrue(any("Please reconsider" in c["prompt"] for c in self.fixture.calls()[1:]))

    def test_git_replacements_and_inherited_git_directory_cannot_change_evidence(self):
        git(self.fixture.repo, "replace", self.fixture.tooling, self.fixture.head)
        self.fixture.env["GIT_DIR"] = str(self.fixture.deps / "mathlib/.git")
        result = self.run_review(extra=("--dry-run", "--keep-workspace"))
        self.assertEqual(result["tooling"], self.fixture.tooling)
        self.assertTrue((self.root / "result/workspace/approved/README.md").read_text().startswith("APPROVED SENTINEL"))

    def test_promisor_sources_do_not_trigger_implicit_fetches(self):
        git(self.fixture.repo, "config", "remote.origin.promisor", "true")
        process = self.fixture.run(extra=("--dry-run",))
        self.assertEqual(process.returncode, 2)
        self.assertIn("promisor", process.stderr)
        self.assertFalse(self.fixture.calls())

    def test_invalid_reply_selection_cannot_silently_run_another_review(self):
        reply = self.root / "reply.txt"
        reply.write_text("Please reconsider.")
        for flags in (("--reply-file", str(reply)),
                      ("--mode", "reply", "--reply-rubric", "correctness", "--reply-file", str(reply), "--rubrics", "naming"),
                      ("--mode", "reply", "--reply-rubric", "correctness", "--reply-file", str(self.root / "missing"))):
            with self.subTest(flags=flags):
                self.assertEqual(self.fixture.run(extra=flags).returncode, 2)
        self.assertFalse(self.fixture.calls())

    def test_github_main_selects_approved_context_not_candidate_readme(self):
        import sys
        fixture = self.fixture
        repo = "thefundamentaltheor3m/SphereCeti"
        payloads = {f"repos/{repo}/pulls/1": {"number": 1, "title": "Proposed roadmap", "body": "untrusted",
                     "head": {"sha": fixture.head}, "base": {"sha": fixture.tooling, "repo": {"full_name": repo}}},
                    f"repos/{repo}/commits/main": {"sha": fixture.tooling}}
        fake = fixture.bin / "gh"
        fake.write_text(f"#!{sys.executable}\nimport json, sys\npayloads = {payloads!r}\n"
                        "assert sys.argv[1:4] == ['api', '--hostname', 'github.com'] and len(sys.argv) == 5\n"
                        "print(json.dumps(payloads[sys.argv[4]]))\n")
        fake.chmod(0o755)
        original = fixture.command(extra=("--dry-run", "--keep-workspace"))
        command = []
        i = 0
        while i < len(original):
            arg = original[i]
            if arg in ("--tooling", "--base", "--head"):
                i += 2
                continue
            if arg != "--local-sources":
                command.append(arg)
            i += 1
        process = subprocess.run(command, cwd=fixture.foreign, env=fixture.env,
                                 capture_output=True, text=True, timeout=120)
        self.assertEqual(process.returncode, 0, process.stderr)
        report = json.loads(process.stdout)
        self.assertTrue(report["tooling_approved"])
        self.assertEqual(report["context_authority"], "approved")
        self.assertTrue(all(e["revision"] == fixture.tooling for e in report["evidence"]))
        self.assertTrue((self.root / "result/workspace/approved/README.md").read_text().startswith("APPROVED SENTINEL"))
        self.assertFalse(report["merge_eligible"])

    def test_changed_context_invalidates_greens_but_keeps_budget(self):
        self.run_review(output="first")
        before = self.fixture.ledger()
        git(self.fixture.repo, "checkout", "-q", self.fixture.tooling)
        (self.fixture.repo / "CONVENTIONS.md").write_text("APPROVED SENTINEL changed convention")
        self.fixture.tooling = commit(self.fixture.repo)
        # Preserve the candidate head while changing the selected prospective context.
        self.run_review(output="second")
        after = self.fixture.ledger()
        self.assertEqual(len(self.fixture.calls()), 20)
        self.assertGreater(sum(after["days"].values()), sum(before["days"].values()))

    def test_provider_failure_is_an_error_not_an_approval(self):
        (self.fixture.bin / "mode").write_text("error")
        process = self.fixture.run()
        self.assertEqual(process.returncode, 1, process.stderr)
        result = json.loads(process.stdout)
        self.assertEqual(result["completion"], "error")
        self.assertFalse(result["merge_eligible"])

    def test_no_posting_flag_or_mutable_revision_is_accepted(self):
        process = self.fixture.run(extra=("--post",))
        self.assertEqual(process.returncode, 2)
        self.fixture.tooling = "main"
        process = self.fixture.run(extra=("--dry-run",))
        self.assertEqual(process.returncode, 2)
        self.assertFalse(self.fixture.calls())


if __name__ == "__main__":
    unittest.main()
