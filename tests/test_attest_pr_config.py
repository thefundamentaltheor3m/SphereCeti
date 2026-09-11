"""Adapted from TauCetiProject/TauCeti@b743b607ce3e9742b18026ad79082e5d15badff5,
scripts/test_attest_pr_config.py (Apache-2.0; TauCeti contributors).
SphereCeti requires unchanged pins as well as an unchanged Lake configuration.
"""

from __future__ import annotations

import pathlib
import subprocess
import tempfile
import unittest


ROOT = pathlib.Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "attest-pr-config.sh"


class ConfigAttestation(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.temp.name)
        self.mergebase = self.root / "mergebase"
        self.candidate = self.root / "candidate"
        self.mergebase.mkdir()
        self.candidate.mkdir()
        for directory in (self.mergebase, self.candidate):
            (directory / "lakefile.toml").write_text('name = "TauCeti"\n')
            (directory / "lake-manifest.json").write_text('{"packages": []}\n')
            (directory / "lean-toolchain").write_text("leanprover/lean4:v4.34.0-rc1\n")
        subprocess.run(["git", "init", "-q"], cwd=self.candidate, check=True)
        subprocess.run(["git", "add", "."], cwd=self.candidate, check=True)
        subprocess.run(
            ["git", "-c", "user.name=test", "-c", "user.email=test@example.com", "commit", "-qm", "fixture"],
            cwd=self.candidate,
            check=True,
        )
        self.sha = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=self.candidate, text=True
        ).strip()

    def tearDown(self) -> None:
        self.temp.cleanup()

    def run_attestation(
        self, *, event: str = "pull_request_target", exact: str = "1", pins: str = "0"
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [
                "bash",
                str(SCRIPT),
                str(self.mergebase),
                str(self.candidate),
                self.sha,
                event,
                exact,
                pins,
            ],
            text=True,
            capture_output=True,
        )

    def test_unchanged_config_passes(self) -> None:
        self.assertEqual(self.run_attestation().returncode, 0)

    def test_lakefile_change_fails(self) -> None:
        (self.candidate / "lakefile.toml").write_text('name = "Other"\n')
        self.assertNotEqual(self.run_attestation().returncode, 0)

    def test_introduced_lakefile_lean_fails(self) -> None:
        (self.candidate / "lakefile.lean").write_text("import Lake\n")
        self.assertNotEqual(self.run_attestation().returncode, 0)

    def test_symlinked_lakefile_fails(self) -> None:
        (self.candidate / "lakefile.toml").unlink()
        (self.candidate / "lakefile.toml").symlink_to("lean-toolchain")
        self.assertNotEqual(self.run_attestation().returncode, 0)

    def test_pin_delta_must_match_tree_attestation(self) -> None:
        (self.candidate / "lean-toolchain").write_text("leanprover/lean4:v4.34.0\n")
        self.assertNotEqual(self.run_attestation(pins="0").returncode, 0)
        self.assertNotEqual(self.run_attestation(pins="1").returncode, 0)

    def test_unresolved_merge_base_and_unsupported_event_fail(self) -> None:
        self.assertNotEqual(self.run_attestation(exact="0").returncode, 0)
        self.assertNotEqual(
            self.run_attestation(event="merge_group", exact="0").returncode,
            0,
        )

    def test_wrong_head_fails(self) -> None:
        original = self.sha
        self.sha = "0" * 40
        try:
            self.assertNotEqual(self.run_attestation().returncode, 0)
        finally:
            self.sha = original


if __name__ == "__main__":
    unittest.main()
