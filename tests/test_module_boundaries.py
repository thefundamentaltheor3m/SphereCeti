"""Real Lean-header regression tests in disposable projects; no fixture proofs are published."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


CHECKER = Path(__file__).resolve().parents[1] / "scripts" / "check_modules.py"


class ModuleBoundariesTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="sphereceti-modules-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.write("SphereCeti.lean", "module\n")
        self.write("SphereCetiRoadmap.lean", "module\n")

    def write(self, path, source):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(source)
        return target

    def run_check(self):
        return subprocess.run(
            [sys.executable, str(CHECKER), "--root", str(self.root), "--json"],
            capture_output=True, text=True, timeout=60,
        )

    def assert_rejected(self, message):
        result = self.run_check()
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn(message, result.stderr)

    def test_roadmap_may_import_library(self):
        self.write("SphereCetiRoadmap.lean", "module\npublic import SphereCeti\n")
        result = self.run_check()
        self.assertEqual(result.returncode, 0, result.stderr)
        records = json.loads(result.stdout)["modules"]
        self.assertEqual(records[1]["imports"], ["SphereCeti"])

    def test_direct_roadmap_import(self):
        self.write("SphereCeti.lean", "module\npublic import SphereCetiRoadmap\n")
        self.assert_rejected("forbidden import: SphereCeti (library) -> SphereCetiRoadmap")

    def test_transitive_roadmap_import(self):
        self.write("SphereCeti.lean", "module\npublic import SphereCeti.Bridge\n")
        self.write("SphereCeti/Bridge.lean", "module\nimport SphereCetiRoadmap\n")
        self.assert_rejected("forbidden import: SphereCeti.Bridge")

    def test_unimported_nested_module_is_checked(self):
        self.write("SphereCeti/Unused/Hidden.lean", "module\nimport SphereCetiRoadmap\n")
        self.assert_rejected("forbidden import: SphereCeti.Unused.Hidden")

    def test_unknown_nested_source(self):
        self.write("Unclassified/Nested.lean", "module\n")
        self.assert_rejected("unclassified Lean source")

    def test_library_cannot_import_fixture_or_tool(self):
        for path in ("tests/fixtures/Target.lean", "scripts/Target.lean"):
            with self.subTest(path=path):
                self.write(path, "module\n")
                module = path.removesuffix(".lean").replace("/", ".")
                self.write("SphereCeti.lean", f"module\nimport {module}\n")
                self.assert_rejected("forbidden import")

    def test_lean_parser_handles_comments_and_escaped_names(self):
        self.write("SphereCeti.lean", "module\n/- import SphereCetiRoadmap /- nested -/ -/\n")
        result = self.run_check()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.write("SphereCeti.lean", "module\npublic /- comment -/ import «SphereCetiRoadmap»\n")
        self.assert_rejected("forbidden import")

    def test_missing_import(self):
        self.write("SphereCeti.lean", "module\nimport SphereCeti.Missing\n")
        self.assert_rejected("missing import source")

    def test_inherited_source_path_cannot_supply_unclassified_modules(self):
        with tempfile.TemporaryDirectory(prefix="sphereceti-foreign-") as directory:
            Path(directory, "Foreign.lean").write_text("module\n")
            self.write("SphereCeti.lean", "module\nimport Foreign\n")
            env = os.environ.copy()
            env["LEAN_SRC_PATH"] = directory + os.pathsep + env.get("LEAN_SRC_PATH", "")
            result = subprocess.run(
                [sys.executable, str(CHECKER), "--root", str(self.root)],
                env=env, capture_output=True, text=True, timeout=60,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("import outside inventory", result.stderr)

    def test_missing_aggregator(self):
        (self.root / "SphereCetiRoadmap.lean").unlink()
        self.assert_rejected("missing library aggregator")

    def test_symlinked_file_and_directory(self):
        for name, target in (("SphereCeti/Link.lean", "../SphereCetiRoadmap.lean"),
                             ("SphereCeti/Linked", "../outside")):
            with self.subTest(name=name):
                link = self.root / name
                link.parent.mkdir(exist_ok=True)
                os.symlink(target, link)
                # A broken directory link is also an invalid source route, once it exists.
                (self.root / "outside").mkdir(exist_ok=True)
                self.assert_rejected("symlinked source path")
                link.unlink()

    def test_dependencies_are_excluded_only_at_root(self):
        self.write(".lake/packages/Foreign/Target.lean", "not valid Lean\n")
        self.assertEqual(self.run_check().returncode, 0)
        self.write("hidden/.lake/Target.lean", "module\n")
        self.assert_rejected("invalid module path")


if __name__ == "__main__":
    unittest.main()
