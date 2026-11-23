"""Proof PRs never edit SphereCeti.lean: the static contracts that make that safe.

Each library selects its modules with Lake's `andSubmodules` glob, so a topic module builds without
a root import; the compiled audit enumerates the source tree (see test_compiled_audits'
unimported-module cases). The root keeps its existing re-exports and is otherwise frozen.
scripts/check_roadmap.py keeps the globs and the root's import list fixed in ordinary CI.
"""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
IGNORED = shutil.ignore_patterns('.git', '.lake', '.venv', '__pycache__', 'dist')


class LibraryRootContractTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='sphereceti-root-contract-')
        self.addCleanup(self.temp.cleanup)
        self.copy = Path(self.temp.name) / 'repo'
        shutil.copytree(ROOT, self.copy, ignore=IGNORED)

    def check(self):
        return subprocess.run([sys.executable, '-I', str(self.copy / 'scripts/check_roadmap.py')],
                              capture_output=True, text=True, timeout=60)

    def edit(self, path, old, new):
        file = self.copy / path
        text = file.read_text()
        self.assertIn(old, text)
        file.write_text(text.replace(old, new))

    def test_installed_tree_satisfies_the_contract(self):
        result = self.check()
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_library_globs_cannot_be_narrowed(self):
        for library in ('SphereCeti', 'SphereCetiRoadmap'):
            with self.subTest(library=library):
                shutil.copy2(ROOT / 'lakefile.toml', self.copy / 'lakefile.toml')
                self.edit('lakefile.toml', f'globs = ["{library}.*"]', f'globs = ["{library}"]')
                result = self.check()
                self.assertEqual(result.returncode, 1)
                self.assertIn(f'library {library} must select its modules', result.stderr)

    def test_root_imports_are_frozen(self):
        # Existing re-exports stay (downstream `import SphereCeti` keeps working); nothing is added,
        # removed or reordered by a proof PR.
        lines = [l + '\n' for l in (ROOT / 'SphereCeti.lean').read_text().splitlines() if l.startswith('public import ')]
        first, second, last = lines[0], lines[1], lines[-1]
        edits = {
            'added public import': (first, first + 'public import SphereCeti.ZLattice.CovolumeBound\n'),
            'added plain import': (first, first + 'import SphereCeti.ZLattice.CovolumeBound\n'),
            'added indented meta import': (first, first + '  public meta import SphereCeti.ZLattice.CovolumeBound\n'),
            'removed re-export': (last, ''),
            'reordered': (first + second, second + first),
        }
        for name, (old, new) in edits.items():
            with self.subTest(name=name):
                shutil.copy2(ROOT / 'SphereCeti.lean', self.copy / 'SphereCeti.lean')
                self.edit('SphereCeti.lean', old, new)
                result = self.check()
                self.assertEqual(result.returncode, 1)
                self.assertIn('must keep exactly its frozen imports', result.stderr)
                self.assertIn('import topic modules directly', result.stderr)

    def test_existing_reexports_are_preserved(self):
        text = (ROOT / 'SphereCeti.lean').read_text()
        for module in ('SphereCeti.Basic', 'SphereCeti.Analysis.ExactZeroOrder',
                       'SphereCeti.Contour.HalfInfiniteRectangle', 'SphereCeti.CohnElkies.Certificate'):
            self.assertIn(f'public import {module}\n', text)


if __name__ == '__main__':
    unittest.main()
