#!/usr/bin/env python3
"""Check fresh wheel and sdist installs from a foreign working directory."""
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CHECK = r'''
import hashlib
from importlib import metadata, util
import json
from sphereceti_progress_sources import source_root

assert util.find_spec('progress') is None, 'upstream implementation must not be a global package'
dist = metadata.distribution('sphereceti-progress-sources')
assert not dist.entry_points, 'inactive import must not install commands'
root = source_root()
manifest = json.loads(root.joinpath('import-manifest.json').read_text())
assert len(manifest['files']) == 32
for row in manifest['files']:
    assert hashlib.sha256(root.joinpath(row['destination']).read_bytes()).hexdigest() == row['import_sha256'], row['destination']
for name in ('progress', 'status'):
    assert root.joinpath(f'progress/prompts/{name}.md').read_text().strip()
assert 'Apache License' in root.joinpath('LICENSE').read_text()
print('fresh installed resources verified; no global progress package or console commands')
'''


def main():
    artifacts = ROOT / "tools/progress/dist"
    wheels, sources = list(artifacts.glob("*.whl")), list(artifacts.glob("*.tar.gz"))
    if len(wheels) != 1 or len(sources) != 1:
        raise SystemExit("build exactly one wheel and one source archive first")
    uv = shutil.which("uv")
    if not uv:
        raise SystemExit("uv is required")
    for artifact in wheels + sources:
        with tempfile.TemporaryDirectory(prefix="sphereceti-progress-package-") as temp:
            cwd = Path(temp)
            python = cwd / "venv/bin/python"
            subprocess.run([uv, "venv", str(cwd / "venv")], check=True)
            subprocess.run([uv, "pip", "install", "--python", str(python), str(artifact)],
                           cwd=cwd, check=True)
            # Conflicting local files cannot supply resources to an installed package.
            (cwd / "progress/prompts").mkdir(parents=True)
            (cwd / "progress/prompts/progress.md").write_text("wrong local prompt")
            subprocess.run([str(python), "-I", "-B", "-c", CHECK], cwd=cwd, check=True)
            print("passed:", artifact.name, flush=True)


if __name__ == "__main__":
    main()
