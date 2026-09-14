#!/usr/bin/env python3
"""Validate host-prepared dependencies against T's unchanged manifest before staging D."""
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
assert manifest['packagesDir'] == '.lake/packages'
for package in manifest['packages']:
    assert package['type'] == 'git', 'Only exact Git dependencies are supported'
    assert re.fullmatch(r'[A-Za-z0-9_-]+', package['name'])
    assert re.fullmatch(r'[0-9a-f]{40}', package['rev'])
    directory = ROOT / '.lake/packages' / package['name']
    actual = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
    assert actual == package['rev'], f"Dependency revision mismatch: {package['name']}"
    dirty = subprocess.check_output(['git', '-C', str(directory), 'status', '--porcelain',
                                     '--untracked-files=no'], text=True)
    assert not dirty, f"Dependency tracked sources changed: {package['name']}"
print('Validated all dependency checkouts against the approved manifest.')
