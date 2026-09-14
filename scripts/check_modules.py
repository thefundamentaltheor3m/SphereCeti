#!/usr/bin/env python3
"""Inventory project Lean sources and check their import boundaries using Lean's parser.

Design adapted from TauCeti's fail-closed source inventory:
TauCetiProject/TauCeti@8671bee98125933c56b9b00a08ded873b77dd23b,
scripts/source-modules.sh. This Python implementation adds SphereCeti's roadmap boundary.
Run under `lake env`; this is an import check, not a compiled axiom audit or a sandbox.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import asdict, dataclass
from pathlib import Path


class BoundaryError(Exception):
    """The inventory or an import cannot be accepted."""


@dataclass(frozen=True)
class Module:
    name: str
    path: str
    kind: str


# Only generated/dependency locations are excluded, and only at the project root.
EXCLUDED = {".git", ".lake", ".venv"}
PART = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\Z")
ALLOWED_IMPORTS = {
    "library": {"library"},
    "roadmap": {"library", "roadmap"},
    "tooling": {"library", "roadmap", "tooling"},
    "fixture": {"library", "roadmap", "tooling", "fixture"},
}


def classify(path: Path) -> Module:
    parts = path.with_suffix("").parts
    if not all(PART.fullmatch(part) for part in parts):
        raise BoundaryError(f"invalid module path: {path}")
    if parts[0] == "SphereCeti":
        kind = "library"
    elif parts[0] == "SphereCetiRoadmap":
        kind = "roadmap"
    elif len(parts) > 1 and parts[0] == "scripts":
        kind = "tooling"
    elif len(parts) > 2 and parts[:2] == ("tests", "fixtures"):
        kind = "fixture"
    else:
        raise BoundaryError(f"unclassified Lean source: {path}")
    return Module(".".join(parts), path.as_posix(), kind)


def inventory(root: Path) -> list[Module]:
    modules = []

    def walk_error(error: OSError) -> None:
        raise error

    for directory, dirs, files in os.walk(root, onerror=walk_error, followlinks=False):
        base = Path(directory)
        if base == root:
            dirs[:] = [d for d in dirs if d not in EXCLUDED]
        for name in dirs + files:
            path = base / name
            if path.is_symlink() and (name in dirs or path.suffix == ".lean"):
                raise BoundaryError(f"symlinked source path: {path.relative_to(root)}")
        for name in sorted(files):
            path = base / name
            if path.suffix == ".lean":
                modules.append(classify(path.relative_to(root)))
    paths = {m.path for m in modules}
    for required in ("SphereCeti.lean", "SphereCetiRoadmap.lean"):
        if required not in paths:
            raise BoundaryError(f"missing library aggregator: {required}")
    return sorted(modules, key=lambda m: m.name)


def source_dependencies(root: Path, module: Module) -> list[Path]:
    env = os.environ.copy()
    # The candidate's own source takes precedence over any surrounding Lake project.
    env["LEAN_SRC_PATH"] = str(root) + os.pathsep + env.get("LEAN_SRC_PATH", "")
    result = subprocess.run(
        ["lean", "--src-deps", module.path], cwd=root, env=env,
        text=True, capture_output=True, timeout=60, check=False,
    )
    if result.returncode:
        raise BoundaryError(
            f"cannot read imports for {module.path}:\n{result.stdout}{result.stderr}"
        )
    return [(root / line).resolve() for line in result.stdout.splitlines() if line]


def check(root: Path) -> dict:
    modules = inventory(root)
    by_path = {(root / m.path).resolve(): m for m in modules}
    prefix = subprocess.run(
        ["lean", "--print-prefix"], text=True, capture_output=True, timeout=60, check=True,
    ).stdout.strip()
    dependency_roots = ((root / ".lake" / "packages").resolve(),
                        (Path(prefix) / "src" / "lean").resolve())
    records = []
    for module in modules:
        imports = set()
        for dependency in source_dependencies(root, module):
            if not dependency.is_file():
                raise BoundaryError(f"missing import source: {module.name} -> {dependency}")
            if dependency in by_path:
                imported = by_path[dependency]
                imports.add(imported.name)
                if imported.kind not in ALLOWED_IMPORTS[module.kind]:
                    raise BoundaryError(
                        f"forbidden import: {module.name} ({module.kind}) -> "
                        f"{imported.name} ({imported.kind})"
                    )
            elif not any(dependency.is_relative_to(base) for base in dependency_roots):
                raise BoundaryError(f"import outside inventory: {module.name} -> {dependency}")
        records.append({**asdict(module), "imports": sorted(imports)})
    # Checking every edge also rules out a transitive library -> roadmap/tooling/fixture path.
    return {"modules": records}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--json", action="store_true", help="emit the checked module inventory")
    args = parser.parse_args()
    try:
        report = check(args.root.resolve())
    except (BoundaryError, OSError, subprocess.SubprocessError) as error:
        print(f"module boundaries: {error}", file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(f"module boundaries: {len(report['modules'])} modules checked; OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
