#!/usr/bin/env python3
"""Static contract checks for the SphereCeti roadmap package."""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = {
    "lean": "leanprover/lean4:v4.34.0-rc1",
    "tauceti": "8671bee98125933c56b9b00a08ded873b77dd23b",
    "mathlib": "618f225e1ff4a6b2790a944e01b806b7c68bdc56",
    "sphere_packing": "bad3de916074748eb88b7d1ee6dbf9494361ad17",
}

errors: list[str] = []

def require(condition: bool, message: str) -> None:
    if not condition:
        errors.append(message)

# Pin coherence.
toolchain = (ROOT / "lean-toolchain").read_text().strip()
require(toolchain == EXPECTED["lean"], f"lean-toolchain is {toolchain!r}")

lakefile = (ROOT / "lakefile.toml").read_text()
require(EXPECTED["tauceti"] in lakefile, "TauCeti SHA missing from lakefile.toml")
require("Sphere-Packing-Lean" not in lakefile, "roadmap must not import the 4.32 production package")

manifest = json.loads((ROOT / "lake-manifest.json").read_text())
require(manifest.get("name") == "SphereCeti", "manifest package name is not SphereCeti")
packages = {p["name"]: p for p in manifest["packages"]}
require(packages.get("TauCeti", {}).get("rev") == EXPECTED["tauceti"],
        "TauCeti manifest revision does not match the declared pin")
require(packages.get("TauCeti", {}).get("inputRev") == EXPECTED["tauceti"],
        "TauCeti manifest inputRev is not the exact commit pin")
require(packages.get("mathlib", {}).get("rev") == EXPECTED["mathlib"],
        "Mathlib manifest revision does not match the TauCeti snapshot")
require(packages.get("Cli", {}).get("inputRev") == "v4.34.0-rc1",
        "Lean CLI dependency is not on the v4.34.0-rc1 release line")

readme = (ROOT / "README.md").read_text()
provenance = (ROOT / "PROVENANCE.md").read_text()
require(EXPECTED["sphere_packing"] in readme, "Sphere-Packing semantic baseline missing from README")
for key, value in EXPECTED.items():
    require(value in readme or key == "lean" and value in toolchain,
            f"README does not record {key} pin {value}")
    require(value in provenance, f"PROVENANCE.md does not record {key} pin {value}")

# Local Markdown links should resolve. Ignore external URLs and anchors, and skip the Lake
# build directory, whose dependency checkouts carry their own documentation.
for md in ROOT.rglob("*.md"):
    if ".lake" in md.parts:
        continue
    text = md.read_text()
    for target in re.findall(r"\[[^\]]+\]\(([^)]+)\)", text):
        clean = target.split("#", 1)[0]
        if not clean or "://" in clean or clean.startswith("mailto:"):
            continue
        require((md.parent / clean).exists(), f"broken local link in {md.name}: {target}")

# Suggested targets must be mathematical declarations, not vacuous placeholders.
for lean in (ROOT / "SphereCeti").glob("*.lean"):
    text = lean.read_text()
    require("by\n  exact True.intro" not in text, f"vacuous True proof in {lean.name}")
    require(not re.search(r"(?:theorem|lemma)\s+\w+[^:]*:\s*True\b", text),
            f"vacuous True target in {lean.name}")
    require(text.endswith("\n"), f"missing final newline in {lean.name}")

# The roadmap must expose the agreed summit and classification boundaries.
suggested = (ROOT / "SphereCeti" / "Suggested.lean").read_text()
for declaration in (
    "spherePackingConstant_eight",
    "spherePackingConstant_twentyFour",
    "uniqueOptimalPeriodic",
    "even_unimodular_rank_eight_unique",
    "rootless_even_unimodular_rank_twentyFour_unique",
    "generated_covolume_eq_one_and_index_eq_numOrbits",
):
    require(declaration in suggested, f"missing roadmap declaration boundary: {declaration}")

upstream = (ROOT / "UPSTREAM.md").read_text()
for heading in (
    "Focused Mathlib candidates",
    "TauCeti IntegralLattices roadmap extensions",
    "TauCeti coding-theory and code-lattice roadmap",
    "Larger TauCeti roadmaps suggested by the uniqueness literature",
):
    require(heading in upstream, f"UPSTREAM.md is missing section: {heading}")
require(not (ROOT / "Mathlib").exists(), "do not create a parallel Mathlib roadmap directory")
require(not (ROOT / "TauCetiRoadmap").exists(),
        "do not create a parallel TauCeti roadmap directory")

# This is intentionally a roadmap: sorries are expected, but count them visibly and keep the
# validation ledger synchronized.
sorry_count = sum(p.read_text().count("sorry") for p in (ROOT / "SphereCeti").glob("*.lean"))
validation = (ROOT / "VALIDATION.md").read_text()
require(f"{sorry_count} intentional `sorry` occurrences" in validation,
        "VALIDATION.md has a stale intentional-sorry count")
print(f"roadmap static checks: {sorry_count} intentional sorry occurrences")

if errors:
    for error in errors:
        print(f"ERROR: {error}", file=sys.stderr)
    raise SystemExit(1)
print("roadmap static checks: OK")
