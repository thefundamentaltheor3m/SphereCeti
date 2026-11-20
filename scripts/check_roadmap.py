#!/usr/bin/env python3
"""Static contract checks for the SphereCeti roadmap package."""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = {
    "lean": "leanprover/lean4:v4.36.0-rc2",
    "tauceti": "83769e442d55cda9d85b3927a93b286831c595ff",
    "mathlib": "1b1ccf4b088b32fa3f23f2de1127433254a81e1e",
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
require(packages.get("Cli", {}).get("inputRev") == "v4.36.0-rc2",
        "Lean CLI dependency is not on the v4.36.0-rc2 release line")

readme = (ROOT / "README.md").read_text()
provenance = (ROOT / "PROVENANCE.md").read_text()
require(EXPECTED["sphere_packing"] in readme, "Sphere-Packing semantic baseline missing from README")
for key, value in EXPECTED.items():
    require(value in readme or key == "lean" and value in toolchain,
            f"README does not record {key} pin {value}")
    require(value in provenance, f"PROVENANCE.md does not record {key} pin {value}")

# Check owned roadmap documentation; imported upstream documentation keeps its own links.
for name in ("README.md", "CONTRIBUTING.md", "CONVENTIONS.md", "MIGRATION.md",
             "PROVENANCE.md", "UPSTREAM.md", "VALIDATION.md", "AGENTS.md"):
    md = ROOT / name
    text = md.read_text()
    for target in re.findall(r"\[[^\]]+\]\(([^)]+)\)", text):
        clean = target.split("#", 1)[0]
        if not clean or "://" in clean or clean.startswith("mailto:"):
            continue
        require((md.parent / clean).exists(), f"broken local link in {md.name}: {target}")

# Suggested targets must be mathematical declarations, not vacuous placeholders.
for lean in (ROOT / "SphereCetiRoadmap").glob("*.lean"):
    text = lean.read_text()
    require("by\n  exact True.intro" not in text, f"vacuous True proof in {lean.name}")
    require(not re.search(r"(?:theorem|lemma)\s+\w+[^:]*:\s*True\b", text),
            f"vacuous True target in {lean.name}")
    require(text.endswith("\n"), f"missing final newline in {lean.name}")

# The roadmap must expose the agreed summit and classification boundaries.
pinned = (ROOT / "SphereCetiRoadmap" / "Pinned.lean").read_text()
require("public import Mathlib\n" not in pinned,
        "Pinned.lean must import the intended Mathlib modules, not the aggregate root")
suggested = (ROOT / "SphereCetiRoadmap" / "Suggested.lean").read_text()
require("Quotient P.addAction.orbitRel" in suggested,
        "Orbit must reuse the pinned production additive-action quotient")
require("def orbitSetoid" not in suggested,
        "Suggested.lean must not define a duplicate periodic orbit setoid")
# Split the source into top-level chunks (declarations, doc comments, commands) so that a name
# mentioned in a `#check` line or a docstring does not count as a use inside a proof.
TOP_LEVEL = re.compile(
    r"^(?:/--|/-!|@\[|#\w+|(?:private |protected )?(?:noncomputable )?"
    r"(?:theorem|lemma|def|abbrev|example|instance|structure|class|inductive|section|namespace|"
    r"end|variable|open|universe)\b)", re.M)

def top_level_chunks(text: str) -> list[str]:
    starts = [m.start() for m in TOP_LEVEL.finditer(text)] + [len(text)]
    return [text[a:b] for a, b in zip(starts, starts[1:])]

def declaration_chunk(text: str, keyword: str, name: str) -> str:
    pattern = re.compile(rf"^(?:noncomputable )?{keyword} {re.escape(name)}\b")
    found = [chunk for chunk in top_level_chunks(text) if pattern.match(chunk)]
    return found[0] if len(found) == 1 else ""

require("namespace ThetaSeries" not in suggested,
        "TauCeti supplies the theta theory; do not restate it in a local ThetaSeries namespace")
theta_section = re.search(r"^section ThetaSeries\n(.*?)^end ThetaSeries$", suggested, re.M | re.S)
require(theta_section is not None, "missing section ThetaSeries of typed TauCeti theta checks")
theta_examples = [chunk for chunk in top_level_chunks(theta_section.group(1) if theta_section else "")
                  if chunk.startswith("example") and "sorry" not in chunk]
# Each API must be applied in the proof of a sorry-free `example` (dot notation is accepted for the
# `IsEven` lemmas, whose receiver is the evenness hypothesis).
for theta_api in (
    "ZLattice.thetaSeries_S_smul",
    "ZLattice.coe_thetaForm",
    "ZLattice.qExpansion_thetaForm_coeff",
    "thetaForm_eq_E₄",
    "representationNumber_two_of_finrank_eq_eight",
    "thetaSeries_eq_E₄_cube_add_mul_discriminant",
    "representationNumber_four_of_rootless",
):
    require(any(re.search(rf"(?<![\w.]){re.escape(theta_api)}\b|\.{re.escape(theta_api)}\b",
                          chunk.split(":=", 1)[-1]) for chunk in theta_examples),
            f"no sorry-free typed example in section ThetaSeries applies the TauCeti theta API {theta_api}")

# The presentation bridge: an isometry into TauCeti's rational model, and the real evenness and
# unimodularity proved by transporting TauCeti's ratModel comparisons along it.
bridge = declaration_chunk(suggested, "def", "IntegralPresentation.ratModelIsometry")
require("TauCeti.IntegralLattice.Isometry P.toIntegralLattice (ZLattice.ratModel" in bridge,
        "IntegralPresentation.ratModelIsometry must be an isometry into TauCeti's ZLattice.ratModel")
for name, comparison, transport in (
    ("IntegralPresentation.isEven_real", "ZLattice.isEven_ratModel_iff", "isEven_iff"),
    ("IntegralPresentation.isUnimodular_real", "ZLattice.isUnimodular_ratModel_iff",
     "isUnimodular_iff"),
):
    proof = declaration_chunk(suggested, "theorem", name).split(":=", 1)
    require(len(proof) == 2 and "sorry" not in proof[1] and comparison in proof[1]
            and f"P.ratModelIsometry.{transport}" in proof[1],
            f"{name} must be proved from {comparison} transported along P.ratModelIsometry")
require("ADEType" not in suggested and "NiemeierType" not in suggested,
        "ADE and Niemeier machinery is owned upstream; only the classification endpoints remain")
require("% 23 ∈ ({0, 1, 5, 6, 7, 9, 11}" in suggested,
        "Golay generator rows must use cyclic indexing modulo 23")
for certificate in (
    "golayPivotMinor_unitriangular",
    "golayGeneratorMatrix_rowWeight",
    "basisCoordinateMatrix_det",
):
    require(certificate in suggested, f"missing finite-data certificate: {certificate}")
require(suggested.count("CohnElkies.Certificate.ofRadial") >= 2,
        "the dimension-specific certificates must be literal ofRadial applications")
for adapter, equation in (
    ("thetaForm", "coe_thetaForm"),
    ("certificate", "certificate_f"),
    ("packing", "packing_centers"),
):
    require(adapter in suggested and equation in suggested,
            f"adapter {adapter} is missing characteristic equation {equation}")
for declaration in (
    "spherePackingConstant_eight",
    "spherePackingConstant_twentyFour",
    "uniqueOptimalPeriodic",
    "even_unimodular_rank_eight_unique",
    "rootless_even_unimodular_rank_twentyFour_unique",
    "generated_covolume_eq_one_and_index_eq_numOrbits",
    "exists_translatedBox_normalizedCount_ge_finiteDensity_sub",
    "perm_leftLegs_eq_smul_rightLegs",
    "fourier_leftComponent",
    "fourier_centralComponent",
    "fourier_reverse",
    "fourier_sixPieceComponent",
    "horizontal_add_vertical_eq_vertical_of_tendsto_top",
):
    require(declaration in suggested, f"missing roadmap declaration boundary: {declaration}")

# The characteristic equations and applied contour Fourier identities must exist in both the E8
# and the Leech namespaces: at least one statement plus one use per dimension.
for declaration in (
    "magicPlus_eq_sixPieceComponent",
    "magicMinus_eq_sixPieceComponent",
    "fourier_sixPiece_plus",
    "fourier_sixPiece_minus",
):
    require(suggested.count(declaration) >= 4,
            f"declaration boundary not present in both dimensions: {declaration}")

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
# validation ledger synchronized. Count standalone `sorry` commands (a line consisting of the
# keyword), not textual substrings, so documentation mentions of the word do not inflate the
# ledger.
sorry_command = re.compile(r"^\s*sorry\s*$", re.MULTILINE)
sorry_count = sum(len(sorry_command.findall(p.read_text()))
                  for p in (ROOT / "SphereCetiRoadmap").glob("*.lean"))
validation = (ROOT / "VALIDATION.md").read_text()
require(f"{sorry_count} intentional `sorry` commands" in validation,
        "VALIDATION.md has a stale intentional-sorry count")
print(f"roadmap static checks: {sorry_count} intentional sorry commands")

if errors:
    for error in errors:
        print(f"ERROR: {error}", file=sys.stderr)
    raise SystemExit(1)
print("roadmap static checks: OK")
