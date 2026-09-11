#!/usr/bin/env bash
# Adapted from TauCetiProject/TauCeti@b743b607ce3e9742b18026ad79082e5d15badff5,
# scripts/sandbox-build.sh (Apache-2.0; TauCeti contributors).
# This workflow-approved copy is mounted separately from the exact candidate sources.
# I04 builds the complete inventory and checks compiled modules, axioms, lint, and the roadmap ledger.
set -euo pipefail
export TMPDIR=/project/.lake/tmp
mkdir -p "$TMPDIR"
# Python isolated mode excludes candidate cwd/PYTHONPATH; scripts always come from /gate.
lake env python3 -I /gate/scripts/check_audits.py --root /project
