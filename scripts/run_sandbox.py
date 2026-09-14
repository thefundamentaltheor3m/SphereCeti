#!/usr/bin/env python3
"""Entrypoint for the workflow-approved sandbox launcher; invoke with python3 -I."""
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools' / 'project'))
from sphereceti.sandbox import main

if __name__ == '__main__':
    sys.exit(main())
