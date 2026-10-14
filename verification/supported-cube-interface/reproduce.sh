#!/usr/bin/env bash
set -euo pipefail
# Run from the repository root with the pinned Lean toolchain available.
python scripts/verify_snapshot.py
lake build Hindman168.OriginalSupportedCubeInterval
lake env lean --trust=0 verification/supported-cube-interface/CheckAllDeclarations.lean
sha256sum --check verification/supported-cube-interface/source-sha256.txt
