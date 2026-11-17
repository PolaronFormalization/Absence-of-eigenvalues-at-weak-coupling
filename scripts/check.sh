#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Download the Mathlib cache separately once, with: lake exe cache get
lake build GW:elabArts Froehlich:elabArts
lake env lean -j1 verification/MN03FinalInterfaces.lean
lake env lean -j1 verification/MainDefinitionFingerprints.lean

echo 'Lean build and main-theorem inspection completed successfully.'
