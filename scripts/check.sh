#!/usr/bin/env bash
# Rebuild the proofs and regenerate the validation reports. Every check fails
# on a mismatch. The larger exact Algorithm S suite can be run separately.
set -euo pipefail
cd "$(dirname "$0")/.."

python3 scripts/check_formalization.py
python3 scripts/run_cycle_fpras_checks.py
python3 scripts/algs_transcription/run.py 1
