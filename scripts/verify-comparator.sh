#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 3 ]]; then
  echo 'Usage: verify-comparator.sh <Lean prefix> <effective config> <evidence directory>' >&2
  exit 2
fi
cd "$(dirname "$0")/.."
prefix=$1
config=$2
evidence=$3
set +e
"$prefix/bin/lake" comparator --config "$config" 2>&1 | tee "$evidence/comparator.log"
pipeline_status=("${PIPESTATUS[@]}")
set -e
python3 scripts/prepare_comparator.py --record-exit "${pipeline_status[0]}" "${pipeline_status[1]}" \
  "$prefix" "$config" "$evidence/provenance.json"
