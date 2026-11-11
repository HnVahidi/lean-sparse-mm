#!/usr/bin/env bash
set -euo pipefail

repo=$(cd "$(dirname "$0")/.." && pwd -P)
cd "$repo"
commit=$(git rev-parse --verify 'HEAD^{commit}')
if ! git diff --quiet "$commit" -- .; then
  echo 'Commit the tracked source changes before running exact-commit verification.' >&2
  exit 1
fi
mkdir -p .lake/verification
evidence=$(mktemp -d "$repo/.lake/verification/run-$(date -u +%Y%m%dT%H%M%SZ).XXXXXXXX")
temporary_parent=$(realpath "${TMPDIR:-/tmp}")
scratch=$(mktemp -d "$temporary_parent/lean-sparse-mm.XXXXXXXX")
case "$scratch" in
  "$temporary_parent"/lean-sparse-mm.*) ;;
  *) echo 'Unexpected temporary verification directory.' >&2; exit 1 ;;
esac
cleanup() {
  result=$?
  cd "$repo"
  rm -rf -- "$scratch" || result=1
  printf 'exit_code=%s\n' "$result" > "$evidence/run-status.txt"
  printf 'Verification evidence retained in %s\n' "${evidence#"$repo/"}"
  exit "$result"
}
trap cleanup EXIT

mirror="$scratch/source"
mkdir "$mirror"
python3 scripts/source_snapshot.py create "$repo" "$commit" "$mirror" "$evidence/source-snapshot.json" \
  2>&1 | tee "$evidence/snapshot.log"
cd "$mirror"
python3 scripts/source_snapshot.py verify "$mirror" "$evidence/source-snapshot.json" "$evidence/input-comparison.json" --exact
python3 scripts/check_sources.py 2>&1 | tee "$evidence/source-check.log"
python3 scripts/build_challenge.py --check 2>&1 | tee "$evidence/interface-check.log"
python3 scripts/check_metadata.py "$evidence" 2>&1 | tee "$evidence/metadata.log"
python3 scripts/check_dependencies.py --manifest-only

unset LEAN_PATH LEAN_SRC_PATH MATHLIB_CACHE_GET_URL MATHLIB_CACHE_DEBUG_USE_LEGACY
prefix=$(lean --print-prefix)
export PATH="$prefix/bin:$PATH"
export GIT_TERMINAL_PROMPT=0
export MATHLIB_CACHE_DIR="$scratch/mathlib-cache"
config="$scratch/effective-comparator.json"
python3 scripts/prepare_comparator.py "$prefix" "$config" "$evidence/provenance.json"
chmod 0444 "$config"

# Lake materializes the existing manifest. The source byte checks detect any change to it.
lake env true 2>&1 | tee "$evidence/dependency-fetch.log"
python3 scripts/check_dependencies.py "$evidence" 2>&1 | tee "$evidence/dependency-check.log"
module_names=$(python3 scripts/check_sources.py --mathlib-imports)
mapfile -t modules <<< "$module_names"
lake exe cache --repo=leanprover-community/mathlib4 get "${modules[@]}" 2>&1 | tee "$evidence/mathlib-cache.log"
lake build 2>&1 | tee "$evidence/build.log"
python3 scripts/audit_axioms.py "$evidence"
bash scripts/verify-comparator.sh "$prefix" "$config" "$evidence"
python3 scripts/source_snapshot.py verify "$mirror" "$evidence/source-snapshot.json" "$evidence/output-comparison.json" --exact
python3 scripts/source_snapshot.py verify "$repo" "$evidence/source-snapshot.json" "$evidence/live-comparison.json"
