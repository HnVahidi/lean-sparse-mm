#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 1 ]]; then
  echo 'Usage: install-bubblewrap.sh <destination bin directory>' >&2
  exit 2
fi
mkdir -p "$1"
destination=$(realpath "$1")
revision=2a76602a8c71f36c1527cf9fc3417d9149822e0c
temporary_parent=$(realpath "${TMPDIR:-/tmp}")
scratch=$(mktemp -d "$temporary_parent/lean-sparse-mm-bwrap.XXXXXXXX")
case "$scratch" in
  "$temporary_parent"/lean-sparse-mm-bwrap.*) ;;
  *) echo 'Unexpected temporary Bubblewrap directory.' >&2; exit 1 ;;
esac
trap 'rm -rf -- "$scratch"' EXIT
git init -q "$scratch/source"
git -C "$scratch/source" fetch --depth 1 https://github.com/containers/bubblewrap.git "$revision"
git -C "$scratch/source" checkout -q --detach FETCH_HEAD
test "$(git -C "$scratch/source" rev-parse HEAD)" = "$revision"
meson setup "$scratch/build" "$scratch/source" --buildtype=release \
  -Dman=disabled -Dselinux=disabled -Dtests=false -Dbash_completion=disabled -Dzsh_completion=disabled
meson compile -C "$scratch/build" bwrap
install -m 0755 "$scratch/build/bwrap" "$destination/bwrap"
"$destination/bwrap" --version
