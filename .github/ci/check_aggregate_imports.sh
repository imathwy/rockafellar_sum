#!/usr/bin/env bash
set -euo pipefail

check_aggregate() {
  local root="$1"
  local aggregate="$2"
  local expected_file actual_file
  expected_file="$(mktemp)"
  actual_file="$(mktemp)"
  trap 'rm -f "$expected_file" "$actual_file"' RETURN

  find "$root" -type f -name '*.lean' -printf '%P\n' |
    sed -e 's/\.lean$//' -e 's#/#.#g' | sort >"$expected_file"
  sed -n "s/^public import ${root}\.//p" "$aggregate" | sort >"$actual_file"

  if ! diff -u "$expected_file" "$actual_file"; then
    echo "aggregate import coverage mismatch: $aggregate" >&2
    return 1
  fi
}

check_aggregate ReasLib ReasLib.lean
check_aggregate S2 S2.lean
