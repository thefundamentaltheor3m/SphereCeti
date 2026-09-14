#!/usr/bin/env bash
# Adapted from TauCetiProject/TauCeti@b743b607ce3e9742b18026ad79082e5d15badff5,
# scripts/attest-pr-config.sh (Apache-2.0; TauCeti contributors).
# SphereCeti I03 admits no dependency/configuration changes. Compare with the approved
# tooling snapshot; the Git-tree gate supplies exact, ordinary config files first.
# Attest an exact PR checkout before any command executes its Lake configuration.
#
# Usage:
#   attest-pr-config.sh <merge-base-dir> <candidate-dir> <head-sha> \
#     <event-name> <merge-base-exact:0|1> <pins-changed:0|1>
#
# The lakefiles and both pins must match the approved tooling snapshot byte-for-byte.
# The Git-tree gate already checked modes, paths, and exact revisions. The retained
# upstream argument names/interface are also exercised by the adapted regression tests.
# There is no dependency-bump exception in this adaptation.
set -euo pipefail

MERGE_BASE="${1:?merge-base directory is required}"
CANDIDATE="${2:?candidate directory is required}"
EXPECTED_SHA="${3:?expected head SHA is required}"
EVENT_NAME="${4:?event name is required}"
MERGEBASE_EXACT="${5:-0}"
PINS_CHANGED="${6:-0}"

fail() {
  echo "::error::config-attestation: $*" >&2
  exit 1
}

case "$EXPECTED_SHA" in
  ''|*[!0-9a-f]*) fail "expected head is not a lowercase hexadecimal object ID" ;;
esac
[ "${#EXPECTED_SHA}" = 40 ] || fail "expected head is not a 40-character object ID"
[ "$EVENT_NAME" = "pull_request_target" ] || fail "unsupported attestation event"
[ "$MERGEBASE_EXACT" = "1" ] \
  || fail "the approved snapshot was not resolved exactly"
case "$PINS_CHANGED" in
  0) ;;
  *) fail "pin changes require human review; I03 has no dependency-bump exception" ;;
esac

GOT="$(git -C "$CANDIDATE" rev-parse HEAD 2>/dev/null)" \
  || fail "candidate is not a readable Git checkout"
[ "$GOT" = "$EXPECTED_SHA" ] \
  || fail "candidate resolved to $GOT instead of immutable event head $EXPECTED_SHA"

ordinary_file() {
  [ -f "$1" ] && [ ! -L "$1" ]
}

# Lake accepts either spelling. Preserve both presence and bytes from the approved snapshot so a
# candidate cannot switch which configuration Lake loads.
for FILE in lakefile.toml lakefile.lean; do
  MB="$MERGE_BASE/$FILE"
  HEAD="$CANDIDATE/$FILE"
  if [ -e "$MB" ] || [ -L "$MB" ]; then
    ordinary_file "$MB" || fail "$FILE is not an ordinary file at the merge base"
    ordinary_file "$HEAD" || fail "$FILE is missing or not an ordinary file at the candidate head"
    cmp -s "$MB" "$HEAD" || fail "$FILE differs from the approved snapshot"
  elif [ -e "$HEAD" ] || [ -L "$HEAD" ]; then
    fail "$FILE was introduced by the candidate"
  fi
done
ordinary_file "$CANDIDATE/lakefile.toml" \
  || fail "this repository requires an ordinary lakefile.toml"

LOCAL_PIN_DELTA=0
for FILE in lake-manifest.json lean-toolchain; do
  ordinary_file "$MERGE_BASE/$FILE" || fail "$FILE is not an ordinary approved pin"
  ordinary_file "$CANDIDATE/$FILE" || fail "$FILE is not an ordinary candidate pin"
  cmp -s "$MERGE_BASE/$FILE" "$CANDIDATE/$FILE" || LOCAL_PIN_DELTA=1
done
[ "$LOCAL_PIN_DELTA" = "$PINS_CHANGED" ] \
  || fail "the local pin delta disagrees with the immutable GitHub tree check"

echo "config-attestation: exact candidate config is safe to validate/build"
