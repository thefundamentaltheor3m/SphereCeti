#!/usr/bin/env bash
# Public TauCeti Lake cache; failures fall back to source compilation.
set -euo pipefail
config="$RUNNER_TEMP/tauceti-lake-cache.toml"
cache_dir="$(pwd)/.lake/cache"
cat > "$config" <<TOML
cache.defaultService = "tauceti-public"
[[cache.service]]
name = "tauceti-public"
kind = "s3"
artifactEndpoint = "https://cache.taucetiproject.org/artifacts"
revisionEndpoint = "https://cache.taucetiproject.org/revisions"
TOML

discard_cache() {
  [ -e "$cache_dir" ] || return 0
  stale="$cache_dir.discard.$$"
  if mv "$cache_dir" "$stale" 2>/dev/null; then
    rm -rf "$stale" 2>/dev/null || true
  else
    rm -rf "$cache_dir" 2>/dev/null || true
  fi
}

clean=0
attempts=3
for attempt in $(seq 1 "$attempts"); do
  discard_cache
  log="$RUNNER_TEMP/tauceti-cache-get-$attempt.log"
  rc=0
  LAKE_CONFIG="$config" LAKE_CACHE_DIR="$cache_dir" \
      lake cache get --package=TauCeti --service=tauceti-public \
        --repo=TauCetiProject/TauCeti --mappings-only --max-revs=20 \
        > "$log" 2>&1 || rc=$?
  cat "$log"

  if [ "$rc" = 0 ]; then
    clean=1
    break
  fi
  if grep -q 'no outputs found' "$log"; then
    break
  fi
  if [ "$attempt" != "$attempts" ]; then
    echo "::notice::Tau Ceti cache-map fetch attempt $attempt failed; retrying from an empty cache"
    sleep 2
  fi
done

if [ "$clean" = 1 ]; then
  echo "enabled=1" >> "$GITHUB_OUTPUT"
  {
    echo "LAKE_CONFIG=$config"
    echo "LAKE_CACHE_DIR=$cache_dir"
  } >> "$GITHUB_ENV"
else
  echo "::warning::Tau Ceti cache map unavailable; building from source"
  discard_cache
  echo "enabled=0" >> "$GITHUB_OUTPUT"
fi
