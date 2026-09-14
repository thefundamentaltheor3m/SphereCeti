#!/usr/bin/env bash
# Adapted from TauCetiProject/TauCeti@b743b607ce3e9742b18026ad79082e5d15badff5,
# .github/workflows/pr-build.yml (Apache-2.0; TauCeti contributors).
# Run from T: pin the bootstrap executable as well as lean-toolchain, never elan/master.
set -euo pipefail
case "${1:-}" in
  ''|--toolchain-only) ;;
  *) echo 'usage: install_lean.sh [--toolchain-only]' >&2; exit 2 ;;
esac
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cd "$script_dir/.."
mapfile -t pin < <(python3 -I -c 'import json,sys; p=json.load(open(sys.argv[1])); print(p["version"]); print(p["archive_sha256"])' tools/ci/elan.json)
[ "${#pin[@]}" = 2 ]
download=$(mktemp -d)
trap 'rm -rf "$download"' EXIT
curl --fail --location --silent --show-error --connect-timeout 15 --max-time 120 --retry 2 \
  "https://github.com/leanprover/elan/releases/download/${pin[0]}/elan-x86_64-unknown-linux-gnu.tar.gz" \
  -o "$download/elan.tar.gz"
printf '%s  %s\n' "${pin[1]}" "$download/elan.tar.gz" | sha256sum -c -
tar -xzf "$download/elan.tar.gz" -C "$download" elan-init
"$download/elan-init" -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
elan toolchain install "$(cat lean-toolchain)"
lean --version
if [ "${1:-}" != --toolchain-only ]; then
  lake exe cache get
fi
