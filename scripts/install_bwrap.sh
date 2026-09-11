#!/usr/bin/env bash
# Adapted from TauCetiProject/TauCeti@b743b607ce3e9742b18026ad79082e5d15badff5,
# .github/workflows/pr-build.yml (Apache-2.0; TauCeti contributors).
# Run only from the approved checkout. This installs the exact Ubuntu noble package.
set -euo pipefail
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
mapfile -t pin < <(python3 -I -c 'import json,sys; p=json.load(open(sys.argv[1])); print(p["version"]); print(p["deb_sha256"]); print(p["binary_sha256"])' "$script_dir/../tools/ci/bubblewrap.json")
[ "${#pin[@]}" = 3 ]
download=$(mktemp -d)
trap 'rm -rf "$download"' EXIT
deb="bubblewrap_${pin[0]}_amd64.deb"
downloaded=0
for mirror in archive.ubuntu.com security.ubuntu.com; do
  if curl --fail --location --silent --show-error --connect-timeout 15 --max-time 60 \
      "https://$mirror/ubuntu/pool/main/b/bubblewrap/$deb" -o "$download/bwrap.deb"; then
    downloaded=1
    break
  fi
done
# Hosted Ubuntu runners may route APT through a local mirror while public TLS endpoints
# are unavailable. APT still requests the exact version; the hard-coded digest below
# authenticates the bytes independently of the mirror and transport.
if [ "$downloaded" != 1 ]; then
  if (cd "$download" && timeout 120 apt-get -o Acquire::Retries=1 -o Acquire::http::Timeout=30 \
      -o Acquire::https::Timeout=30 download "bubblewrap=${pin[0]}"); then
    mv "$download/$deb" "$download/bwrap.deb"
    downloaded=1
  fi
fi
[ "$downloaded" = 1 ] || { echo 'Pinned bubblewrap unavailable; refusing candidate execution' >&2; exit 1; }
printf '%s  %s\n' "${pin[1]}" "$download/bwrap.deb" | sha256sum -c -
sudo dpkg -i "$download/bwrap.deb"
printf '%s  /usr/bin/bwrap\n' "${pin[2]}" | sha256sum -c -
# Grant user namespaces to this binary, not every process on the runner.
printf '%s\n' 'abi <abi/4.0>,' 'include <tunables/global>' \
  'profile bwrap /usr/bin/bwrap flags=(unconfined) {' '  userns,' \
  '  include if exists <local/bwrap>' '}' | sudo tee /etc/apparmor.d/bwrap
sudo apparmor_parser -r /etc/apparmor.d/bwrap
