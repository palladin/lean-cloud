#!/usr/bin/env bash
set -euo pipefail

# Hosted runners already provide most packages and populated package indexes.
# Try those first; a stale index or stalled runner mirror gets one fallback.
missing=()
for package in "$@"; do
  status=$(dpkg-query -W -f='${Status}' "$package" 2>/dev/null || true)
  if [[ "$status" != 'install ok installed' ]]; then
    missing+=("$package")
  fi
done
if [[ ${#missing[@]} == 0 ]]; then
  echo 'Native build dependencies are already installed.'
  exit 0
fi

echo "Installing missing native dependencies: ${missing[*]}"
root=()
if (( EUID != 0 )); then root=(sudo); fi
options=(-o Acquire::Retries=1 -o Acquire::http::Timeout=15
  -o Acquire::https::Timeout=15 -o DPkg::Lock::Timeout=15
  -o Acquire::Languages=none -o Dpkg::Use-Pty=0)
if [[ -f /etc/apt/sources.list.d/ubuntu.sources ]]; then
  options+=(-o Dir::Etc::sourcelist=/etc/apt/sources.list.d/ubuntu.sources
    -o Dir::Etc::sourceparts=-)
fi

run_apt() {
  local stage=$1 limit=$2 status started=$SECONDS
  shift 2
  echo "Native dependencies: $stage (limit $limit)"
  if "${root[@]}" env DEBIAN_FRONTEND=noninteractive NEEDRESTART_MODE=l \
      timeout --kill-after=5s "$limit" apt-get "${options[@]}" "$@"; then
    echo "Native dependencies: $stage completed in $((SECONDS - started))s."
    return 0
  else
    status=$?
    echo "::warning::Native dependencies: $stage failed (exit $status; 124 means timeout)." >&2
    return "$status"
  fi
}

# Retry only downloads, before dpkg can change anything. Once every archive is
# present, installation is offline and cannot stall on a package download.
install=(install -y --no-install-recommends --no-remove "${missing[@]}")
if ! run_apt 'download from runner indexes' 30s "${install[@]}" --download-only; then
  echo 'Retrying with fresh indexes from the official Ubuntu archive.'
  # Use private sources/indexes: never rewrite the runner repositories or trust
  # unsigned packages. Avoid refreshing unrelated third-party repositories.
  source /etc/os-release
  [[ "$ID" == ubuntu ]]
  archive=https://archive.ubuntu.com/ubuntu
  security=https://security.ubuntu.com/ubuntu
  if [[ $(dpkg --print-architecture) != amd64 ]]; then
    archive=https://ports.ubuntu.com/ubuntu-ports
    security=$archive
  fi
  apt_dir=$(mktemp -d)
  trap '"${root[@]}" rm -rf "$apt_dir"' EXIT
  chmod 755 "$apt_dir"
  cat > "$apt_dir/ubuntu.sources" <<EOF
Types: deb
URIs: $archive
Suites: $VERSION_CODENAME $VERSION_CODENAME-updates
Components: main universe
Signed-By: /usr/share/keyrings/ubuntu-archive-keyring.gpg

Types: deb
URIs: $security
Suites: $VERSION_CODENAME-security
Components: main universe
Signed-By: /usr/share/keyrings/ubuntu-archive-keyring.gpg
EOF
  options+=(-o "Dir::Etc::sourcelist=$apt_dir/ubuntu.sources"
    -o Dir::Etc::sourceparts=- -o "Dir::State::lists=$apt_dir/lists")
  mkdir -p "$apt_dir/lists/partial"
  run_apt 'refresh official Ubuntu indexes' 45s update --error-on=any
  run_apt 'download from official Ubuntu archive' 120s "${install[@]}" --download-only
fi
run_apt 'install downloaded packages' 60s "${install[@]}" --no-download

for package in "${missing[@]}"; do
  if [[ $(dpkg-query -W -f='${Status}' "$package" 2>/dev/null) != 'install ok installed' ]]; then
    echo "::error::Native dependency was not installed: $package" >&2
    exit 1
  fi
done
