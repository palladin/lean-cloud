#!/usr/bin/env bash
set -euo pipefail

# Hosted runners already provide most of these packages. Do not refresh every
# configured repository (including unrelated third-party feeds) on every job.
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
options=(-o Acquire::Retries=2 -o Acquire::http::Timeout=20
  -o Acquire::https::Timeout=20 -o DPkg::Lock::Timeout=30)
if [[ -f /etc/apt/sources.list.d/ubuntu.sources ]]; then
  options+=(-o Dir::Etc::sourcelist=/etc/apt/sources.list.d/ubuntu.sources
    -o Dir::Etc::sourceparts=-)
fi
sudo env DEBIAN_FRONTEND=noninteractive timeout --kill-after=10s 90s \
  apt-get "${options[@]}" update --error-on=any
sudo env DEBIAN_FRONTEND=noninteractive timeout --kill-after=10s 120s \
  apt-get "${options[@]}" install -y --no-install-recommends "${missing[@]}"
