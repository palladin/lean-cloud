#!/usr/bin/env bash
# Shared validation only; no login, installation, or implicit provisioning.
set -euo pipefail
umask 077
fail() { printf '%s\n' "$*" >&2; exit 1; }
need() { command -v "$1" >/dev/null || fail "Missing tool: $1. Install it before running this helper."; }
identifier() { [[ "$1" =~ ^[a-z][a-z0-9-]{0,62}$ ]] || fail 'Use a lowercase name beginning with a letter (max 63 characters).'; }
number() { [[ "$1" =~ ^(0|[1-9][0-9]{0,4})$ ]] || fail 'Expected a nonnegative integer (at most 5 digits, no leading zeroes).'; }
absolute_dir() { (cd "$1" && pwd -P); }
secret() { openssl rand -hex "${1:-32}"; }
# State directories may have any name. Protect them even outside this checkout.
private_dir() {
  [[ ! -e "$1/.git" ]] || fail 'Use a dedicated state directory, not a Git repository root.'
  chmod 700 "$1"
  if [[ ! -f "$1/.gitignore" ]] || ! grep -Fxq '*' "$1/.gitignore"; then
    printf '\n# Generated private deployment state.\n*\n' >> "$1/.gitignore"
  fi
}
# An interrupted operation leaves a lock for deliberate operator recovery.
lock_dir() {
  mkdir "$1/.operation" 2>/dev/null || fail "Operation locked: $1/.operation. Remove it only after verifying the previous operator has stopped."
  operation_lock="$1/.operation"
  trap 'rmdir "$operation_lock"' EXIT
}
