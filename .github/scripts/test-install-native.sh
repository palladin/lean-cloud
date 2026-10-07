#!/usr/bin/env bash
set -euo pipefail

# Exercise timeout/recovery paths without network access or changing packages.
installer=$(cd "$(dirname "$0")" && pwd)/install-native.sh
fixture=$(mktemp -d)
trap 'rm -rf "$fixture"' EXIT
mkdir "$fixture/bin"

cat > "$fixture/bin/dpkg-query" <<'EOF'
#!/usr/bin/env bash
if [[ ${!#} == present || -f "$CASE_DIR/installed" ]]; then
  printf 'install ok installed'
else
  exit 1
fi
EOF
cat > "$fixture/bin/dpkg" <<'EOF'
#!/usr/bin/env bash
echo amd64
EOF
cat > "$fixture/bin/sudo" <<'EOF'
#!/usr/bin/env bash
exec "$@"
EOF
cat > "$fixture/bin/timeout" <<'EOF'
#!/usr/bin/env bash
[[ $1 == --kill-after=5s ]] || exit 99
case "$2" in 30s|45s|60s|120s) ;; *) exit 99 ;; esac
shift 2
exec "$@"
EOF
cat > "$fixture/bin/apt-get" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
[[ $DEBIAN_FRONTEND == noninteractive && $NEEDRESTART_MODE == l ]] || exit 98
printf '%s\n' "$*" >> "$CASE_DIR/calls"
case " $* " in
  *' --download-only '*)
    count=0
    if [[ -f "$CASE_DIR/downloads" ]]; then read -r count < "$CASE_DIR/downloads"; fi
    echo "$((count + 1))" > "$CASE_DIR/downloads"
    if (( count == 0 )) && [[ $SCENARIO == stale ]]; then exit 100; fi
    if [[ $SCENARIO == timeout || $SCENARIO == refresh-failure || $SCENARIO == download-failure ]]; then
      if (( count == 0 )); then exit 124; fi
      if [[ $SCENARIO == download-failure ]]; then exit 100; fi
    fi
    ;;
  *' update '*)
    if [[ $SCENARIO == refresh-failure ]]; then exit 100; fi
    ;;
  *' --no-download '*)
    if [[ $SCENARIO == install-failure ]]; then exit 42; fi
    if [[ $SCENARIO != incomplete ]]; then touch "$CASE_DIR/installed"; fi
    ;;
  *) exit 97 ;;
esac
EOF
chmod +x "$fixture/bin/"*

for scenario in installed direct stale timeout refresh-failure download-failure install-failure incomplete; do
  case_dir=$fixture/$scenario
  mkdir "$case_dir"
  packages=(present needed)
  expected=0
  case "$scenario" in
    installed) packages=(present) ;;
    refresh-failure|download-failure) expected=100 ;;
    install-failure) expected=42 ;;
    incomplete) expected=1 ;;
  esac
  status=0
  PATH="$fixture/bin:$PATH" CASE_DIR="$case_dir" SCENARIO="$scenario" \
    bash "$installer" "${packages[@]}" > "$case_dir/output" 2>&1 || status=$?
  if [[ $status != "$expected" ]]; then
    cat "$case_dir/output"
    echo "$scenario: expected exit $expected, got $status" >&2
    exit 1
  fi
  case "$scenario" in
    installed) [[ ! -f "$case_dir/calls" ]] ;;
    direct)
      [[ $(wc -l < "$case_dir/calls") == 2 ]]
      ! grep -q ' update ' "$case_dir/calls"
      grep -q -- '--no-download' "$case_dir/calls"
      ;;
    stale|timeout)
      [[ $(wc -l < "$case_dir/calls") == 4 ]]
      grep -q ' update --error-on=any' "$case_dir/calls"
      grep -q -- '--no-download' "$case_dir/calls"
      ;;
    refresh-failure|download-failure)
      ! grep -q -- '--no-download' "$case_dir/calls"
      ;;
    install-failure|incomplete)
      [[ $(wc -l < "$case_dir/calls") == 2 ]]
      ;;
  esac
  if [[ -f "$case_dir/calls" ]]; then
    ! grep -q ' present' "$case_dir/calls"
  fi
  echo "Native installer: $scenario passed"
done
