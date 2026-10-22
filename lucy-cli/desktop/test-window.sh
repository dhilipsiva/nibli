#!/usr/bin/env bash
# Real GTK smoke test. All data, configuration and service sockets are isolated.
set -euo pipefail
binary="$(realpath "${1:-target/release/lucy}")"
fixture="$(mktemp -d)"
trap 'rm -rf -- "$fixture"' EXIT
mkdir -m700 "$fixture/runtime" "$fixture/config" "$fixture/workspace"
export XDG_RUNTIME_DIR="$fixture/runtime"
export XDG_CONFIG_HOME="$fixture/config"
export XDG_DATA_DIRS="$fixture/empty-share"
export XDG_CURRENT_DESKTOP=lucy-test
export GIO_USE_VFS=local
export GSETTINGS_BACKEND=memory
export GTK_A11Y=none
export GTK_USE_PORTAL=0
export LUCY_DATA_DIR="$fixture/data"
export LUCY_TEST_BINARY="$binary"
export LUCY_TEST_FIXTURE="$fixture"
export GDK_BACKEND=x11
export GSK_RENDERER=cairo
cat > "$fixture/session.conf" <<'BUS'
<busconfig>
  <type>session</type>
  <listen>unix:tmpdir=/tmp</listen>
  <auth>EXTERNAL</auth>
  <policy context="default">
    <allow send_destination="*" eavesdrop="true"/>
    <allow eavesdrop="true"/>
    <allow own="*"/>
  </policy>
</busconfig>
BUS
dbus-run-session --config-file="$fixture/session.conf" -- xvfb-run -a bash -euo pipefail <<'TEST'
service_pid=
ui_pid=
cleanup() {
    test -z "$ui_pid" || kill "$ui_pid" 2>/dev/null || true
    test -z "$service_pid" || kill "$service_pid" 2>/dev/null || true
    wait 2>/dev/null || true
}
trap cleanup EXIT
"$LUCY_TEST_BINARY" serve >"$LUCY_TEST_FIXTURE/service.log" 2>&1 &
service_pid=$!
for attempt in $(seq 1 100); do
    test ! -S "$XDG_RUNTIME_DIR/lucy/service.sock" || break
    sleep 0.05
done
"$LUCY_TEST_BINARY" ui --workspace "$LUCY_TEST_FIXTURE/workspace" >"$LUCY_TEST_FIXTURE/ui.log" 2>&1 &
ui_pid=$!
window=
for attempt in $(seq 1 100); do
    window="$(xdotool search --onlyvisible --name '^Ask Lucy$' 2>/dev/null || true)"
    test -z "$window" || break
    kill -0 "$ui_pid" 2>/dev/null || { cat "$LUCY_TEST_FIXTURE/ui.log"; exit 1; }
    sleep 0.1
done
test -n "$window"
sleep 0.2
kill -0 "$ui_pid"
test ! -e "$LUCY_DATA_DIR"
if test -n "${LUCY_TEST_SCREENSHOT:-}"; then
    magick import -window "$window" "$LUCY_TEST_SCREENSHOT"
fi
printf '%s\n' 'Rust GTK window opened without memory loading or inference.'
TEST
