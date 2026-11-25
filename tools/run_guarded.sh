#!/bin/bash
# Run a command with a memory and wall-clock ceiling, killing its whole process tree if
# either is exceeded. Exists because on 2026-11-25 an unbounded branch-and-bound loop in
# six orphaned debug runs used ~205 GB on a 36 GB machine and caused a kernel panic.
# macOS does not enforce RLIMIT_AS, so the ceiling is enforced by polling.
#
# Usage: tools/run_guarded.sh [-m MAX_MB] [-t MAX_SECONDS] -- command [args...]
# Defaults: 4096 MB, 600 s. Exit status is the command's, or 137 if the guard killed it.
set -u
max_mb=4096
max_s=600
while [ $# -gt 0 ]; do
  case "$1" in
    -m) max_mb=$2; shift 2 ;;
    -t) max_s=$2; shift 2 ;;
    --) shift; break ;;
    *) break ;;
  esac
done
[ $# -gt 0 ] || { echo "usage: $0 [-m MB] [-t S] -- command..." >&2; exit 2; }

"$@" &
pid=$!

tree() {  # the pid and all of its descendants
  local p=$1
  echo "$p"
  for c in $(pgrep -P "$p" 2>/dev/null); do tree "$c"; done
}

kill_tree() {
  local pids
  pids=$(tree "$pid")
  kill -9 $pids 2>/dev/null
}
trap 'kill_tree; exit 130' INT TERM

start=$(date +%s)
while kill -0 "$pid" 2>/dev/null; do
  rss_kb=0
  for p in $(tree "$pid"); do
    r=$(ps -o rss= -p "$p" 2>/dev/null | tr -d ' ')
    rss_kb=$((rss_kb + ${r:-0}))
  done
  elapsed=$(( $(date +%s) - start ))
  if [ "$rss_kb" -gt $((max_mb * 1024)) ]; then
    echo "run_guarded: killed after ${elapsed}s, resident $((rss_kb / 1024)) MB > ${max_mb} MB" >&2
    kill_tree; wait "$pid" 2>/dev/null; exit 137
  fi
  if [ "$elapsed" -gt "$max_s" ]; then
    echo "run_guarded: killed after ${elapsed}s > ${max_s}s, resident $((rss_kb / 1024)) MB" >&2
    kill_tree; wait "$pid" 2>/dev/null; exit 137
  fi
  sleep 0.2
done
wait "$pid"
