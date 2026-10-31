#!/bin/sh
# Tab inserts spaces to the next tab stop, every 8 columns, as the C's
# `tabstop` (the specification allows any positive number of spaces).
# Run from the repository root after `lake build`:  sh tests/tab.sh
set -e
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
fail=0
for ed in zeditor zeditor2026; do
  printf '' > "$T/f.txt"; printf 'type a\nTab\ntype b\nTab\nTab\ntype c\nSave\n' > "$T/k"
  .lake/build/bin/$ed --keys "$T/k" "$T/f.txt" > /dev/null
  printf 'a       b               c' > "$T/expect"
  if cmp -s "$T/expect" "$T/f.txt"; then echo "PASS  $ed: tab stops every 8 columns"
  else echo "FAIL  $ed: got [$(cat "$T/f.txt")]"; fail=1; fi
done
exit $fail
