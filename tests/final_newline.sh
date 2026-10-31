#!/bin/sh
# Decision D4. The 1990 edition removes empty lines at the end of the document,
# including a file's final newline, as the C does (the specification allows it).
# The 2026 edition keeps the final newline, wherever the cursor goes.
# Run from the repository root after `lake build`:  sh tests/final_newline.sh
set -e
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
fail=0
run() {  # run EDITION-BINARY NAME START-TEXT KEYS EXPECTED-TEXT
  printf "$3" > "$T/f.txt"; printf "$4" > "$T/k"
  .lake/build/bin/$1 --keys "$T/k" "$T/f.txt" > /dev/null
  printf "$5" > "$T/expect"
  if cmp -s "$T/expect" "$T/f.txt"; then echo "PASS  $1: $2"
  else echo "FAIL  $1: $2"; od -c "$T/f.txt" | sed 's/^/    got: /'; fail=1; fi
}
run zeditor     "final newline removed after a key (as the C)"     'abc\n'      'Right\nSave\n' 'abc'
run zeditor     "final newline removed, cursor above the end"      'abc\ndef\n' 'Right\nSave\n' 'abc\ndef'
run zeditor     "all empty lines at the end removed"               'abc\n\n\n'  'Right\nSave\n' 'abc'
run zeditor2026 "final newline kept after a key"                   'abc\n'      'Right\nSave\n' 'abc\n'
run zeditor2026 "final newline kept, cursor above the end"         'abc\ndef\n' 'Right\nSave\n' 'abc\ndef\n'
run zeditor2026 "extra empty lines at the end are tidied"          'abc\n\n\n'  'Right\nSave\n' 'abc\n'
run zeditor2026 "a file without a final newline is left so"        'abc'        'Right\nSave\n' 'abc'
exit $fail
