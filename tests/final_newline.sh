#!/bin/sh
# Decision D4: a document's final newline is kept, wherever the cursor goes,
# while extra empty lines at the end are still tidied away.
# Run from the repository root after `lake build`:  sh tests/final_newline.sh
set -e
Z=.lake/build/bin/zeditor
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
fail=0
run() {  # run NAME START-TEXT KEYS EXPECTED-TEXT
  printf "$2" > "$T/f.txt"; printf "$3" > "$T/k"
  $Z --keys "$T/k" "$T/f.txt" > /dev/null
  printf "$4" > "$T/expect"
  if cmp -s "$T/expect" "$T/f.txt"; then echo "PASS  $1"
  else echo "FAIL  $1"; od -c "$T/f.txt" | sed 's/^/    got: /'; fail=1; fi
}
run "final newline kept after a key"            'abc\n'        'Right\nSave\n'        'abc\n'
run "final newline kept, cursor above the end"  'abc\ndef\n'   'Right\nSave\n'        'abc\ndef\n'
run "extra empty lines at the end are tidied"   'abc\n\n\n'    'Right\nSave\n'        'abc\n'
run "a file without a final newline is left so" 'abc'          'Right\nSave\n'        'abc'
exit $fail
