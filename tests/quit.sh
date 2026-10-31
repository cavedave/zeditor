#!/bin/sh
# Quit. The 1990 edition does what the specification's Quit and the C do: if
# the document has changed, save it, then quit. The 2026 edition asks for Quit
# to be pressed twice when there are unsaved changes, and does not save.
# Run from the repository root after `lake build`:  sh tests/quit.sh
set -e
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
fail=0
run() {  # run EDITION-BINARY NAME KEYS EXPECTED-TEXT QUIT(yes|no)
  printf 'abc' > "$T/f.txt"; printf "$3" > "$T/k"
  out=$(.lake/build/bin/$1 --keys "$T/k" "$T/f.txt")
  case "$out" in *"(quit)"*) q=yes ;; *) q=no ;; esac
  printf "$4" > "$T/expect"
  if cmp -s "$T/expect" "$T/f.txt" && [ "$q" = "$5" ]; then echo "PASS  $1: $2"
  else echo "FAIL  $1: $2 (quit: $q; file: $(cat "$T/f.txt"))"; fail=1; fi
}
run zeditor     "quit with changes saves, then quits"        'type x\nQuit\n'       'xabc' yes
run zeditor     "quit without changes just quits"            'Quit\n'               'abc'  yes
run zeditor2026 "quit with changes asks first, saves nothing" 'type x\nQuit\n'      'abc'  no
run zeditor2026 "quit twice quits without saving"            'type x\nQuit\nQuit\n' 'abc'  yes
exit $fail
