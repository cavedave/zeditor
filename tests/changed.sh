#!/bin/sh
# Decision D6: the editor records whether the document has been edited since it
# was last read or saved, as the C's DocChanged does (the specification has no
# such record). Checked through the status line of the scripted mode.
# Run from the repository root after `lake build`:  sh tests/changed.sh
set -e
Z=.lake/build/bin/zeditor
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
fail=0
status() {  # status NAME START-TEXT KEYS  -> prints the status line
  printf "$2" > "$T/f.txt"; printf "$3" > "$T/k"
  $Z --keys "$T/k" "$T/f.txt" | tail -1
}
expect() {  # expect NAME START-TEXT KEYS yes|no
  s=$(status "$1" "$2" "$3")
  case "$s" in *"[modified]"*) got=yes ;; *) got=no ;; esac
  if [ "$got" = "$4" ]; then echo "PASS  $1"; else echo "FAIL  $1: $s"; fail=1; fi
}
expect "opening a file: not changed"                   'abc' ''                         no
expect "moving the cursor: not changed"                'abc' 'Right\nRight\n'           no
expect "typing: changed"                               'abc' 'type x\n'                 yes
expect "typing then deleting it: still changed (as C)" 'abc' 'type x\nBackspace\n'      yes
expect "saving clears it"                              'abc' 'type x\nSave\n'           no
expect "an edit after saving: changed again"           'abc' 'type x\nSave\ntype y\n'   yes
exit $fail
