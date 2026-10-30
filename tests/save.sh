#!/bin/sh
# Test that Save writes exactly the document's text, and nothing else.
# Run from the repository root after `lake build`:  sh tests/save.sh
set -e
Z=.lake/build/bin/zeditor
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
fail=0
check() {  # check NAME EXPECTED-FILE ACTUAL-FILE
  if cmp -s "$2" "$3"; then echo "PASS  $1"
  else echo "FAIL  $1"; echo "  expected:"; od -c "$2" | sed 's/^/    /'
       echo "  got:"; od -c "$3" | sed 's/^/    /'; fail=1; fi
}

# 1. A new file: type two lines, save. The file holds just those two lines.
printf 'type hello\nEnter\ntype world\nSave\n' > "$T/keys"
$Z --keys "$T/keys" "$T/new.txt" > /dev/null
printf 'hello\nworld' > "$T/expect"
check "new file holds only the typed text" "$T/expect" "$T/new.txt"

# 2. An existing file: open it, add a word at the start, save.
#    The file holds the old text with the change, not the old text twice.
printf 'first line\nsecond line' > "$T/old.txt"
printf 'type new \nSave\n' > "$T/keys"
$Z --keys "$T/keys" "$T/old.txt" > /dev/null
printf 'new first line\nsecond line' > "$T/expect"
check "existing file holds only the edited text" "$T/expect" "$T/old.txt"

# 3. No Save key: the file is not touched.
printf 'unchanged' > "$T/keep.txt"
printf 'type xyz\n' > "$T/keys"
$Z --keys "$T/keys" "$T/keep.txt" > /dev/null
printf 'unchanged' > "$T/expect"
check "without Save the file is unchanged" "$T/expect" "$T/keep.txt"

exit $fail
