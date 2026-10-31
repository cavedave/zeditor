#!/bin/sh
# Decision D5: the mark is a position in the text (as in the C). Each case is
# one of the findings the decision fixes, or one of its two sub-choices.
# Run from the repository root after `lake build`:  sh tests/mark.sh
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
L5='Left\nLeft\nLeft\nLeft\nLeft\n'; R5='Right\nRight\nRight\nRight\nRight\n'
run "cut then paste gives the text back (6a, C1)" \
    '' "type hello world\n${L5}Mark\n${R5}Cut\nPaste\nSave\n" 'hello world'
run "a mark at the top of the document works (6d)" \
    'abc' 'Mark\nRight\nRight\nRight\nCopy\nPaste\nSave\n' 'abcabc'
run "cut with the mark after the cursor (6b)" \
    'abcdef' 'Right\nRight\nRight\nMark\nLeft\nLeft\nLeft\nCut\nSave\n' 'def'
run "no doubt which side the mark is on: ab|ba (6e)" \
    'abba' 'Right\nMark\nRight\nCut\nSave\n' 'aba'
run "an edit clears the mark (sub-choice i, spec and C)" \
    'abc' 'Mark\nRight\ntype x\nCut\nSave\n' 'axbc'
run "a move keeps the mark on the same text (sub-choice ii, as the C)" \
    'a\ncdef' 'Down\nRight\nRight\nRight\nRight\nUp\nMark\nDown\nCopy\nPaste\nSave\n' 'a\ncdef\ncdef'
exit $fail
