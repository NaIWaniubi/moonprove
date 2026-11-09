#!/usr/bin/env bash
# Run the verifier over examples/ and compare with each file's EXPECT line.
#
# The EXPECT line states how many obligations the file has, how many must be
# proven, and how many must be violated. It is written by hand from what the code
# means, so this catches a tool that starts proving things it should not.
set -uo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.moon/bin:$PATH"

bin=_build/native/release/build/cmd/main/main.exe
if [ ! -x "$bin" ]; then
  echo "corpus: build the CLI first: ./dev.sh build --target native --release cmd/main" >&2
  exit 2
fi

fail=0
count=0
for f in examples/*.mbt; do
  expected="$(sed -n 's#^// EXPECT proven=\([0-9]*\) violated=\([0-9]*\) undecided=\([0-9]*\)$#\1 \2 \3#p' "$f" | head -1)"
  if [ -z "$expected" ]; then
    echo "SKIP $f (no EXPECT line)"
    continue
  fi
  read -r want_p want_v want_u <<< "$expected"
  out="$("$bin" verify "$f" 2>&1)"
  line="$(printf '%s\n' "$out" | grep -E '^[0-9]+ obligation' | tail -1)"
  got_p="$(printf '%s' "$line" | sed -n 's/.*: \([0-9]*\) proven.*/\1/p')"
  got_v="$(printf '%s' "$line" | sed -n 's/.*, \([0-9]*\) violated.*/\1/p')"
  got_u="$(printf '%s' "$line" | sed -n 's/.*, \([0-9]*\) undecided.*/\1/p')"
  count=$((count + 1))
  if [ "$got_p" != "$want_p" ] || [ "$got_v" != "$want_v" ] || [ "$got_u" != "$want_u" ]; then
    echo "FAIL $f: want proven=$want_p violated=$want_v undecided=$want_u, got proven=$got_p violated=$got_v undecided=$got_u"
    fail=1
  else
    echo "ok   $f: proven=$got_p violated=$got_v undecided=$got_u"
  fi
done

if [ "$fail" -ne 0 ]; then
  echo
  echo "corpus check FAILED"
  exit 1
fi
echo "corpus ok: $count example(s) match their expected verdicts"
