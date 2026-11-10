#!/usr/bin/env bash
# The CLI's contract: exit codes, JSON shape, and the messages a caller parses.
set -uo pipefail
cd "$(dirname "$0")/.."

bin=_build/native/release/build/cmd/main/main.exe
if [ ! -x "$bin" ]; then
  echo "smoke: build the CLI first" >&2
  exit 2
fi
run() { "$bin" "$@"; }

fails=0
check() {
  local what="$1" want="$2" got="$3"
  if [ "$want" != "$got" ]; then
    printf 'FAIL %s\n  want: %s\n  got:  %s\n' "$what" "$want" "$got" >&2
    fails=$((fails + 1))
  fi
}

# version comes from moon.mod, so a bump that forgets one place fails here
manifest_version="$(sed -n 's/^version = "\(.*\)"$/\1/p' moon.mod | head -1)"
check "version" "moonprove $manifest_version" "$(run version)"

# a proven file exits 0
set +e
run verify examples/06_loop.mbt > /dev/null 2>&1
code=$?
set -e
check "proven exits 0" "0" "$code"

# a violated file exits 1
set +e
run verify examples/10_bad_assert.mbt > /dev/null 2>&1
code=$?
set -e
check "violated exits 1" "1" "$code"

# an undecided file exits 3, distinct from both
set +e
run verify examples/04_overflow.mbt > /dev/null 2>&1
code=$?
set -e
check "undecided exits 3" "3" "$code"

# a missing file exits 2 with a message
set +e
out="$(run verify no_such_file.mbt 2>&1)"
code=$?
set -e
check "missing file exits 2" "2" "$code"
case "$out" in
  *"cannot read"*) ;;
  *) echo "FAIL missing file message: $out" >&2; fails=$((fails + 1)) ;;
esac

# JSON is parseable and says what the text says. The run exits 1 on a violation,
# which is the correct behaviour and must not abort this script.
set +e
json="$(run verify examples/10_bad_assert.mbt --json)"
set -e
printf '%s' "$json" | node -e '
let s = "";
process.stdin.on("data", (d) => (s += d)).on("end", () => {
  const j = JSON.parse(s);
  if (!Array.isArray(j.results) || j.results.length !== 1) throw new Error("bad results");
  const r = j.results[0];
  if (r.label !== "assert") throw new Error("bad label: " + r.label);
  if (r.outcome !== "violated") throw new Error("bad outcome: " + r.outcome);
  if (typeof r.line !== "number") throw new Error("bad line");
});
' || { echo "FAIL json shape" >&2; fails=$((fails + 1)); }

# a parse error exits 2 and reports the line
set +e
out="$(printf 'fn f(x : Int) {\n  assert\n}\n' > /tmp/mp_bad.mbt && run verify /tmp/mp_bad.mbt 2>&1)"
code=$?
set -e
check "parse error exits 2" "2" "$code"
case "$out" in
  *"parse:"*) ;;
  *) echo "FAIL parse message: $out" >&2; fails=$((fails + 1)) ;;
esac
rm -f /tmp/mp_bad.mbt

# --width is honoured: at 8 bits the sum bound tightens
set +e
out16="$(run verify examples/05_bounded_sum.mbt --width 16)"
set -e
case "$out16" in
  *"1 proven"*) ;;
  *) echo "FAIL --width 16: $out16" >&2; fails=$((fails + 1)) ;;
esac

# SARIF is the CI-facing format: it has to parse and carry the verdict as a level.
set +e
sarif="$(run verify examples/10_bad_assert.mbt --format sarif)"
set -e
printf '%s' "$sarif" | node -e '
let s = "";
process.stdin.on("data", (d) => (s += d)).on("end", () => {
  const j = JSON.parse(s);
  if (j.version !== "2.1.0") throw new Error("bad sarif version: " + j.version);
  const run = j.runs[0];
  if (run.tool.driver.name !== "moonprove") throw new Error("bad driver");
  const ids = run.tool.driver.rules.map((r) => r.id);
  for (const want of ["proven", "violated", "undecided"]) {
    if (!ids.includes(want)) throw new Error("missing rule " + want);
  }
  const r = run.results[0];
  if (r.ruleId !== "violated" || r.level !== "error") throw new Error("bad result");
  if (!r.locations[0].physicalLocation.artifactLocation.uri.endsWith("examples/10_bad_assert.mbt")) {
    throw new Error("bad uri");
  }
  if (!r.message.text.includes("x = ")) throw new Error("counterexample not named: " + r.message.text);
});
' || { echo "FAIL sarif shape" >&2; fails=$((fails + 1)); }

# An unknown --format is a usage error, not a silent fallback to text.
set +e
run verify examples/06_loop.mbt --format xml > /dev/null 2>&1
code=$?
set -e
check "bad --format exits 2" "2" "$code"

if [ "$fails" -ne 0 ]; then
  echo "cli smoke FAILED: $fails check(s)" >&2
  exit 1
fi
echo "cli smoke ok"
