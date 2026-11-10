# Changelog

## 0.2.0 — 2026-11-10

- **SARIF 2.1.0 output** (`--format sarif`, or `--json` for the plain shape). A
  verifier a CI cannot read is a verifier nobody runs twice: `violated` maps to
  `error`, `undecided` to `warning`, and proven obligations are emitted at `none`
  so a reviewer sees what was checked, not only what failed. Counterexamples are
  rendered with the variable's own name (`x = -1073741824`, not `v1 = ...`).
- `--format` rejects an unknown value with exit 2 instead of falling back to text.
- Seven tests pin the SARIF shape (version, driver, rule ids, level per verdict,
  location line, named counterexample, escaping); the CLI smoke parses a real
  document and checks the same fields.
- Removed the empty `src/rules` directory left over from the skeleton.

## 0.1.1 — 2026-11-10

- Dropped `moonbitlang/parser` from the module's dependencies. The surface
  language has its own lexer and parser by design — it is a subset with contracts
  added, and a general parser would accept far more than the verifier can reason
  about — so nothing imported the dependency. Declaring one it never uses is what
  a licence review flags first.
- `README.md` gained a section mapping the project onto the hackathon's six
  acceptance criteria, including where it falls short of the suggested 10,000
  effective lines and why.

No behaviour change; all 47 tests, the corpus check and the CLI smoke still pass.

## 0.1.0 — 2026-11-09

First release. A bounded verifier for MoonBit-style code: every contract and
assertion gets one of three verdicts — proven, violated with a counterexample, or
undecided with a reason.

- `src/solver`: a sort-aware simplifier, interval refutation, Fourier–Motzkin
  elimination and boundary search. `Unsat` only ever comes from the first three;
  `Sat` only ever from a checked model.
- `src/symir`: lexer and recursive-descent parser for the surface language, with
  the full precedence cascade and contract syntax.
- `src/explore`: path-sensitive symbolic execution; loops verified by induction
  rather than unrolled, so an unbounded loop can be proven.
- `src/verify`: the driver both entry points share.
- `cmd/main`: `verify`, `explain`, `dump`, with exit codes 0/1/2/3.
- `src/web` + `web/index.html`: a single-file playground running the same MoonBit
  compiled to wasm.
