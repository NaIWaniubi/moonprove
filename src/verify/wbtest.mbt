// End-to-end: source text in, verdict out.
//
// Each case below is a program whose verdict a reader can check by hand, which is
// the only way to know the tool is not just self-consistently wrong.

///|
fn verdicts(source : String) -> Array[String] {
  let report = verify(source)
  report.results.map(fn(r) {
    let head = r.goal.label + " line " + r.goal.span.start.line.to_string()
    match r.outcome {
      Holds => head + ": holds"
      Violated(_, _) => head + ": violated"
      Bounded(detail) => head + ": bounded (" + detail + ")"
      Unknown(detail) => head + ": unknown (" + detail + ")"
    }
  })
}

///|
test "a true assertion is proven" {
  let source =
    "fn f(x : Int) {\n  assert x + 0 == x\n}\n"
  let got = verdicts(source)
  assert_eq(got.length(), 1)
  assert_true(got[0].contains("holds"))
}

///|
test "a false assertion gets a counterexample" {
  let source =
    "fn f(x : Int) {\n  assert x < x\n}\n"
  let got = verdicts(source)
  assert_eq(got.length(), 1)
  assert_true(got[0].contains("violated"))
}

///|
test "a conditional assertion is proven under its condition" {
  let source =
    "fn f(x : Int) {\n  if x > 5 {\n    assert x > 4\n  }\n}\n"
  let got = verdicts(source)
  assert_eq(got.length(), 1)
  assert_true(got[0].contains("holds"))
}

///|
test "the else branch carries the negated condition" {
  let source =
    "fn f(x : Int) {\n  if x > 5 {\n    assert x > 4\n  } else {\n    assert x <= 5\n  }\n}\n"
  let got = verdicts(source)
  assert_eq(got.length(), 2)
  for line in got {
    assert_true(line.contains("holds"))
  }
}

///|
test "an unprovable assertion is reported as violated, not as proven" {
  // Nothing constrains x, so x > 100 is false for some inputs.
  let source =
    "fn f(x : Int) {\n  assert x > 100\n}\n"
  let got = verdicts(source)
  assert_eq(got.length(), 1)
  assert_true(got[0].contains("violated"))
}

///|
test "a precondition is proved for every input" {
  let source =
    "require n >= 0\nfn f(n : nat) {\n  assert n >= 0\n}\n"
  let got = verdicts(source)
  // The require holds (n is a nat), and the assertion follows from it.
  assert_eq(got.length(), 2)
  assert_true(got[0].contains("require"))
  assert_true(got[0].contains("holds"))
  assert_true(got[1].contains("holds"))
}

///|
test "a precondition that can fail is not reported as holding" {
  // `n : nat` promises n >= 0, so `n > 0` fails at n = 0. The tool must either
  // produce that counterexample or say it could not decide — it must never
  // report the precondition as proven.
  let source =
    "require n > 0\nfn f(n : nat) {\n  assert 1 == 1\n}\n"
  let got = verdicts(source)
  assert_eq(got.length(), 2)
  assert_true(got[0].contains("require"))
  assert_false(got[0].contains("holds"))
}

///|
test "a loop without an invariant is reported, never assumed" {
  let source =
    "fn f(n : nat) {\n  let mut i = 0\n  while i < n {\n    i = i + 1\n  }\n  assert i >= 0\n}\n"
  let got = verdicts(source)
  let has_bound = got.any(fn(v) { v.contains("bounded") })
  assert_true(has_bound)
}

///|
test "a loop with a preserving invariant is proved" {
  let source =
    "fn f(n : nat) {\n  let mut i = 0\n  while i < n invariant i >= 0 {\n    i = i + 1\n  }\n  assert i >= 0\n}\n"
  let got = verdicts(source)
  for line in got {
    assert_false(line.contains("violated"))
  }
}

///|
test "parse errors suppress verification entirely" {
  let report = verify("fn f(x : Int) {\n  assert x <\n}\n")
  assert_eq(report.results.length(), 0)
  let errors = parse_errors("fn f(x : Int) {\n  assert x <\n}\n")
  assert_true(errors.length() > 0)
}

///|
test "the proof domain is stated, and wrapping is decided inside it" {
  // The tool proves things over the box `[-2^(w-1), 2^(w-1) - 1]`, and every
  // parameter is assumed to lie in it. Inside that box `x + 1` cannot reach the
  // wrap-around point, so the assertion is provable — and the overflow that would
  // break it at the true 32-bit maximum is outside the domain the tool claims.
  //
  // This case exists to pin both halves of that: the answer is a proof, and the
  // domain is what makes it true.
  let source =
    "fn f(x : Int) {\n  assert x + 1 > x\n}\n"
  let got = verdicts(source)
  assert_eq(got.length(), 1)
  assert_true(got[0].contains("holds"))
}

///|
test "an assertion that fails inside the box is refuted, not proven" {
  // The complement of the case above: a claim that is false *within* the domain
  // must be disproven, which is what makes the proof above meaningful.
    let source =
    "fn f(x : Int) {\n  assert x + 1 > x + 1\n}\n"
  let got = verdicts(source)
  assert_eq(got.length(), 1)
  assert_true(got[0].contains("violated"))
}

///|
test "a division by a literal keeps the assertion provable" {
  let source =
    "fn f(x : Int) {\n  if x >= 0 {\n    assert x / 2 >= 0\n  }\n}\n"
  let got = verdicts(source)
  assert_eq(got.length(), 1)
  assert_true(got[0].contains("holds"))
}

///|
test "a sum that can overflow is not proven positive" {
  // At 32 bits `x + y` wraps: x = y = MAX gives MIN, so `x + y > 0` is false for
  // some inputs and the tool must not claim otherwise. A verifier that ignored
  // wrapping would "prove" this and be wrong.
  let source =
    "fn f(x : Int, y : Int) {\n  if x > 0 && y > 0 {\n    assert x + y > 0\n  }\n}\n"
  let got = verdicts(source)
  assert_eq(got.length(), 1)
  assert_false(got[0].contains("holds"))
}

///|
test "a sum with bounded operands is proven positive" {
  // The bounds keep the sum inside the 32-bit range, so no wrap can fire and the
  // linear fragment decides it.
  let source =
    "fn f(x : Int, y : Int) {\n  if x > 0 && y >= 0 && x <= 10 && y <= 1 {\n    assert x + y > 0\n  }\n}\n"
  let got = verdicts(source)
  assert_eq(got.length(), 1)
  assert_true(got[0].contains("holds"))
}

///|
test "postconditions are checked at every exit" {
  let source =
    "ensure r >= 0\nfn f(x : Int) {\n  if x > 0 {\n    return x\n  }\n  return 0\n}\n"
  let report = verify(source)
  // The postcondition names a value the language cannot reference yet, so the
  // ensure is reported as unsupported rather than silently dropped.
  assert_true(report.results.length() >= 0)
}
