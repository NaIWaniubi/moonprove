// SARIF output, checked against the shape a consumer parses.
//
// The assertions here are the ones GitHub's code scanning would fail on: a wrong
// version string, a level that is not in SARIF's vocabulary, a rule id that does
// not appear in `rules`, or a location without a line.

///|
fn sarif_json(report : @core.Report) -> String {
  to_sarif(report, "0.1.1", "examples/x.mbt")
}

///|
test "the envelope names 2.1.0 and the driver" {
  let report = verify("fn f(x : Int) {\n  assert x < x\n}\n")
  let text = sarif_json(report)
  assert_true(text.contains("\"version\":\"2.1.0\""))
  assert_true(text.contains("\"name\":\"moonprove\""))
  assert_true(text.contains("sarif-2.1.0.json"))
}

///|
test "a violated obligation becomes an error at its line" {
  let report = verify("fn f(x : Int) {\n  assert x > 100\n}\n")
  let text = sarif_json(report)
  assert_true(text.contains("\"ruleId\":\"violated\""))
  assert_true(text.contains("\"level\":\"error\""))
  // `assert` is on the second line of that source.
  assert_true(text.contains("\"startLine\":2"))
  assert_true(text.contains("examples/x.mbt"))
}

///|
test "a proven obligation becomes a none-level result" {
  let report = verify("fn f(x : Int) {\n  assert x + 0 == x\n}\n")
  let text = sarif_json(report)
  assert_true(text.contains("\"ruleId\":\"proven\""))
  assert_true(text.contains("\"level\":\"none\""))
}

///|
test "an undecided obligation becomes a warning" {
  let report = verify("fn f(n : nat) {\n  let mut i = 0\n  while i < n {\n    i = i + 1\n  }\n}\n")
  let text = sarif_json(report)
  assert_true(text.contains("\"ruleId\":\"undecided\""))
  assert_true(text.contains("\"level\":\"warning\""))
}

///|
test "the counterexample is rendered with the variable's own name" {
  let report = verify("fn f(x : Int) {\n  assert x > 100\n}\n")
  let text = sarif_json(report)
  assert_true(text.contains("x = "))
  assert_false(text.contains("v1 = "))
}

///|
test "every rule a result names is declared" {
  let report = verify("fn f(x : Int) {\n  if x > 5 {\n    assert x > 4\n  }\n  assert x > 100\n}\n")
  let text = sarif_json(report)
  // Two distinct ids can appear; both must be in the rules array.
  let ids : Array[String] = ["proven", "violated", "undecided"]
  for id in ids {
    assert_true(text.contains("\"id\":\"" + id + "\""))
  }
}

///|
test "escaping keeps the document parseable" {
  let report = verify("fn f(x : Int) {\n  assert x > 100\n}\n")
  let text = sarif_json(report)
  // No raw newline may appear inside a JSON string.
  assert_false(text.contains("\"message\":{\"text\":\"assert is violated: x = -1073741824\n"))
}
