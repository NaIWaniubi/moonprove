// The three command implementations. Kept apart from argument parsing so the
// parsing stays a flat table a reader can check at a glance.

///|
fn outcome_tag(outcome : @core.GoalOutcome) -> String {
  match outcome {
    @core.GoalOutcome::Holds => "proven"
    @core.GoalOutcome::Violated(_, _) => "violated"
    @core.GoalOutcome::Bounded(_) => "bounded"
    @core.GoalOutcome::Unknown(_) => "unknown"
  }
}

///|
fn outcome_detail(outcome : @core.GoalOutcome) -> String {
  match outcome {
    @core.GoalOutcome::Holds => ""
    @core.GoalOutcome::Violated(model, _) => render_model(model)
    @core.GoalOutcome::Bounded(detail) => detail
    @core.GoalOutcome::Unknown(detail) => detail
  }
}

///|
fn render_model(model : Map[Int32, Int]) -> String {
  let parts : Array[String] = []
  model.each(fn(id, value) { parts.push("v" + id.to_string() + "=" + value.to_string()) })
  parts.sort()
  "counterexample: " + parts.join(", ")
}

///|
fn run_verify(source : String, format : String, width : Int, path : String) -> Unit {
  let half = @solver.half_range(width)
  let errors = @verify.parse_errors(source)
  if errors.length() > 0 {
    for e in errors {
      println("parse: " + e)
    }
    @sys.exit(2)
  }
  let report = @verify.verify(source, width~)
  let mut violated = 0
  let mut undecided = 0
  for r in report.results {
    match r.outcome {
      @core.GoalOutcome::Violated(_, _) => violated = violated + 1
      @core.GoalOutcome::Holds => ()
      _ => undecided = undecided + 1
    }
  }
  if format == "json" {
    println(render_json(report))
  } else if format == "sarif" {
    println(@verify.to_sarif(report, tool_version, path))
  } else {
    for r in report.results {
      let line = "line " + r.goal.span.start.line.to_string() +
        "  " + r.goal.label + "  " + outcome_tag(r.outcome)
      println(line)
      let detail = outcome_detail(r.outcome)
      if detail != "" {
        println("        " + detail)
      }
    }
    let total = report.results.length()
    // A proof is always a proof *within a domain*. Stating it keeps the claim
    // honest: outside this box the tool makes no promise, and the 32-bit
    // wrap-around that lives outside it is exactly the case a reader should not
    // mistake for a bug in the assertion.
    println(
      "domain: Int parameters lie in [" + (0 - half).to_string() + ", " +
      (half - 1).to_string() + "]",
    )
    println(
      "\n" + total.to_string() + " obligation(s): " +
      (total - violated - undecided).to_string() + " proven, " +
      violated.to_string() + " violated, " +
      undecided.to_string() + " undecided",
    )
  }
  if violated > 0 {
    @sys.exit(1)
  }
  if undecided > 0 {
    @sys.exit(3)
  }
}

///|
fn render_json(report : @core.Report) -> String {
  let out = StringBuilder()
  out.write_string("{\"results\":[")
  let mut first = true
  for r in report.results {
    if !first {
      out.write_char(',')
    }
    first = false
    out.write_string("{\"label\":\"" + r.goal.label + "\",\"line\":")
    out.write_string(r.goal.span.start.line.to_string())
    out.write_string(",\"outcome\":\"")
    out.write_string(outcome_tag(r.outcome))
    out.write_string("\",\"paths\":")
    out.write_string(r.paths.to_string())
    out.write_string("}")
  }
  out.write_string("],\"functions\":[")
  let mut first_fn = true
  for f in report.functions {
    if !first_fn {
      out.write_char(',')
    }
    first_fn = false
    out.write_string("\"" + f + "\"")
  }
  out.write_string("],\"truncated\":")
  out.write_string(report.truncated.to_string())
  out.write_string("}")
  out.to_string()
}

///|
fn run_explain(source : String) -> Unit {
  let report = @verify.verify(source)
  for r in report.results {
    println("line " + r.goal.span.start.line.to_string() + "  " + r.goal.label)
    match r.outcome {
      @core.GoalOutcome::Holds =>
        println("  proven: the negation of the goal is unsatisfiable")
      @core.GoalOutcome::Violated(model, steps) => {
        println("  violated: " + render_model(model))
        for s in steps {
          println("    [" + s.kind + "] " + s.detail)
        }
      }
      @core.GoalOutcome::Bounded(detail) => println("  bounded: " + detail)
      @core.GoalOutcome::Unknown(detail) => println("  unknown: " + detail)
    }
    println("")
  }
}

///|
fn run_dump(source : String) -> Unit {
  let program = @symir.parse(source)
  for e in program.errors {
    println("parse: " + e)
  }
  for f in program.functions {
    println("fn " + f.name + " (line " + f.line.to_string() + ")")
    println("  params: " + f.params.length().to_string())
    println("  requires: " + f.requires.length().to_string())
    println("  ensures: " + f.ensures.length().to_string())
    println("  body: " + f.body.length().to_string() + " statement(s)")
  }
}
