// SARIF 2.1.0 output.
//
// A verifier that a CI cannot read is a verifier nobody runs twice. SARIF is the
// format GitHub's code scanning ingests, so a finding here shows up in the pull
// request's diff instead of in a log nobody opens.
//
// The mapping is deliberately literal: one obligation becomes one result, its
// verdict becomes the level, and a counterexample goes into the message because
// that is the part a reader needs. `proven` results are included as `none` level:
// a reviewer scrolling the PR should see what was checked, not only what failed.

///|
/// Render a report as SARIF 2.1.0.
pub fn to_sarif(report : @core.Report, tool_version : String, source_name : String) -> String {
  let out = StringBuilder()
  out.write_string("{\"$schema\":\"https://json.schemastore.org/sarif-2.1.0.json\",")
  out.write_string("\"version\":\"2.1.0\",\"runs\":[{")
  out.write_string("\"tool\":{\"driver\":{\"name\":\"moonprove\",\"version\":\"")
  out.write_string(escape(tool_version))
  out.write_string("\",\"informationUri\":\"https://github.com/NaIWaniubi/moonprove\",")
  out.write_string("\"rules\":[")
  out.write_string(rule_json("proven", "proven", "The negation of this obligation is unsatisfiable."))
  out.write_char(',')
  out.write_string(rule_json("violated", "violated", "A concrete input violates this obligation."))
  out.write_char(',')
  out.write_string(rule_json("undecided", "undecided", "Neither proven nor refuted within the analysis domain."))
  out.write_string("]}},")
  out.write_string("\"results\":[")
  let mut first = true
  for r in report.results {
    if !first {
      out.write_char(',')
    }
    first = false
    out.write_string(result_json(r, source_name, report.vars))
  }
  out.write_string("]}]}")
  out.to_string()
}

///|
fn rule_json(id : String, name : String, text : String) -> String {
  "{\"id\":\"" + id + "\",\"name\":\"" + escape(name) +
  "\",\"shortDescription\":{\"text\":\"" + escape(text) + "\"}," +
  "\"defaultConfiguration\":{\"level\":\"" + level_of_name(id) + "\"}}"
}

///|
fn level_of_name(name : String) -> String {
  match name {
    "violated" => "error"
    "undecided" => "warning"
    _ => "none"
  }
}

///|
/// One result. `ruleId` names the verdict so a query can filter on it; `level`
/// follows SARIF's vocabulary and is what the CI renders.
fn result_json(
  r : @core.GoalResult,
  source_name : String,
  vars : Array[@core.SymVar],
) -> String {
  let category = match r.outcome {
    @core.GoalOutcome::Holds => "proven"
    @core.GoalOutcome::Violated(_, _) => "violated"
    @core.GoalOutcome::Bounded(_) => "undecided"
    @core.GoalOutcome::Unknown(_) => "undecided"
  }
  let message = message_of(r, vars)
  "{\"ruleId\":\"" + category + "\",\"level\":\"" + level_of_name(category) +
  "\",\"message\":{\"text\":\"" + escape(message) + "\"}," +
  "\"locations\":[{\"physicalLocation\":{\"artifactLocation\":{\"uri\":\"" +
  escape(source_name) + "\"},\"region\":{\"startLine\":" +
  r.goal.span.start.line.to_string() + ",\"startColumn\":1}}}]," +
  "\"properties\":{\"obligation\":\"" + escape(r.goal.label) +
  "\",\"paths\":" + r.paths.to_string() + "}}"
}

///|
/// The text a reader sees in the PR annotation.
fn message_of(r : @core.GoalResult, vars : Array[@core.SymVar]) -> String {
  let head = r.goal.label + " could not be violated"
  match r.outcome {
    @core.GoalOutcome::Holds => head
    @core.GoalOutcome::Violated(model, _) =>
      r.goal.label + " is violated: " + render_model_text(model, vars)
    @core.GoalOutcome::Bounded(detail) => r.goal.label + " is undecided: " + detail
    @core.GoalOutcome::Unknown(detail) => r.goal.label + " is undecided: " + detail
  }
}

///|
fn render_model_text(model : Map[Int32, Int], vars : Array[@core.SymVar]) -> String {
  let parts : Array[String] = []
  model.each(fn(id, value) {
    // The name the user wrote, not the internal id: a CI annotation reading
    // `v1 = -1073741824` makes the reader go looking for a variable called v1.
    parts.push(name_of(vars, id) + " = " + value.to_string())
  })
  parts.sort()
  parts.join(", ")
}

///|
fn name_of(vars : Array[@core.SymVar], id : Int32) -> String {
  for v in vars {
    if v.id == id {
      return v.name
    }
  }
  "v" + id.to_string()
}

///|
/// JSON string escaping. Only the characters SARIF consumers care about.
pub fn escape(text : String) -> String {
  let out = StringBuilder()
  for ch in text {
    let code = ch.to_int()
    if ch == '"' {
      out.write_string("\\\"")
    } else if code == 92 {
      out.write_string("\\\\")
    } else if code == 10 {
      out.write_string("\n")
    } else if code == 13 {
      out.write_string("\r")
    } else if code == 9 {
      out.write_string("\t")
    } else {
      out.write_char(ch)
    }
  }
  out.to_string()
}
