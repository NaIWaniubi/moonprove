// Browser entry point. The host page defines two globals:
//
//   moonProveReadInput() -> the source to verify, as text
//   moonProveWriteOutput(json) -> unit
//
// The MoonBit side parses, verifies and returns one JSON document describing
// every obligation; the page renders it. Keeping the rendering out of MoonBit
// means the browser bundle contains the verifier and nothing about presentation.

///|
extern "js" fn read_input() -> String = "moonProveReadInput"

///|
extern "js" fn write_output(text : String) -> Unit = "moonProveWriteOutput"

///|
fn main {
  let source = read_input()
  let errors = @verify.parse_errors(source)
  if errors.length() > 0 {
    write_output(errors_json(errors))
    return
  }
  let report = @verify.verify(source)
  write_output(report_json(report))
}

///|
fn escape(text : String) -> String {
  let out = StringBuilder()
  for ch in text {
    match ch {
      '"' => out.write_string("\\\"")
      '\\' => out.write_string("\\\\")
      '\n' => out.write_string("\\n")
      '\r' => out.write_string("\\r")
      '\t' => out.write_string("\\t")
      _ => out.write_char(ch)
    }
  }
  out.to_string()
}

///|
fn errors_json(errors : Array[String]) -> String {
  let out = StringBuilder()
  out.write_string("{\"ok\":false,\"errors\":[")
  let mut first = true
  for e in errors {
    if !first {
      out.write_char(',')
    }
    first = false
    out.write_string("\"" + escape(e) + "\"")
  }
  out.write_string("]}")
  out.to_string()
}

///|
fn report_json(report : @core.Report) -> String {
  let out = StringBuilder()
  out.write_string("{\"ok\":true,\"results\":[")
  let mut first = true
  for r in report.results {
    if !first {
      out.write_char(',')
    }
    first = false
    out.write_string("{\"label\":\"" + escape(r.goal.label) + "\",\"line\":")
    out.write_string(r.goal.span.start.line.to_string())
    out.write_string(",\"outcome\":\"")
    out.write_string(outcome_tag(r.outcome))
    out.write_string("\",\"detail\":\"")
    out.write_string(escape(outcome_detail(report, r.outcome)))
    out.write_string("\",\"paths\":")
    out.write_string(r.paths.to_string())
    out.write_char('}')
  }
  out.write_string("],\"functions\":[")
  let mut first_fn = true
  for f in report.functions {
    if !first_fn {
      out.write_char(',')
    }
    first_fn = false
    out.write_string("\"" + escape(f) + "\"")
  }
  out.write_string("],\"truncated\":")
  out.write_string(report.truncated.to_string())
  out.write_char('}')
  out.to_string()
}

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
fn outcome_detail(report : @core.Report, outcome : @core.GoalOutcome) -> String {
  match outcome {
    @core.GoalOutcome::Holds => "the negation is unsatisfiable"
    @core.GoalOutcome::Violated(model, _) => {
      let parts : Array[String] = []
      model.each(fn(id, value) {
        parts.push(name_of(report, id) + " = " + value.to_string())
      })
      parts.sort()
      parts.join(", ")
    }
    @core.GoalOutcome::Bounded(detail) => detail
    @core.GoalOutcome::Unknown(detail) => detail
  }
}

///|
fn name_of(report : @core.Report, id : Int32) -> String {
  for v in report.vars {
    if v.id == id {
      return v.name
    }
  }
  "v" + id.to_string()
}
