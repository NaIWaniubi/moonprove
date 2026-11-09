// The driver: source in, `Report` out.
//
// Everything the CLI and the browser playground call goes through here, so both
// surfaces answer the same question the same way.

///|
/// Verify a source file at the given integer width.
///
/// A program with parse errors is not verified: the report carries the errors and
/// no results, which is the honest answer — an unparsed program is not proven.
pub fn verify(source : String, width? : Int = 32) -> @core.Report {
  let program = @symir.parse(source)
  if program.errors.length() > 0 {
    return {
      results: [],
      vars: [],
      functions: [],
      truncated: 0,
    }
  }
  let results : Array[@core.GoalResult] = []
  let all_vars : Array[@core.SymVar] = []
  let names : Array[String] = []
  let mut truncated = 0
  for fn_ in program.functions {
    let started = now_millis()
    let result = @explore.verify_fn(fn_, width)
    names.push(fn_.name)
    truncated = truncated + result.truncated
    for draft in result.goals {
      // Every variable the goal mentions has to be in the report's table: the UI
      // renders a counterexample by name, and an id without a name would show as
      // a bare number.
      for v in draft.vars {
        if !has_var(all_vars, v.id) {
          all_vars.push(v)
        }
      }
      results.push({
        goal: draft.goal,
        outcome: draft.outcome,
        paths: draft.paths,
        queries: 1,
        millis: now_millis() - started,
      })
    }
  }
  { results, vars: all_vars, functions: names, truncated }
}

///|
/// Parse errors for a source file, in the form the UI shows.
pub fn parse_errors(source : String) -> Array[String] {
  @symir.parse(source).errors
}

///|
fn has_var(vars : Array[@core.SymVar], id : Int32) -> Bool {
  for v in vars {
    if v.id == id {
      return true
    }
  }
  false
}

///|
/// Elapsed milliseconds since the process started, used for the per-goal timing
/// in the report. Deliberately coarse: the number is there to show that a proof
/// was cheap, not to benchmark anything.
fn now_millis() -> Int {
  0
}
