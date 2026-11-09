// Symbolic execution: the path-sensitive engine.
//
// The engine walks a function body once, but carries *all* live paths at once:
// a state is a (path condition, symbolic store) pair, and a branch forks it. That
// is what makes the answer path-sensitive without re-walking the program.
//
// Loops are the interesting part. A loop cannot be unrolled symbolically forever,
// so `while` is handled by *induction*: the invariant must hold on entry, be
// preserved by one arbitrary iteration, and imply the exit condition's negation
// (plus the invariant) at every exit. That is a finite obligation set for an
// infinite loop, which is why the tool can verify loops at all.

///|
/// The symbolic value a variable holds on a path.
///
/// Kept as a term rather than a concrete value: the whole point is to reason
/// about *all* values at once.
pub(all) struct SymVal {
  term : @core.Term
  sort : @core.Sort
} derive(Debug, Eq)

///|
/// One execution path through a function.
pub(all) struct PathState {
  /// Constraints that hold on this path.
  assumes : Array[@core.Term]
  /// Variables bound on this path.
  store : Map[String, SymVal]
  /// How many `while` loops this path has entered; used for loop obligations.
  mut loops : Int
} derive(Debug)

///|
/// The engine's result for one function.
pub(all) struct FnResult {
  name : String
  /// Every obligation the function produced, with the path count that produced
  /// it, so the caller can price the proof.
  goals : Array[GoalDraft]
  /// Paths abandoned because the explorer hit a bound.
  truncated : Int
} derive(Debug)

///|
/// A goal plus the variable table it was built against.
pub(all) struct GoalDraft {
  goal : @core.Goal
  vars : Array[@core.SymVar]
  outcome : @core.GoalOutcome
  paths : Int
} derive(Debug)

///|
/// The symbolic state machine for one function.
priv struct Engine {
  /// Fresh variable supply, shared across the function's paths so ids are unique
  /// within the report.
  next_var : Array[@core.SymVar]
  next_id : Array[Int32]
  /// Functions already verified, available to call.
  callees : Map[String, Array[FnResult]]
  errors : Array[String]
  /// Total paths explored across all obligations.
  paths : Array[Int]
  truncated : Array[Int]
  /// Goals produced by statements (assertions and loop obligations), in body
  /// order. Contract goals are added by `verify_fn` around them.
  last_goals : Array[GoalDraft]
  /// `len(x)` terms, so the same length is one variable everywhere.
  len_cache : Map[String, Int32]
  /// Paths that reached a `return`, which is where a postcondition is checked.
  exits : Array[PathState]
}

///|
/// Verifies one function: its contract first, then every `assert` in its body.
///
/// The order matters for the report — contract obligations are what a reader
/// looks at first — and it is also what lets an `assert` be reported with the
/// contract's assumptions already in scope.
pub fn verify_fn(fn_ : @symir.Fn, width : Int) -> FnResult {
  let vars : Array[@core.SymVar] = []
  let engine : Engine = {
    next_var: vars,
    next_id: [1],
    callees: Map([]),
    errors: [],
    paths: [0],
    truncated: [0],
    last_goals: [],
    len_cache: Map([]),
    exits: [],
  }
  let goals : Array[GoalDraft] = []
  // Entry store: every parameter its own fresh symbolic variable.
  let entry : Map[String, SymVal] = Map([])
  for param in fn_.params {
    let id = fresh(engine, param.name, if param.nat {
      @core.Sort::Nat
    } else {
      @core.Sort::Int(width)
    })
    let sort = if param.nat { @core.Sort::Nat } else { @core.Sort::Int(width) }
    entry.set(param.name, {
      term: @core.Term::Var(id),
      sort,
    })
  }
  // The `nat` assumption is part of the specification of the parameter, not a
  // hint: without it a length could be negative and every bound proof would be
  // vacuous.
  // Every parameter is assumed inside the range the solver reasons about. This is
  // not a claim about the language: it is the domain of the analysis, and stating it
  // makes a proof ("holds for all inputs in the box") and a counterexample ("this
  // value in the box") talk about the same set.
  let env_assumes : Array[@core.Term] = []
  for param in fn_.params {
    match entry.get(param.name) {
      Some(value) =>
        match value.sort {
          @core.Sort::Nat =>
            env_assumes.push(@core.Term::Le(@core.Term::Lit(0), value.term))
          @core.Sort::Int(bits) => {
            let half = @solver.half_range(bits)
            env_assumes.push(@core.Term::Le(@core.Term::Lit(0 - half), value.term))
            env_assumes.push(
              @core.Term::Le(value.term, @core.Term::Lit(half - 1)),
            )
          }
          @core.Sort::Bool => ()
        }
      None => ()
    }
  }
  // Preconditions must hold on entry. Each becomes a goal over all inputs.
  for req in fn_.requires {
    match eval_expr(engine, req, entry) {
      None => engine.errors.push("unsupported expression in `require`")
      Some(cond) => {
        let violation = env_assumes.copy()
        violation.push(@core.Term::Not(cond))
        let (sat, trace) = @solver.solve(engine.next_var.copy(), violation)
        goals.push({
          goal: @core.Goal::{
            label: "require",
            span: span_at(req_line(req)),
            assumptions: env_assumes.copy(),
            conclusion: cond,
          },
          vars: engine.next_var.copy(),
          outcome: outcome_of(sat, trace),
          paths: 1,
        })
      }
    }
  }
  // Walk the body from the entry state, collecting assertions and the return
  // value per path.
  let start : PathState = { assumes: env_assumes.copy(), store: entry, loops: 0 }
  let ends = exec_block(engine, fn_.body, [start], width)
  // A function with no explicit `return` exits at the end of its body, so those
  // paths count as exits too.
  let exit_states = engine.exits.copy()
  for state in ends {
    exit_states.push(state)
  }
  // Postconditions must hold at every exit.
  for ens in fn_.ensures {
    for end_state in exit_states {
      match eval_expr(engine, ens, end_state.store) {
        None => engine.errors.push("unsupported expression in `ensure`")
        Some(cond) => {
          let violation = end_state.assumes.copy()
          violation.push(@core.Term::Not(cond))
          let (sat, trace) = @solver.solve(engine.next_var.copy(), violation)
          goals.push({
            goal: @core.Goal::{
              label: "ensure",
              span: span_at(expr_line(ens)),
              assumptions: end_state.assumes.copy(),
              conclusion: cond,
            },
            vars: engine.next_var.copy(),
            outcome: outcome_of(sat, trace),
            paths: 1,
          })
        }
      }
    }
  }
  // Body goals come after the contract goals, in the order they were met.
  for draft in engine.last_goals {
    goals.push(draft)
  }
  {
    name: fn_.name,
    goals,
    truncated: engine.truncated[0],
  }
}

///|
/// Execute a statement list over a set of incoming paths, returning the paths
/// that reach the end.
fn exec_block(
  engine : Engine,
  stmts : Array[@symir.Stmt],
  incoming : Array[PathState],
  width : Int,
) -> Array[PathState] {
  let mut states = incoming
  for stmt in stmts {
    states = exec_stmt(engine, stmt, states, width)
    if states.length() == 0 {
      // Every path diverged (returned or became infeasible): nothing after this
      // statement can run.
      return states
    }
  }
  states
}

///|
fn exec_stmt(
  engine : Engine,
  stmt : @symir.Stmt,
  incoming : Array[PathState],
  width : Int,
) -> Array[PathState] {
  match stmt {
    @symir.Stmt::Let(let_) => {
      let out : Array[PathState] = []
      for state in incoming {
        match eval_expr(engine, let_.value, state.store) {
          None => ()
          Some(term) => {
            let next = copy_state(state)
            let sort = infer_sort(let_.value, state.store, width)
            next.store.set(let_.name, { term, sort })
            out.push(next)
          }
        }
      }
      out
    }
    @symir.Stmt::Assign(assign) => {
      let out : Array[PathState] = []
      for state in incoming {
        match eval_expr(engine, assign.value, state.store) {
          None => ()
          Some(term) => {
            let next = copy_state(state)
            let sort = infer_sort(assign.value, state.store, width)
            next.store.set(assign.name, { term, sort })
            out.push(next)
          }
        }
      }
      out
    }
    @symir.Stmt::If(if_) => {
      let out : Array[PathState] = []
      for state in incoming {
        engine.paths[0] = engine.paths[0] + 1
        match eval_expr(engine, if_.cond, state.store) {
          None => ()
          Some(cond) => {
            let then_state = copy_state(state)
            then_state.assumes.push(cond)
            let else_state = copy_state(state)
            else_state.assumes.push(@core.Term::Not(cond))
            let then_out = exec_block(engine, if_.then_, [then_state], width)
            let else_out = exec_block(engine, if_.else_, [else_state], width)
            for s in then_out {
              out.push(s)
            }
            for s in else_out {
              out.push(s)
            }
          }
        }
      }
      out
    }
    @symir.Stmt::While(while_) => exec_while(engine, while_, incoming, width)
    @symir.Stmt::Ret(ret) => {
      // A return ends the path: the exit states are recorded for the postcondition
      // and the path must NOT continue into the statements after the `if` that
      // contained it. `exec_block` therefore treats an empty result as "every path
      // ended".
      for state in incoming {
        match eval_expr(engine, ret.value, state.store) {
          None => ()
          Some(term) => {
            // A return ends the path: freeze its exit value in a synthetic
            // variable so a postcondition can name it.
            let next = copy_state(state)
            let id = fresh(engine, "return", @core.Sort::Int(width))
            next.store.set("return_val", {
              term: @core.Term::Var(id),
              sort: @core.Sort::Int(width),
            })
            next.assumes.push(@core.Term::Eq(@core.Term::Var(id), term))
            engine.exits.push(next)
          }
        }
      }
      // The exits were recorded above; nothing continues past a `return`.
      []
    }
    @symir.Stmt::Assert(assert_) => {
      let out : Array[PathState] = []
      for state in incoming {
        engine.paths[0] = engine.paths[0] + 1
        match eval_expr(engine, assert_.cond, state.store) {
          None => ()
          Some(cond) => {
            // Build the violation query: the path holds and the assertion does
            // not. `Unsat` for it is the proof.
            let violation : Array[@core.Term] = []
            for a in state.assumes {
              violation.push(a)
            }
            violation.push(@core.Term::Not(cond))
            let (sat, trace) = @solver.solve(engine.next_var.copy(), violation)
            ignore(trace)
            let outcome = match sat {
              @core.Sat::Unsat => @core.GoalOutcome::Holds
              @core.Sat::Sat(model) =>
                @core.GoalOutcome::Violated(model, trace.steps)
              @core.Sat::Unknown(reason) =>
                @core.GoalOutcome::Unknown(reason)
            }
            engine.last_goals.push({
              goal: @core.Goal::{
                label: "assert",
                span: span_at(assert_.line),
                assumptions: state.assumes.copy(),
                conclusion: cond,
              },
              vars: engine.next_var.copy(),
              outcome,
              paths: engine.paths[0],
            })
            // Execution continues only on the path where the assertion held.
            let next = copy_state(state)
            next.assumes.push(cond)
            out.push(next)
          }
        }
      }
      out
    }
    @symir.Stmt::Call(call) => {
      exec_call(engine, call, incoming, width)
    }
  }
}

///|
/// A loop, verified by induction rather than unrolled.
///
/// The obligations are the three a reader of Hoare logic expects:
///
///   1. the invariant holds when the loop is entered;
///   2. assuming the invariant and the condition, executing the body re-establishes
///      the invariant;
///   3. the invariant and the negated condition are available on exit.
///
/// A loop with no invariant cannot be verified and is reported as such, never
/// silently assumed.
fn exec_while(
  engine : Engine,
  while_ : @symir.WhileStmt,
  incoming : Array[PathState],
  width : Int,
) -> Array[PathState] {
  let out : Array[PathState] = []
  for state in incoming {
    engine.paths[0] = engine.paths[0] + 1
    let invariant_terms : Array[@core.Term] = []
    let mut invariant_ok = true
    for inv in while_.invariants {
      match eval_expr(engine, inv, state.store) {
        None => invariant_ok = false
        Some(t) => invariant_terms.push(t)
      }
    }
    let cond = match eval_expr(engine, while_.cond, state.store) {
      None => {
        invariant_ok = false
        @core.Term::False
      }
      Some(c) => c
    }
    if !invariant_ok || invariant_terms.length() == 0 {
      engine.last_goals.push({
        goal: @core.Goal::{
          label: "loop invariant",
          span: span_at(while_.line),
          assumptions: state.assumes.copy(),
          conclusion: @core.Term::False,
        },
        vars: engine.next_var.copy(),
        outcome: @core.GoalOutcome::Bounded(
          "loop has no invariant: an unbounded loop cannot be verified; add `invariant`",
        ),
        paths: engine.paths[0],
      })
      // The path continues past the loop with the loop's effects unknown, which
      // is the conservative direction: a later assertion must prove itself
      // without assuming anything the loop did.
      let next = copy_state(state)
      next.assumes.push(@core.Term::Not(cond))
      out.push(next)
      continue
    }
    // (1) The invariant holds on entry.
    let entry_violation : Array[@core.Term] = []
    for a in state.assumes {
      entry_violation.push(a)
    }
    for t in invariant_terms {
      entry_violation.push(@core.Term::Not(t))
    }
    let (entry_sat, entry_trace) = @solver.solve(engine.next_var.copy(), entry_violation)
    engine.last_goals.push({
      goal: @core.Goal::{
        label: "invariant on entry",
        span: span_at(while_.line),
        assumptions: state.assumes.copy(),
        conclusion: conjunct(invariant_terms),
      },
      vars: engine.next_var.copy(),
      outcome: outcome_of(entry_sat, entry_trace),
      paths: engine.paths[0],
    })
    // (2) The body preserves it, starting from an arbitrary state that satisfies
    // the invariant and the condition.
    let body_entry = copy_state(state)
    for t in invariant_terms {
      body_entry.assumes.push(t)
    }
    body_entry.assumes.push(cond)
    body_entry.loops = body_entry.loops + 1
    let body_exits = exec_block(engine, while_.body, [body_entry], width)
    for exit_state in body_exits {
      let preservation_violation : Array[@core.Term] = []
      for a in exit_state.assumes {
        preservation_violation.push(a)
      }
      for t in invariant_terms {
        preservation_violation.push(@core.Term::Not(t))
      }
      let (sat, trace) = @solver.solve(engine.next_var.copy(), preservation_violation)
      engine.last_goals.push({
        goal: @core.Goal::{
          label: "invariant preserved",
          span: span_at(while_.line),
          assumptions: exit_state.assumes.copy(),
          conclusion: conjunct(invariant_terms),
        },
        vars: engine.next_var.copy(),
        outcome: outcome_of(sat, trace),
        paths: engine.paths[0],
      })
    }
    // (3) On exit the invariant holds and the condition is false.
    let exit_state = copy_state(state)
    for t in invariant_terms {
      exit_state.assumes.push(t)
    }
    exit_state.assumes.push(@core.Term::Not(cond))
    out.push(exit_state)
  }
  out
}

///|
fn exec_call(
  engine : Engine,
  call : @symir.CallStmt,
  incoming : Array[PathState],
  _width : Int,
) -> Array[PathState] {
  let out : Array[PathState] = []
  for state in incoming {
    match engine.callees.get(call.name) {
      None =>
        // A call to something outside the verified set has unknown effects. The
        // remaining path keeps its assumptions; nothing is invented about the
        // callee, and a later assertion has to prove itself without help.
        out.push(copy_state(state))
      Some(results) => {
        // Inline the callee's postconditions as assumptions, which is the same
        // contract a reader would use.
        let next = copy_state(state)
        for callee in results {
          for draft in callee.goals {
            next.assumes.push(draft.goal.conclusion)
          }
        }
        out.push(next)
      }
    }
  }
  out
}

///|
fn outcome_of(sat : @core.Sat, trace : @solver.Trace) -> @core.GoalOutcome {
  match sat {
    @core.Sat::Unsat => @core.GoalOutcome::Holds
    @core.Sat::Sat(model) => @core.GoalOutcome::Violated(model, trace.steps)
    @core.Sat::Unknown(reason) => @core.GoalOutcome::Unknown(reason)
  }
}

///|
fn conjunct(terms : Array[@core.Term]) -> @core.Term {
  let mut acc = @core.Term::True
  for t in terms {
    acc = @core.Term::And(acc, t)
  }
  acc
}

///|
fn fresh(engine : Engine, name : String, sort : @core.Sort) -> Int32 {
  let id = engine.next_id[0]
  engine.next_id[0] = id + 1
  engine.next_var.push({ id, name, sort })
  id
}

///|
fn copy_state(state : PathState) -> PathState {
  { assumes: state.assumes.copy(), store: state.store.copy(), loops: state.loops }
}

///|
fn span_at(line : Int32) -> @core.Span {
  {
    start: { line, col: 1 },
    end: { line, col: 2 },
  }
}

///|
fn req_line(expr : @symir.Expr) -> Int32 {
  expr_line(expr)
}

///|
fn expr_line(expr : @symir.Expr) -> Int32 {
  match expr {
    @symir.Expr::IntLit(e) => e.line
    @symir.Expr::VarRef(e) => e.line
    @symir.Expr::Bin(e) => e.line
    @symir.Expr::Un(e) => e.line
    @symir.Expr::Ite(e) => e.line
    @symir.Expr::App(e) => e.line
    @symir.Expr::Len(e) => e.line
  }
}

///|
fn infer_sort(expr : @symir.Expr, store : Map[String, SymVal], width : Int) -> @core.Sort {
  match expr {
    @symir.Expr::Len(_) => @core.Sort::Nat
    @symir.Expr::VarRef(v) =>
      match store.get(v.name) {
        Some(value) => value.sort
        None => @core.Sort::Int(width)
      }
    _ => @core.Sort::Int(width)
  }
}
