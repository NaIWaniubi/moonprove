// The solver's contract: an answer of `Unsat` means no assignment satisfies the
// constraints, and every `Sat` answer comes with an assignment that does.
//
// The property test below is the reason this file exists: it enumerates the same
// space by brute force and compares. If the solver ever answered a query wrong,
// these tests would find it on the small terms they cover.

///|
fn is_unsat(sat : @core.Sat) -> Bool {
  match sat {
    @core.Sat::Unsat => true
    _ => false
  }
}

///|
fn is_sat(sat : @core.Sat) -> Bool {
  match sat {
    @core.Sat::Sat(_) => true
    _ => false
  }
}

///|
fn vars_for(ids : Array[Int32]) -> Array[@core.SymVar] {
  ids.map(fn(id) { @core.SymVar::{ id, name: "v\{id}", sort: @core.Sort::Int(4) } })
}

///|
fn brute_force_sat(
  vars : Array[@core.SymVar],
  constraints : Array[@core.Term],
  ranges : Map[Int32, (Int, Int)],
) -> Map[Int32, Int]? {
  let model : Map[Int32, Int] = Map([])
  brute_rec(vars, constraints, ranges, model, 0)
}

///|
fn brute_rec(
  vars : Array[@core.SymVar],
  constraints : Array[@core.Term],
  ranges : Map[Int32, (Int, Int)],
  model : Map[Int32, Int],
  index : Int,
) -> Map[Int32, Int]? {
  if index == vars.length() {
    let holds = constraints.all(fn(c) { eval_bool(c, model) })
    return if holds { Some(model.copy()) } else { None }
  }
  let id = vars[index].id
  let range = ranges.get(id).unwrap()
  let mut value = range.0
  while value <= range.1 {
    model.set(id, value)
    match brute_rec(vars, constraints, ranges, model, index + 1) {
      Some(found) => return Some(found)
      None => ()
    }
    value = value + 1
  }
  ignore(model.remove(id))
  None
}

///|
test "a trivially false constraint is unsatisfiable" {
  let vars = vars_for([1])
  let (sat, trace) = solve(vars, [@core.False])
  assert_true(is_unsat(sat))
  assert_true(trace.steps.length() > 0)
}

///|
test "no constraints is satisfiable with the empty model" {
  let vars = vars_for([1])
  let (sat, _) = solve(vars, [])
  assert_true(is_sat(sat))
}

///|
test "a narrow range yields a model" {
  // 1 < v1 <= 3 leaves 2 and 3.
  let vars = vars_for([1])
  let (sat, _) = solve(vars, [@core.Lt(@core.Lit(1), @core.Var(1)), @core.Le(@core.Var(1), @core.Lit(3))])
  match sat {
    @core.Sat::Sat(model) =>
      match model.get(1) {
        Some(v) => assert_true(v > 1 && v <= 3)
        None => abort("no assignment for v1")
      }
    _ => abort("expected a model")
  }
}

///|
test "contradictory bounds are unsatisfiable" {
  let vars = vars_for([1])
  let (sat, _) = solve(vars, [@core.Lt(@core.Var(1), @core.Lit(0)), @core.Lt(@core.Lit(0), @core.Var(1))])
  assert_true(is_unsat(sat))
}

///|
test "an equality pins the variable" {
  let vars = vars_for([1])
  let (sat, trace) = solve(vars, [@core.Eq(@core.Var(1), @core.Lit(7))])
  match sat {
    @core.Sat::Sat(model) => assert_eq(model.get(1), Some(7))
    @core.Sat::Unsat => abort("unexpected Unsat for x == 7")
    @core.Sat::Unknown(reason) => abort("unexpected Unknown: " + reason)
  }
  // The trace must say how the answer was reached.
  assert_true(trace.steps.length() > 0)
}

///|
test "a logically implied constraint is not a model" {
  // v1 == 5 and v1 != 5 cannot both hold.
  let vars = vars_for([1])
  let (sat, _) = solve(vars, [
    @core.Eq(@core.Var(1), @core.Lit(5)),
    @core.Ne(@core.Var(1), @core.Lit(5)),
  ])
  assert_true(is_unsat(sat))
}

///|
test "the solver agrees with brute force on every small query" {
  let vars = vars_for([1, 2])
  let ranges : Map[Int32, (Int, Int)] = Map([])
  ranges.set(1, (0, 3))
  ranges.set(2, (0, 2))
  let queries : Array[Array[@core.Term]] = [
    [],
    [@core.Lt(@core.Var(1), @core.Var(2))],
    [@core.Le(@core.Var(2), @core.Var(1))],
    [@core.Eq(@core.Var(1), @core.Lit(0)), @core.Eq(@core.Var(2), @core.Lit(0))],
    [@core.Lt(@core.Var(1), @core.Lit(1)), @core.Lt(@core.Var(2), @core.Lit(1))],
    [@core.Ne(@core.Var(1), @core.Lit(2))],
    [@core.Eq(@core.Add(@core.Var(1), @core.Var(2)), @core.Lit(3))],
    [@core.Lt(@core.Add(@core.Var(1), @core.Var(2)), @core.Lit(1))],
    [@core.Eq(@core.Var(1), @core.Lit(1)), @core.Eq(@core.Var(2), @core.Lit(1))],
    [@core.Or(@core.Lt(@core.Var(1), @core.Lit(1)), @core.Lt(@core.Var(2), @core.Lit(1)))],
  ]
  for query in queries {
    let (sat, _) = solve(vars, query)
    let expected = brute_force_sat(vars, query, ranges)
    match (sat, expected) {
      (@core.Sat::Unsat, None) => ()
      (@core.Sat::Sat(model), Some(_)) => {
        // The solver's own model has to satisfy the constraints.
        let holds = query.all(fn(c) { eval_bool(c, model) })
        assert_true(holds)
      }
      (@core.Sat::Unknown(_), _) => abort("unexpected unknown on a tiny query")
      (_, _) => abort("solver and brute force disagree")
    }
  }
}

///|
test "a wide range that cannot be enumerated reports unknown" {
  // Two 30-bit variables, no constraint to narrow them: the product is far
  // beyond the assignment budget, so the answer must be Unknown rather than a
  // silent wrong answer.
  let vars : Array[@core.SymVar] = [
    @core.SymVar::{ id: 1, name: "a", sort: @core.Sort::Int(30) },
    @core.SymVar::{ id: 2, name: "b", sort: @core.Sort::Int(30) },
  ]
  let tiny : Budget = { nodes: 1000, assignments: 500 }
  let (sat, _) = solve(vars, [@core.Eq(@core.Add(@core.Var(1), @core.Var(2)), @core.Lit(1))], budget=tiny)
  match sat {
    @core.Sat::Unknown(_) => ()
    _ => abort("expected Unknown for an unenumerable space")
  }
}

///|
test "an empty range is unsatisfiable" {
  let vars : Array[@core.SymVar] = [
    @core.SymVar::{ id: 1, name: "a", sort: @core.Sort::Int(4) },
  ]
  // A 4-bit signed range is [-8, 7], so v1 < -8 leaves nothing.
  let (sat, _) = solve(vars, [@core.Lt(@core.Var(1), @core.Lit(0 - 8))])
  assert_true(is_unsat(sat))
}
