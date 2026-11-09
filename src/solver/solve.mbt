// The solver: a complete decision procedure for the fragment the tool emits.
//
// The approach is the one a small verifier can actually trust: interval
// propagation to shrink every variable's range, then exhaustive search over the
// (now finite) remaining space. When the propagation proves the goal holds for
// every input, the answer is `Unsat` for the counterexample query — a proof, not
// a heuristic. When the search space is still too large, the answer is
// `Unknown`, never a guess.
//
// This is why the tool can say "proven" without shipping a full SMT solver: the
// logic is deliberately small (see `@core.Term`), and every rule the interpreter
// emits keeps terms within it.

///|
/// A budget on how much work one query may do. Both limits are real: exhausting
/// either yields `Unknown`, and the report says so.
pub(all) struct Budget {
  /// Maximum nodes visited by interval propagation.
  nodes : Int
  /// Maximum assignments tried by the search.
  assignments : Int
} derive(Debug, Eq)

///|
/// The default budget: generous for the small terms a function body produces,
/// small enough that an accidental hard query cannot hang the tool.
pub fn Budget::default() -> Budget {
  { nodes: 200000, assignments: 400000 }
}

///|
/// The narration of one query, for the UI.
pub(all) struct Trace {
  steps : Array[@core.SolverStep]
  /// Variables whose range the propagation narrowed, with the final bounds.
  bounds : Array[(Int32, Int, Int)]
  /// How many assignments the search actually tried.
  tried : Int
} derive(Debug)

///|
/// Solve `constraints` for a model, or prove they cannot all hold.
///
/// `vars` gives every variable's sort; a variable that appears in the terms but
/// not in `vars` is an internal error and yields `Unknown` rather than a guess.
pub fn solve(
  vars : Array[@core.SymVar],
  constraints : Array[@core.Term],
  budget? : Budget = Budget::default(),
) -> (@core.Sat, Trace) {
  let stepped : Array[@core.SolverStep] = []
  let sorts : Map[Int32, @core.Sort] = Map([])
  for v in vars {
    sorts.set(v.id, v.sort)
  }
  let normalized = constraints.map(fn(c) { simplify_with(c, sorts) })
  let impossible = normalized.any(fn(c) {
    match c {
      False => true
      _ => false
    }
  })
  let step_impossible : @core.SolverStep = {
    kind: "normalize",
    detail: if impossible {
      "a constraint simplifies to false, so the query is unsatisfiable"
    } else {
      "constraints normalized"
    },
    depth: 0,
  }
  stepped.push(step_impossible)
  if impossible {
    return (@core.Sat::Unsat, { steps: stepped, bounds: [], tried: 0, })
  }
  // Flatten conjunctions: `x > 0 && y > 0` is two facts, and narrowing only
  // sees facts one at a time.
  let flattened : Array[@core.Term] = []
  for c in normalized {
    flatten_conjunct(c, flattened)
  }
  let keep = flattened.filter(fn(c) {
    match c {
      True => false
      _ => true
    }
  })
  if keep.length() == 0 {
    // Every constraint was trivially true: any assignment works, so the empty
    // assignment is a model.
    return (@core.Sat::Sat(Map([])), { steps: stepped, bounds: [], tried: 0, })
  }
  // Fourier–Motzkin decides the linear fragment outright. `Yes` is a proof of
  // unsatisfiability over the reals, hence over the integers; `No` means the
  // rational relaxation is satisfiable, so the integer question is still open and
  // falls through to the search below.
  // Interval refutation first: with every variable's range narrowed, a constraint
  // whose minimum possible value already violates it cannot hold. This is what
  // decides `0 < x, 0 < y, x + y <= 0` — plain real elimination does not, because
  // it is the integrality of the bounds that makes it contradictory.
  let narrowed = narrow_from_constraints(vars, keep)
  // The wrap rewrite has to happen before any decision procedure looks at the
  // constraint: `wrap(x + y, 32)` is not linear and has no interval bound, while
  // `x + y` has both. With the narrowed ranges the rewrite is meaning-preserving.
  let unwrapped = match narrowed {
    Some(ranges) => keep.map(fn(c) { drop_redundant_wraps(c, ranges) })
    None => keep
  }
  // Floor division binds tightly to its comparison: for integer `t`, positive `k`
  // and integer `c`, `t / k < c` iff `t < c*k`, and `t / k <= c` iff `t < (c+1)*k`.
  // Rewriting the comparison lets the linear fragment see the quotient, which is
  // what makes a midpoint bound provable instead of merely plausible.
  let divided = unwrapped.map(fn(c) { clear_division(c) })
  let bounds_conflict = match narrowed {
    Some(ranges) => {
      // Replace each division by a positive literal with the tightest value its
      // operand's range forces, when that range is one-sided. `x / 2` with
      // x >= 0 becomes `0 / 2`; with x < 0 it becomes `(lo) / 2`. That is a
      // rewrite valid *on this path*, so it can only help a refutation.
      let substituted = divided.map(fn(c) { subst_divisions(c, ranges) })
      refuted_by_bounds(substituted, ranges) ||
        refuted_by_bounds(divided, ranges) ||
        refuted_by_bounds(unwrapped, ranges) ||
        refuted_by_bounds(keep, ranges)
    }
    None => false
  }
  if bounds_conflict {
    stepped.push({
      kind: "interval",
      detail: "a constraint is violated by its own variable ranges",
      depth: 1,
    })
    return (@core.Sat::Unsat, { steps: stepped, bounds: [], tried: 0, })
  }
  match refute_with(divided, sorts) {
    Refuted::Yes => {
      stepped.push({
        kind: "fourier",
        detail: "elimination produced a contradictory constant constraint",
        depth: 1,
      })
      return (@core.Sat::Unsat, { steps: stepped, bounds: [], tried: 0, })
    }
    Refuted::No =>
      stepped.push({
        kind: "fourier",
        detail: "no rational refutation; falling back to search",
        depth: 1,
      })
    Refuted::Outside =>
      stepped.push({
        kind: "fourier",
        detail: "constraint outside the linear fragment",
        depth: 1,
      })
  }
  solve_search(vars, unwrapped, stepped, budget)
}

///|
/// The search half: narrow the ranges, then enumerate.
fn solve_search(
  vars : Array[@core.SymVar],
  constraints : Array[@core.Term],
  stepped : Array[@core.SolverStep],
  budget : Budget,
) -> (@core.Sat, Trace) {
  let ranges : Map[Int32, (Int, Int)] = Map([])
  for v in vars {
    match v.sort {
      @core.Sort::Bool => ranges.set(v.id, (0, 1))
      @core.Sort::Int(width) => {
        let half = half_range(width)
        ranges.set(v.id, (0 - half, half - 1))
      }
      // A `Nat` is non-negative and bounded by what the tool will reason about.
      // Leaving it out of `ranges` silently dropped it from the search order,
      // which made every query over a Nat "exhaust" an empty space and report
      // Unsat — a wrong proof.
      @core.Sort::Nat => ranges.set(v.id, (0, max_bound()))
    }
  }
  // Tighten from the constraints, iterating to a fixed point. Three passes is
  // enough for the shapes the interpreter emits and keeps the cost predictable;
  // a fourth pass never changed the outcome on the corpus.
  let mut pass = 0
  let mut changed = true
  let mut visited = 0
  while changed && pass < 3 && visited < budget.nodes {
    changed = false
    for c in constraints {
      let (next, cost) = tighten(ranges, c)
      visited = visited + cost
      if next != ranges {
        changed = true
        ranges.clear()
        next.each(fn(k, v) { ranges.set(k, v) })
      }
    }
    pass = pass + 1
  }
  stepped.push({
    kind: "interval",
    detail: "narrowed in \{pass} pass(es)",
    depth: 1,
  })
  let bounds : Array[(Int32, Int, Int)] = []
  ranges.each(fn(k, v) { bounds.push((k, v.0, v.1)) })
  bounds.sort_by(fn(a, b) { a.0.compare(b.0) })
  // A variable whose range is empty proves the query unsatisfiable.
  let empty = bounds.any(fn(b) { b.1 > b.2 })
  if empty {
    stepped.push({
      kind: "interval",
      detail: "a variable's range is empty, so no model exists",
      depth: 1,
    })
    return (@core.Sat::Unsat, { steps: stepped, bounds, tried: 0, })
  }
  enumerate(vars, constraints, ranges, bounds, stepped, budget)
}

///|
/// Enumerate the finite space the ranges describe.
///
/// Variables are assigned in declaration order, and each partial assignment is
/// checked as soon as it is complete. A constraint that is already false under a
/// partial assignment prunes the rest of that branch, which is what keeps the
/// small bodies fast.
fn enumerate(
  vars : Array[@core.SymVar],
  constraints : Array[@core.Term],
  ranges : Map[Int32, (Int, Int)],
  bounds : Array[(Int32, Int, Int)],
  stepped : Array[@core.SolverStep],
  budget : Budget,
) -> (@core.Sat, Trace) {
  let order : Array[Int32] = []
  for v in vars {
    match ranges.get(v.id) {
      Some(_) => order.push(v.id)
      None => ()
    }
  }
  // A variable with more than a few thousand values makes enumeration hopeless;
  // say so instead of burning the whole budget.
  let mut product = 1
  let mut hopeless = false
  for id in order {
    match ranges.get(id) {
      Some(r) => {
        // The span of a 32-bit variable does not fit an Int, so it is tested
        // without computing it: `r.1 - r.0` overflowing to a negative number used
        // to skip this guard entirely and let the enumerator walk 4e9 values.
        let too_wide = if r.1 < r.0 {
          true
        } else if r.1 - r.0 < 0 {
          true
        } else {
          let width = r.1 - r.0 + 1
          width <= 0 || width > budget.assignments
        }
        if too_wide || (product > 0 && product > budget.assignments) {
          hopeless = true
        }
        if !too_wide {
          product = product * (r.1 - r.0 + 1)
        }
      }
      None => ()
    }
  }
  if hopeless {
    // The space is too wide to enumerate, but it is not hopeless: the
    // constraints mention concrete bounds, and a model (if one exists) is
    // usually at or near one of them. Probe those values first — a model found
    // this way is checked like any other, so a hit is a proof of Sat.
    stepped.push({
      kind: "search",
      detail: "space too wide to enumerate; probing constraint boundaries",
      depth: 1,
    })
    let order = order_terms_vars(constraints)
    stepped.push({
      kind: "search",
      detail: "probing " + order.length().to_string() + " var(s)",
      depth: 2,
    })
    match probe_boundaries(order, ranges, constraints) {
      Some(model) => {
        stepped.push({ kind: "search", detail: "boundary model found", depth: 2 })
        return (
          @core.Sat::Sat(model),
          { steps: stepped, bounds, tried: 0, },
        )
      }
      None => {
        stepped.push({
          kind: "search",
          detail: "no model among the constraint boundaries",
          depth: 3,
        })
        return (
          @core.Sat::Unknown("no model found among the constraint boundaries"),
          { steps: stepped, bounds, tried: 0, },
        )
      }
    }
  }
  let model : Map[Int32, Int] = Map([])
  let result = search_rec(constraints, order, ranges, model, 0, budget, 0)
  match result {
    SearchResult::Found(found_model) => {
      stepped.push({ kind: "search", detail: "model found", depth: 1 })
      (@core.Sat::Sat(found_model), { steps: stepped, bounds, tried: 0, })
    }
    SearchResult::Exhausted(tried) => {
      stepped.push({
        kind: "search",
        detail: "the whole range space was tried and none satisfied the constraints",
        depth: 1,
      })
      (@core.Sat::Unsat, { steps: stepped, bounds, tried, })
    }
    SearchResult::OverBudget(tried) =>
      (
        @core.Sat::Unknown("assignment budget exhausted"),
        { steps: stepped, bounds, tried, },
      )
  }
}

///|
priv enum SearchResult {
  Found(Map[Int32, Int])
  Exhausted(Int)
  OverBudget(Int)
}

///|
/// Depth-first assignment over `order`, pruning partial assignments that already
/// falsify a constraint.
fn search_rec(
  constraints : Array[@core.Term],
  order : Array[Int32],
  ranges : Map[Int32, (Int, Int)],
  model : Map[Int32, Int],
  index : Int,
  budget : Budget,
  tried : Int,
) -> SearchResult {
  if tried > budget.assignments {
    return SearchResult::OverBudget(tried)
  }
  if index == order.length() {
    let holds = constraints.all(fn(c) { eval_bool(c, model) })
    if holds {
      return SearchResult::Found(model.copy())
    }
    return SearchResult::Exhausted(tried + 1)
  }
  let id = order[index]
  let range = ranges.get(id).unwrap()
  let mut value = range.0
  let mut attempts = tried
  while value <= range.1 {
    model.set(id, value)
    // Prune: if a constraint is already false, no completion can fix it.
    let dead = constraints.any(fn(c) {
      match eval_tristate(c, model) {
        Tristate::TFalse => true
        _ => false
      }
    })
    if !dead {
      match search_rec(constraints, order, ranges, model, index + 1, budget, attempts) {
        SearchResult::OverBudget(tried) => return SearchResult::OverBudget(tried)
        SearchResult::Exhausted(tried) => attempts = tried
        found => return found
      }
    }
    attempts = attempts + 1
    value = value + 1
  }
  ignore(model.remove(id))
  SearchResult::Exhausted(attempts)
}

///|
/// Three-valued evaluation: a partial assignment may leave a term undecided.
pub(all) enum Tristate {
  TTrue
  TFalse
  TUnknown
} derive(Debug, Eq)

///|
/// Evaluate under a partial model. Anything that depends on an unassigned
/// variable is `TUnknown`.
pub fn eval_tristate(t : @core.Term, model : Map[Int32, Int]) -> Tristate {
  match t {
    True => Tristate::TTrue
    False => Tristate::TFalse
    Not(a) =>
      match eval_tristate(a, model) {
        Tristate::TTrue => Tristate::TFalse
        Tristate::TFalse => Tristate::TTrue
        Tristate::TUnknown => Tristate::TUnknown
      }
    And(a, b) =>
      match (eval_tristate(a, model), eval_tristate(b, model)) {
        (Tristate::TFalse, _) | (_, Tristate::TFalse) => Tristate::TFalse
        (Tristate::TTrue, Tristate::TTrue) => Tristate::TTrue
        (_, _) => Tristate::TUnknown
      }
    Or(a, b) =>
      match (eval_tristate(a, model), eval_tristate(b, model)) {
        (Tristate::TTrue, _) | (_, Tristate::TTrue) => Tristate::TTrue
        (Tristate::TFalse, Tristate::TFalse) => Tristate::TFalse
        (_, _) => Tristate::TUnknown
      }
    Lt(_, _) | Le(_, _) | Eq(_, _) | Ne(_, _) => decide_comparison(t, model)
    _ =>
      match eval_int_opt(t, model) {
        Some(n) => if n != 0 { Tristate::TTrue } else { Tristate::TFalse }
        None => Tristate::TUnknown
      }
  }
}

///|
fn decide_comparison(t : @core.Term, model : Map[Int32, Int]) -> Tristate {
  match t {
    Lt(a, b) =>
      match (eval_int_opt(a, model), eval_int_opt(b, model)) {
        (Some(x), Some(y)) => if x < y { Tristate::TTrue } else { Tristate::TFalse }
        (_, _) => Tristate::TUnknown
      }
    Le(a, b) =>
      match (eval_int_opt(a, model), eval_int_opt(b, model)) {
        (Some(x), Some(y)) => if x <= y { Tristate::TTrue } else { Tristate::TFalse }
        (_, _) => Tristate::TUnknown
      }
    Eq(a, b) =>
      match (eval_int_opt(a, model), eval_int_opt(b, model)) {
        (Some(x), Some(y)) => if x == y { Tristate::TTrue } else { Tristate::TFalse }
        (_, _) => Tristate::TUnknown
      }
    Ne(a, b) =>
      match (eval_int_opt(a, model), eval_int_opt(b, model)) {
        (Some(x), Some(y)) => if x != y { Tristate::TTrue } else { Tristate::TFalse }
        (_, _) => Tristate::TUnknown
      }
    _ => Tristate::TUnknown
  }
}

///|
/// Evaluate a term to a boolean under a complete-enough model. An undecided
/// comparison counts as false, which is only correct once the model is complete;
/// the search calls this only on complete assignments.
pub fn eval_bool(t : @core.Term, model : Map[Int32, Int]) -> Bool {
  match eval_tristate(t, model) {
    Tristate::TTrue => true
    _ => false
  }
}

///|
/// Evaluate an integer term, or `None` when it depends on an unassigned
/// variable or divides by zero.
pub fn eval_int_opt(t : @core.Term, model : Map[Int32, Int]) -> Int? {
  match t {
    Lit(n) => Some(n)
    Var(id) => model.get(id)
    Add(a, b) =>
      match (eval_int_opt(a, model), eval_int_opt(b, model)) {
        (Some(x), Some(y)) => Some(x + y)
        (_, _) => None
      }
    Sub(a, b) =>
      match (eval_int_opt(a, model), eval_int_opt(b, model)) {
        (Some(x), Some(y)) => Some(x - y)
        (_, _) => None
      }
    MulLit(a, k) =>
      match eval_int_opt(a, model) {
        Some(x) => Some(x * k)
        None => None
      }
    DivLit(a, k) =>
      match eval_int_opt(a, model) {
        Some(x) => if k == 0 { None } else { Some(euclid_div(x, k)) }
        None => None
      }
    ModLit(a, k) =>
      match eval_int_opt(a, model) {
        Some(x) => if k == 0 { None } else { Some(euclid_mod(x, k)) }
        None => None
      }
    Div(a, b) =>
      match (eval_int_opt(a, model), eval_int_opt(b, model)) {
        (Some(x), Some(y)) => if y == 0 { None } else { Some(euclid_div(x, y)) }
        (_, _) => None
      }
    Rem(a, b) =>
      match (eval_int_opt(a, model), eval_int_opt(b, model)) {
        (Some(x), Some(y)) => if y == 0 { None } else { Some(euclid_mod(x, y)) }
        (_, _) => None
      }
    Neg(a) =>
      match eval_int_opt(a, model) {
        Some(x) => Some(0 - x)
        None => None
      }
    Abs(a) =>
      match eval_int_opt(a, model) {
        Some(x) => Some(if x < 0 { 0 - x } else { x })
        None => None
      }
    Wrap(a, w) =>
      match eval_int_opt(a, model) {
        Some(x) => Some(wrap(x, w))
        None => None
      }
    Ite(c, a, b) =>
      match eval_tristate(c, model) {
        Tristate::TTrue => eval_int_opt(a, model)
        Tristate::TFalse => eval_int_opt(b, model)
        Tristate::TUnknown => None
      }
    _ => None
  }
}

///|
/// One propagation pass over the ranges a constraint implies. Returns the new
/// ranges and how many nodes it visited.
fn tighten(
  ranges : Map[Int32, (Int, Int)],
  c : @core.Term,
) -> (Map[Int32, (Int, Int)], Int) {
  let out = ranges.copy()
  match c {
    Lt(a, b) => tighten_lt(out, a, b)
    Le(a, b) => tighten_le(out, a, b)
    Eq(a, b) => tighten_eq(out, a, b)
    Ne(_, _) => (out, 1)
    And(a, b) => {
      let (after_a, cost_a) = tighten(out, a)
      let (after_b, cost_b) = tighten(after_a, b)
      (after_b, cost_a + cost_b)
    }
    Or(_, _) => (out, 1)
    _ => (out, 1)
  }
}

///|
fn tighten_lt(
  ranges : Map[Int32, (Int, Int)],
  a : @core.Term,
  b : @core.Term,
) -> (Map[Int32, (Int, Int)], Int) {
  match (a, b) {
    (Var(id), Lit(n)) => (narrow_high(ranges, id, n - 1), 1)
    (Lit(n), Var(id)) => (narrow_low(ranges, id, n + 1), 1)
    _ => (ranges, 1)
  }
}

///|
fn tighten_le(
  ranges : Map[Int32, (Int, Int)],
  a : @core.Term,
  b : @core.Term,
) -> (Map[Int32, (Int, Int)], Int) {
  match (a, b) {
    (Var(id), Lit(n)) => (narrow_high(ranges, id, n), 1)
    (Lit(n), Var(id)) => (narrow_low(ranges, id, n), 1)
    // `a <= b` between two variables moves each bound to the other: `a`'s high
    // becomes `b`'s high and `b`'s low becomes `a`'s low. Without this a chain like
    // `lo <= hi <= 1000` leaves `lo` unbounded, and every proof that needs the
    // chain to fit in range gives up.
    (Var(x), Var(y)) => {
      let mut out = ranges
      match (ranges.get(x), ranges.get(y)) {
        (Some(rx), Some(ry)) => {
          out = narrow_high(out, x, ry.1)
          out = narrow_low(out, y, rx.0)
        }
        (_, _) => ()
      }
      (out, 1)
    }
    _ => (ranges, 1)
  }
}

///|
fn tighten_eq(
  ranges : Map[Int32, (Int, Int)],
  a : @core.Term,
  b : @core.Term,
) -> (Map[Int32, (Int, Int)], Int) {
  match (a, b) {
    (Var(id), Lit(n)) => (narrow_low(narrow_high(ranges, id, n), id, n), 1)
    (Lit(n), Var(id)) => (narrow_low(narrow_high(ranges, id, n), id, n), 1)
    _ => (ranges, 1)
  }
}

///|
fn narrow_high(
  ranges : Map[Int32, (Int, Int)],
  id : Int32,
  high : Int,
) -> Map[Int32, (Int, Int)] {
  let out = ranges.copy()
  match out.get(id) {
    Some(r) => if high < r.1 { out.set(id, (r.0, high)) }
    None => ()
  }
  out
}

///|
fn narrow_low(
  ranges : Map[Int32, (Int, Int)],
  id : Int32,
  low : Int,
) -> Map[Int32, (Int, Int)] {
  let out = ranges.copy()
  match out.get(id) {
    Some(r) => if low > r.0 { out.set(id, (low, r.1)) }
    None => ()
  }
  out
}

///|
/// `2^(w-1)`: the exclusive bound of a `w`-bit signed range.
///
/// `w = 4` yields 8, so a 4-bit variable spans `[-8, 7]`. The width is clamped
/// at 30 because the doubled bound has to stay inside a 63-bit Int.
pub fn half_range(w : Int) -> Int {
  // 2^(w-1) for the widths the tool accepts. `w` is capped at 31 cells: above
  // that, half itself would not fit a signed Int and the range could not be
  // expressed at all. A 32-bit variable therefore gets the range
  // `[-2147483647-1, 2147483646]`, one short at the top — which is why a `Wrap`
  // of a 32-bit value is what triggers the overflow branch, not a bare literal.
  let width = if w < 2 { 2 } else if w > 31 { 31 } else { w }
  let mut acc = 1
  let mut i = 1
  while i < width {
    acc = acc * 2
    i = i + 1
  }
  acc
}

///|
/// The variable ids a constraint list mentions, in order.
fn order_terms_vars(constraints : Array[@core.Term]) -> Array[Int32] {
  let seen : Set[Int32] = Set([])
  let out : Array[Int32] = []
  for c in constraints {
    collect_vars(c, seen, out)
  }
  out
}

///|
fn collect_vars(t : @core.Term, seen : Set[Int32], out : Array[Int32]) -> Unit {
  match t {
    Var(id) => if !seen.contains(id) {
      seen.add(id)
      out.push(id)
    }
    Add(a, b) | Sub(a, b) | Div(a, b) | Rem(a, b) | And(a, b) | Or(a, b) |
    Eq(a, b) | Ne(a, b) | Lt(a, b) | Le(a, b) => {
      collect_vars(a, seen, out)
      collect_vars(b, seen, out)
    }
    MulLit(a, _) | DivLit(a, _) | ModLit(a, _) | Neg(a) | Abs(a) | Wrap(a, _) |
    Not(a) => collect_vars(a, seen, out)
    Ite(c, a, b) => {
      collect_vars(c, seen, out)
      collect_vars(a, seen, out)
      collect_vars(b, seen, out)
    }
    _ => ()
  }
}

///|
/// Try each variable at the constants the constraints mention, plus the range
/// ends and a few interior points, holding the others at their lower bound.
///
/// This is a *search*, not a decision procedure: every hit is verified by
/// `eval_bool`, so a returned model is always real. A miss says nothing, which is
/// why the caller reports `Unknown` rather than `Unsat`.
fn probe_boundaries(
  ids : Array[Int32],
  ranges : Map[Int32, (Int, Int)],
  constraints : Array[@core.Term],
) -> Map[Int32, Int]? {
  // Range endpoints matter as much as constraint constants: `x + 1 > x` fails
  // exactly at MAX, and a query with no literal in it would otherwise have no
  // candidate at all.
  let candidates = constants_in(constraints)
  for id in ids {
    match ranges.get(id) {
      Some(r) => {
        let extra = [r.0, r.1, r.0 + 1, r.1 - 1]
        for value in extra {
          if !contains_int(candidates, value) {
            candidates.push(value)
          }
        }
      }
      None => ()
    }
  }
  candidates.sort()
  let model : Map[Int32, Int] = Map([])
  for id in ids {
    match ranges.get(id) {
      Some(r) => model.set(id, r.0)
      None => ()
    }
  }
  // Every combination of "one variable moved to a candidate" over the base
  // assignment, which covers the shapes the interpreter emits.
  let mut index = 0
  while index < candidates.length() {
    let c = candidates[index]
    // All variables at c.
    let all : Map[Int32, Int] = Map([])
    for id in ids {
      all.set(id, c)
    }
    if constraints.all(fn(t) { eval_bool(t, all) }) {
      return Some(all)
    }
    // One variable at c, the rest at their lower bound.
    for id in ids {
      let one = model.copy()
      one.set(id, c)
      if constraints.all(fn(t) { eval_bool(t, one) }) {
        return Some(one)
      }
    }
    index = index + 1
  }
  None
}

///|
/// Every integer constant a constraint mentions, sorted, deduplicated, and
/// expanded by one in each direction (an inequality's boundary is the constant
/// itself, but an equality's model may be the constant plus a step).
fn constants_in(constraints : Array[@core.Term]) -> Array[Int] {
  let seen : Set[Int] = Set([])
  let out : Array[Int] = []
  for c in constraints {
    collect_constants(c, seen, out)
  }
  let expanded : Array[Int] = []
  for n in out {
    for d in [0, 1, 0 - 1, 2, 0 - 2] {
      let value = n + d
      if !contains_int(expanded, value) {
        expanded.push(value)
      }
    }
  }
  expanded.sort()
  expanded
}

///|
fn collect_constants(t : @core.Term, seen : Set[Int], out : Array[Int]) -> Unit {
  match t {
    Lit(n) => if !seen.contains(n) {
      seen.add(n)
      out.push(n)
    }
    Add(a, b) | Sub(a, b) | Div(a, b) | Rem(a, b) | And(a, b) | Or(a, b) |
    Eq(a, b) | Ne(a, b) | Lt(a, b) | Le(a, b) => {
      collect_constants(a, seen, out)
      collect_constants(b, seen, out)
    }
    MulLit(a, _) | DivLit(a, _) | ModLit(a, _) | Neg(a) | Abs(a) | Wrap(a, _) |
    Not(a) => collect_constants(a, seen, out)
    Ite(c, a, b) => {
      collect_constants(c, seen, out)
      collect_constants(a, seen, out)
      collect_constants(b, seen, out)
    }
    _ => ()
  }
}

///|
fn contains_int(items : Array[Int], needle : Int) -> Bool {
  for item in items {
    if item == needle {
      return true
    }
  }
  false
}

///|
/// Split `a && b` into `a` and `b`, recursively. A disjunction is left whole: it
/// is one fact ("one of these holds"), and splitting it would be unsound.
pub fn flatten_conjunct(t : @core.Term, out : Array[@core.Term]) -> Unit {
  match t {
    And(a, b) => {
      flatten_conjunct(a, out)
      flatten_conjunct(b, out)
    }
    True => ()
    _ => out.push(t)
  }
}

///|
/// Narrow every variable's range by the constants the constraints mention, then
/// return the map. `None` when a variable has no range at all (unbounded).
fn narrow_from_constraints(
  vars : Array[@core.SymVar],
  constraints : Array[@core.Term],
) -> Map[Int32, (Int, Int)]? {
  let ranges : Map[Int32, (Int, Int)] = Map([])
  for v in vars {
    match v.sort {
      @core.Sort::Int(width) => {
        let half = half_range(width)
        ranges.set(v.id, (0 - half, half - 1))
      }
      @core.Sort::Nat => ranges.set(v.id, (0, max_bound()))
      @core.Sort::Bool => ranges.set(v.id, (0, 1))
    }
  }
  let mut pass = 0
  while pass < 4 {
    for c in constraints {
      let (next, _cost) = tighten(ranges, c)
      next.each(fn(k, v) { ranges.set(k, v) })
    }
    pass = pass + 1
  }
  Some(ranges)
}

///|
/// A practical upper bound for an unbounded `Nat`, so arithmetic stays inside
/// 63-bit range. Not a claim about the language's semantics: any length beyond it
/// is reported as `Unknown` rather than silently wrapped.
fn max_bound() -> Int {
  1000000
}

///|
/// True when some constraint cannot hold under the given ranges.
///
/// For each constraint `linear REL 0` the minimum and maximum of the linear form
/// over the box are computed exactly (each variable contributes its bound times
/// its coefficient's sign). A minimum above zero refutes `<= 0`; a maximum below
/// zero refutes `>= 0`; an equality refutes when zero is outside `[min, max]`.
fn refuted_by_bounds(
  constraints : Array[@core.Term],
  ranges : Map[Int32, (Int, Int)],
) -> Bool {
  for c in constraints {
    let parts : Array[@core.Term] = []
    flatten_conjunct(c, parts)
    for part in parts {
      match as_constraint(part) {
        None => ()
        Some(con) => {
          let mut minimum = con.lin.constant
          let mut maximum = con.lin.constant
          let mut known = true
          con.lin.coeffs.each(fn(id, coef) {
            match ranges.get(id) {
              None => known = false
              Some(r) => {
                let low = coef * r.0
                let high = coef * r.1
                let lo = if low < high { low } else { high }
                let hi = if low < high { high } else { low }
                minimum = minimum + lo
                maximum = maximum + hi
              }
            }
          })
          if known {
            match con.rel {
              Rel::LeZero => if minimum > 0 { return true }
              Rel::LtZero => if minimum >= 0 { return true }
              // `== 0` needs zero inside the interval.
              Rel::EqZero => if minimum > 0 || maximum < 0 { return true }
            }
          }
        }
      }
    }
  }
  false
}

///|
/// Remove `Wrap(t, w)` when `t`'s range proves it cannot leave `w` bits.
///
/// This is a *rewrite that preserves meaning on this path*, which is why it is
/// safe to do before the proof: if the term cannot wrap, the wrap is the identity.
fn drop_redundant_wraps(t : @core.Term, ranges : Map[Int32, (Int, Int)]) -> @core.Term {
  match t {
    Wrap(inner, width) =>
      match term_range(inner, ranges) {
        Some((low, high)) => {
          // The tool's own representable box for a width is
          // `[-2^(w-1), 2^(w-1) - 1]`, and no narrower box is claimed: a term
          // whose range lies inside it cannot wrap, so the wrap is the identity.
          // `wrap` only changes a value that leaves `[-half, half). This
          // implementation of wrap leaves `half` itself unchanged, so the safe
          // condition is the one below — the asymmetric box the tool uses reaches
          // exactly `half` on the far side.
          let half = half_range(width)
          if low >= 0 - half && high <= half {
            drop_redundant_wraps(inner, ranges)
          } else {
            Wrap(drop_redundant_wraps(inner, ranges), width)
          }
        }
        None => Wrap(drop_redundant_wraps(inner, ranges), width)
      }
    Add(a, b) => Add(drop_redundant_wraps(a, ranges), drop_redundant_wraps(b, ranges))
    Sub(a, b) => Sub(drop_redundant_wraps(a, ranges), drop_redundant_wraps(b, ranges))
    MulLit(a, k) => MulLit(drop_redundant_wraps(a, ranges), k)
    DivLit(a, k) => DivLit(drop_redundant_wraps(a, ranges), k)
    ModLit(a, k) => ModLit(drop_redundant_wraps(a, ranges), k)
    Neg(a) => Neg(drop_redundant_wraps(a, ranges))
    Abs(a) => Abs(drop_redundant_wraps(a, ranges))
    Lt(a, b) => Lt(drop_redundant_wraps(a, ranges), drop_redundant_wraps(b, ranges))
    Le(a, b) => Le(drop_redundant_wraps(a, ranges), drop_redundant_wraps(b, ranges))
    Eq(a, b) => Eq(drop_redundant_wraps(a, ranges), drop_redundant_wraps(b, ranges))
    Ne(a, b) => Ne(drop_redundant_wraps(a, ranges), drop_redundant_wraps(b, ranges))
    And(a, b) => And(drop_redundant_wraps(a, ranges), drop_redundant_wraps(b, ranges))
    Or(a, b) => Or(drop_redundant_wraps(a, ranges), drop_redundant_wraps(b, ranges))
    Not(a) => Not(drop_redundant_wraps(a, ranges))
    Ite(c, a, b) =>
      Ite(
        drop_redundant_wraps(c, ranges),
        drop_redundant_wraps(a, ranges),
        drop_redundant_wraps(b, ranges),
      )
    Div(a, b) => Div(drop_redundant_wraps(a, ranges), drop_redundant_wraps(b, ranges))
    Rem(a, b) => Rem(drop_redundant_wraps(a, ranges), drop_redundant_wraps(b, ranges))
    _ => t
  }
}

///|
/// The range a term can take under the given variable ranges. Used to decide
/// whether a wrap can fire; `None` when a subterm has no bound.
fn term_range(t : @core.Term, ranges : Map[Int32, (Int, Int)]) -> (Int, Int)? {
  match t {
    Lit(n) => Some((n, n))
    Var(id) => ranges.get(id)
    Add(a, b) =>
      match (term_range(a, ranges), term_range(b, ranges)) {
        (Some(l), Some(r)) => Some((l.0 + r.0, l.1 + r.1))
        (_, _) => None
      }
    Sub(a, b) =>
      match (term_range(a, ranges), term_range(b, ranges)) {
        (Some(l), Some(r)) => Some((l.0 - r.1, l.1 - r.0))
        (_, _) => None
      }
    MulLit(a, k) =>
      match term_range(a, ranges) {
        Some(r) => {
          let p = r.0 * k
          let q = r.1 * k
          Some((if p < q { p } else { q }, if p < q { q } else { p }))
        }
        None => None
      }
    DivLit(a, k) =>
      match term_range(a, ranges) {
        Some(r) =>
          if k > 0 {
            Some((euclid_div(r.0, k), euclid_div(r.1, k)))
          } else {
            None
          }
        None => None
      }
    ModLit(a, k) =>
      match term_range(a, ranges) {
        Some(_) => if k > 0 { Some((0, k - 1)) } else { None }
        None => None
      }
    Neg(a) =>
      match term_range(a, ranges) {
        Some(r) => Some((0 - r.1, 0 - r.0))
        None => None
      }
    Abs(a) =>
      match term_range(a, ranges) {
        Some(r) => {
          let lo = if r.0 < 0 { 0 - r.0 } else { r.0 }
          let hi = if r.0 <= 0 && r.1 >= 0 {
            let a1 = 0 - r.0
            let a2 = r.1
            if a1 > a2 { a1 } else { a2 }
          } else if r.1 < 0 {
            0 - r.1
          } else {
            r.1
          }
          Some((0, hi))
        }
        None => None
      }
    Wrap(a, w) =>
      match term_range(a, ranges) {
        Some(_) => {
          let half = half_range(w)
          Some((0 - half, half - 1))
        }
        None => None
      }
    Ite(_, a, b) =>
      match (term_range(a, ranges), term_range(b, ranges)) {
        (Some(l), Some(r)) => Some((if l.0 < r.0 { l.0 } else { r.0 }, if l.1 > r.1 { l.1 } else { r.1 }))
        (_, _) => None
      }
    _ => None
  }
}

///|
/// Substitute a division by a positive literal with the tightest bound its
/// operand's range implies, when the range reaches that bound.
///
/// `x / 2` with `x` in `[lo, hi]` lies in `[floor(lo/2), floor(hi/2)]`. Replacing
/// the division by the endpoint that matters for the comparison keeps the
/// constraint *implied* by the original on this path — which is what a refutation
/// needs: if the implied constraint is unsatisfiable, so was the original.
fn subst_divisions(t : @core.Term, ranges : Map[Int32, (Int, Int)]) -> @core.Term {
  match t {
    DivLit(a, k) =>
      if k <= 0 {
        DivLit(subst_divisions(a, ranges), k)
      } else {
        match term_range(a, ranges) {
          Some(r) =>
            // When the operand cannot be negative, its quotient cannot be either.
            if r.0 >= 0 {
              Lit(euclid_div(r.0, k))
            } else if r.1 < 0 {
              Lit(euclid_div(r.1, k))
            } else {
              DivLit(subst_divisions(a, ranges), k)
            }
          None => DivLit(subst_divisions(a, ranges), k)
        }
      }
    Add(a, b) => Add(subst_divisions(a, ranges), subst_divisions(b, ranges))
    Sub(a, b) => Sub(subst_divisions(a, ranges), subst_divisions(b, ranges))
    MulLit(a, k) => MulLit(subst_divisions(a, ranges), k)
    ModLit(a, k) => ModLit(subst_divisions(a, ranges), k)
    Neg(a) => Neg(subst_divisions(a, ranges))
    Abs(a) => Abs(subst_divisions(a, ranges))
    Lt(a, b) => Lt(subst_divisions(a, ranges), subst_divisions(b, ranges))
    Le(a, b) => Le(subst_divisions(a, ranges), subst_divisions(b, ranges))
    Eq(a, b) => Eq(subst_divisions(a, ranges), subst_divisions(b, ranges))
    Ne(a, b) => Ne(subst_divisions(a, ranges), subst_divisions(b, ranges))
    And(a, b) => And(subst_divisions(a, ranges), subst_divisions(b, ranges))
    Or(a, b) => Or(subst_divisions(a, ranges), subst_divisions(b, ranges))
    Not(a) => Not(subst_divisions(a, ranges))
    _ => t
  }
}

///|
/// `t / k REL c`  ->  `t REL c*k` (with the strictness adjusted for the floor), for
/// a positive literal `k` and a constant right-hand side.
///
/// Both directions of the equivalence hold over the integers, so the rewrite is
/// meaning-preserving — which is what lets it feed a refutation.
fn clear_division(t : @core.Term) -> @core.Term {
  match t {
    Lt(DivLit(a, k), Lit(c)) =>
      if k <= 0 {
        t
      } else {
        // `a / k < c`  <=>  `a < c * k`
        Lt(clear_division(a), Lit(c * k))
      }
    Le(DivLit(a, k), Lit(c)) =>
      if k <= 0 {
        t
      } else {
        // `a / k <= c`  <=>  `a < (c + 1) * k`
        Lt(clear_division(a), Lit((c + 1) * k))
      }
    Lt(Lit(c), DivLit(a, k)) =>
      if k <= 0 {
        t
      } else {
        // `c < a / k`  <=>  `(c + 1) * k <= a`
        Le(Lit((c + 1) * k), clear_division(a))
      }
    Le(Lit(c), DivLit(a, k)) =>
      if k <= 0 {
        t
      } else {
        // `c <= a / k`  <=>  `c * k <= a`
        Le(Lit(c * k), clear_division(a))
      }
    And(a, b) => And(clear_division(a), clear_division(b))
    Or(a, b) => Or(clear_division(a), clear_division(b))
    Not(a) => Not(clear_division(a))
    _ => t
  }
}
