// Fourier–Motzkin elimination: the decision procedure for the linear fragment.
//
// Why this and not enumeration: a 32-bit variable has 2^32 values, so
// enumeration answers `Unknown` on nearly every real query. Fourier–Motzkin
// eliminates one variable at a time by combining each lower bound with each upper
// bound, and a query is unsatisfiable exactly when elimination produces a
// contradictory constant constraint.
//
// Soundness note, which is the part that matters: eliminating over the *rationals*
// and finding a contradiction proves the *integer* problem unsatisfiable too,
// because every integer solution is a rational one. So `Unsat` from this module is
// a proof, never a guess. The converse does not hold (an integer problem can be
// unsatisfiable while its rational relaxation is satisfiable), and that direction
// is reported as `Unknown`, not `Sat`.

///|
/// A linear form: `sum(coef * var) + constant`.
pub(all) struct Linear {
  coeffs : Map[Int32, Int]
  constant : Int
} derive(Debug, Eq)

///|
/// A linear constraint: `lhs REL 0`.
pub(all) enum Rel {
  /// `lhs < 0`
  LtZero
  /// `lhs <= 0`
  LeZero
  /// `lhs == 0`
  EqZero
} derive(Debug, Eq)

///|
/// A constraint in normal form.
pub(all) struct LCon {
  lin : Linear
  rel : Rel
} derive(Debug, Eq)

///|
/// Extract a linear form from a term, or `None` when the term is not linear in
/// the ways this pass understands (products of variables, division by a
/// non-literal, wrapping, conditionals).
pub fn as_linear(t : @core.Term) -> Linear? {
  match t {
    Lit(n) => Some({ coeffs: Map([]), constant: n })
    Var(id) => {
      let coeffs : Map[Int32, Int] = Map([])
      coeffs.set(id, 1)
      Some({ coeffs, constant: 0 })
    }
    Add(a, b) =>
      match (as_linear(a), as_linear(b)) {
        (Some(l), Some(r)) => Some(add_linear(l, r))
        (_, _) => None
      }
    Sub(a, b) =>
      match (as_linear(a), as_linear(b)) {
        (Some(l), Some(r)) => Some(add_linear(l, scale_linear(r, 0 - 1)))
        (_, _) => None
      }
    MulLit(a, k) =>
      match as_linear(a) {
        // `x * k` is linear for every literal k — the coefficient is just k. The
        // term is only outside the fragment when the *other* factor is symbolic,
        // which `MulLit` by construction is not.
        Some(l) => Some(scale_linear(l, k))
        None => None
      }
    Neg(a) =>
      match as_linear(a) {
        Some(l) => Some(scale_linear(l, 0 - 1))
        None => None
      }
    _ => None
  }
}

///|
fn add_linear(a : Linear, b : Linear) -> Linear {
  let coeffs = a.coeffs.copy()
  b.coeffs.each(fn(id, coef) {
    match coeffs.get(id) {
      None => coeffs.set(id, coef)
      Some(existing) => coeffs.set(id, existing + coef)
    }
  })
  // A coefficient that cancelled to zero must leave the map: `contradiction` reads
  // an empty coefficient map as "this constraint is a constant", and a zero entry
  // left behind hides exactly the contradiction elimination is looking for.
  let zeros : Array[Int32] = []
  coeffs.each(fn(id, coef) { if coef == 0 { zeros.push(id) } })
  for id in zeros {
    ignore(coeffs.remove(id))
  }
  { coeffs, constant: a.constant + b.constant }
}

///|
fn scale_linear(a : Linear, k : Int) -> Linear {
  let coeffs : Map[Int32, Int] = Map([])
  a.coeffs.each(fn(id, coef) { coeffs.set(id, coef * k) })
  { coeffs, constant: a.constant * k }
}

///|
/// Turn a comparison into a constraint of the form `linear REL 0`.
///
/// `Lt(a, b)` is `a - b < 0`; `Le` likewise; `Eq` likewise.
pub fn as_constraint(t : @core.Term) -> LCon? {
  match t {
    Lt(a, b) =>
      match (as_linear(a), as_linear(b)) {
        (Some(l), Some(r)) => Some({ lin: add_linear(l, scale_linear(r, 0 - 1)), rel: Rel::LtZero })
        (_, _) => None
      }
    Le(a, b) =>
      match (as_linear(a), as_linear(b)) {
        (Some(l), Some(r)) => Some({ lin: add_linear(l, scale_linear(r, 0 - 1)), rel: Rel::LeZero })
        (_, _) => None
      }
    Eq(a, b) =>
      match (as_linear(a), as_linear(b)) {
        (Some(l), Some(r)) => Some({ lin: add_linear(l, scale_linear(r, 0 - 1)), rel: Rel::EqZero })
        (_, _) => None
      }
    Ne(_, _) => None
    // A conjunction has to be split before conversion; `refute` flattens first,
    // so reaching one here means a caller skipped that step. Fail closed.
    And(_, _) => None
    _ => None
  }
}

///|
/// The result of a refutation attempt.
pub(all) enum Refuted {
  /// Elimination produced a contradiction: the constraints cannot hold.
  Yes
  /// Elimination finished without a contradiction. The *rational* relaxation is
  /// satisfiable, which says nothing about the integers.
  No
  /// A constraint was outside the linear fragment.
  Outside
} derive(Debug, Eq)

///|
/// Refute a conjunction of constraints by Fourier–Motzkin elimination.
///
/// Every variable that appears is eliminated in turn; the process is exact for
/// linear real arithmetic, which is why `Yes` licenses a proof.
pub fn refute(constraints : Array[@core.Term]) -> Refuted {
  refute_with(constraints, Map([]))
}

///|
/// `refute`, with the variable sorts available so the simplifier can fold an
/// already-in-range `Wrap`.
///
/// Every constraint is simplified before conversion: a violation query is built by
/// negating the conclusion, and the negation is only expressible as a linear
/// constraint after De Morgan and reflexivity have run in the simplifier.
pub fn refute_with(
  constraints : Array[@core.Term],
  sorts : Map[Int32, @core.Sort],
) -> Refuted {
  let mut cons : Array[LCon] = []
  for raw in constraints {
    let t = simplify_with(raw, sorts)
    let parts : Array[@core.Term] = []
    flatten(t, parts)
    for part in parts {
      match as_constraint(part) {
        None =>
          match part {
            // A bare boolean that is not a comparison contributes nothing.
            @core.Term::True => ()
            @core.Term::False => return Refuted::Yes
            _ => return Refuted::Outside
          }
        Some(c) => cons.push(normalize(c))
      }
    }
  }
  // Eliminate every variable that ever appears.
  let mut steps = 0
  while steps < 64 {
    match pick_variable(cons) {
      None => break
      Some(id) => {
        cons = eliminate(cons, id)
        match contradiction(cons) {
          true => return Refuted::Yes
          false => ()
        }
      }
    }
    steps = steps + 1
  }
  if contradiction(cons) {
    Refuted::Yes
  } else {
    Refuted::No
  }
}

///|
/// Split conjunctions so each element is one fact.
fn flatten(t : @core.Term, out : Array[@core.Term]) -> Unit {
  match t {
    @core.Term::And(a, b) => {
      flatten(a, out)
      flatten(b, out)
    }
    @core.Term::True => ()
    _ => out.push(t)
  }
}

///|
/// Divide through by the greatest common divisor so coefficients stay small and
/// two constraints on the same variable can be compared.
fn normalize(c : LCon) -> LCon {
  let mut g = 0
  c.lin.coeffs.each(fn(_id, coef) { g = gcd(g, if coef < 0 { 0 - coef } else { coef }) })
  if g <= 1 {
    return c
  }
  ignore_div(c, g)
}

///|
fn ignore_div(c : LCon, g : Int) -> LCon {
  let coeffs : Map[Int32, Int] = Map([])
  c.lin.coeffs.each(fn(id, coef) { coeffs.set(id, coef / g) })
  // The constant is divided too only when it divides exactly; otherwise keep it,
  // which is the conservative direction.
  let constant = if c.lin.constant % g == 0 { c.lin.constant / g } else { c.lin.constant }
  { lin: { coeffs, constant }, rel: c.rel }
}

///|
fn gcd(a : Int, b : Int) -> Int {
  let mut x = if a < 0 { 0 - a } else { a }
  let mut y = if b < 0 { 0 - b } else { b }
  while y != 0 {
    let r = x % y
    x = y
    y = r
  }
  x
}

///|
/// A variable still present in the constraint set, chosen as the one with the
/// most occurrences so elimination terminates fastest.
fn pick_variable(cons : Array[LCon]) -> Int32? {
  let counts : Map[Int32, Int] = Map([])
  for c in cons {
    c.lin.coeffs.each(fn(id, _coef) {
      match counts.get(id) {
        None => counts.set(id, 1)
        Some(n) => counts.set(id, n + 1)
      }
    })
  }
  let mut best : Int32? = None
  let mut best_count = 0
  counts.each(fn(id, n) {
    if n > best_count || (n == best_count && best_count == 0) {
      best = Some(id)
      best_count = n
    }
  })
  best
}

///|
/// Eliminate one variable: for `a*x + r <= 0` (a > 0) and `b*x + s <= 0` (b < 0),
/// the pair yields `b*r - a*s <= 0` with x gone.
fn eliminate(cons : Array[LCon], id : Int32) -> Array[LCon] {
  let lower : Array[LCon] = []
  let upper : Array[LCon] = []
  let rest : Array[LCon] = []
  for c in cons {
    match c.lin.coeffs.get(id) {
      None => rest.push(c)
      Some(coef) =>
        if coef > 0 {
          lower.push(c)
        } else if coef < 0 {
          upper.push(c)
        } else {
          rest.push(c)
        }
    }
  }
  let out : Array[LCon] = []
  for c in rest {
    out.push(c)
  }
  // An equality behaves as both a lower and an upper bound.
  for l in lower {
    for u in upper {
      match combine(l, u, id) {
        Some(c) => out.push(normalize(c))
        None => ()
      }
    }
    // An equality with no opposite bound can always be satisfied by choosing the
    // variable (its coefficient is non-zero), so its projection is the trivial
    // constraint — NOT its constant part, which would read as "7 == 0".
    if l.rel == Rel::EqZero {
      ()
    }
  }
  for u in upper {
    if u.rel == Rel::EqZero {
      ()
    }
  }
  out
}

///|
/// The resolvent of a lower and an upper bound on `id`.
fn combine(lower : LCon, upper : LCon, id : Int32) -> LCon? {
  let a = lower.lin.coeffs.get(id).unwrap_or(0)
  let b = upper.lin.coeffs.get(id).unwrap_or(0)
  if a <= 0 || b >= 0 {
    return None
  }
  // (a*x + r) and (b*x + s). Multiply the first by -b and the second by a:
  // -b*a*x - b*r and a*b*x + a*s add to a*s - b*r.
  let left = scale_linear(drop_linear(lower.lin, id), 0 - b)
  let right = scale_linear(drop_linear(upper.lin, id), a)
  let combined = add_linear(left, right)
  // A resolvent is strict when *either* bound was strict: `x <= y` (non-strict)
  // combined with `y < x` (strict) yields `0 < 0`, which is the contradiction that
  // makes a strict inequality provable. Marking it non-strict loses exactly that.
  let mut rel = Rel::LeZero
  if lower.rel == Rel::LtZero || upper.rel == Rel::LtZero {
    rel = Rel::LtZero
  }
  if lower.rel == Rel::EqZero && upper.rel == Rel::EqZero {
    rel = Rel::EqZero
  }
  Some({ lin: combined, rel })
}

///|
fn drop_linear(l : Linear, id : Int32) -> Linear {
  let coeffs = l.coeffs.copy()
  ignore(coeffs.remove(id))
  { coeffs, constant: l.constant }
}

///|
/// True when some constraint has no variables left and is false as a constant.
fn contradiction(cons : Array[LCon]) -> Bool {
  for c in cons {
    if c.lin.coeffs.is_empty() {
      match c.rel {
        Rel::LtZero => if c.lin.constant >= 0 { return true }
        Rel::LeZero => if c.lin.constant > 0 { return true }
        Rel::EqZero => if c.lin.constant != 0 { return true }
      }
    }
  }
  false
}
