// Term simplification: the rewrite rules that run before any search.
//
// A verifier's credibility rests on its solver answering *exactly*. Simplifying
// a term must therefore never change its meaning — every rule below is an
// identity over the integers, and the tests pin each one against a brute-force
// evaluation.

///|
/// Fold every constant subterm and apply the algebraic identities that hold for
/// all integers. Returns a term in which no `Add`/`Sub`/`MulLit` has two
/// literals for children and no neutral element remains.
pub fn simplify(t : @core.Term) -> @core.Term {
  simplify_with(t, Map([]))
}

///|
/// Simplify with the sorts of the symbolic variables in hand.
///
/// The sorts matter: a variable of sort `Int(32)` already lies in a 32-bit range,
/// so `wrap(x, 32)` *is* `x`. Without this rule every arithmetic assertion at a
/// declared width looks like it needs a 32-bit search, which no enumeration can
/// do — and the tool would answer `Unknown` on statements a reader can check by
/// eye.
pub fn simplify_with(
  t : @core.Term,
  sorts : Map[Int32, @core.Sort],
) -> @core.Term {
  match t {
    Lit(_) | Var(_) | True | False => t
    Add(a, b) => {
      let x = simplify_with(a, sorts)
      let y = simplify_with(b, sorts)
      match (x, y) {
        (Lit(0), other) => other
        (other, Lit(0)) => other
        (Lit(m), Lit(n)) => lit(m + n)
        (_, _) => Add(x, y)
      }
    }
    Sub(a, b) => {
      let x = simplify_with(a, sorts)
      let y = simplify_with(b, sorts)
      match (x, y) {
        (other, Lit(0)) => other
        (Lit(m), Lit(n)) => lit(m - n)
        (_, Lit(n)) => Add(x, Lit(0 - n))
        (_, _) => Sub(x, y)
      }
    }
    MulLit(a, k) => {
      let x = simplify_with(a, sorts)
      match x {
        Lit(m) => lit(m * k)
        _ =>
          if k == 0 {
            Lit(0)
          } else if k == 1 {
            x
          } else {
            MulLit(x, k)
          }
      }
    }
    DivLit(a, k) => {
      let x = simplify_with(a, sorts)
      match x {
        Lit(m) => lit(euclid_div(m, k))
        _ => if k == 1 { x } else { DivLit(x, k) }
      }
    }
    ModLit(a, k) => {
      let x = simplify_with(a, sorts)
      match x {
        Lit(m) => lit(euclid_mod(m, k))
        _ =>
          if k == 1 {
            Lit(0)
          } else {
            ModLit(x, k)
          }
      }
    }
    Div(a, b) => {
      let x = simplify_with(a, sorts)
      let y = simplify_with(b, sorts)
      match (x, y) {
        (Lit(m), Lit(n)) => if n == 0 { Lit(0) } else { lit(euclid_div(m, n)) }
        (_, Lit(1)) => x
        (_, _) => Div(x, y)
      }
    }
    Rem(a, b) => {
      let x = simplify_with(a, sorts)
      let y = simplify_with(b, sorts)
      match (x, y) {
        (Lit(m), Lit(n)) => if n == 0 { Lit(0) } else { lit(euclid_mod(m, n)) }
        (_, Lit(1)) => Lit(0)
        (_, _) => Rem(x, y)
      }
    }
    Neg(a) => {
      let x = simplify_with(a, sorts)
      match x {
        Lit(m) => lit(0 - m)
        Neg(inner) => inner
        _ => Neg(x)
      }
    }
    Abs(a) => {
      let x = simplify_with(a, sorts)
      match x {
        Lit(m) => lit(if m < 0 { 0 - m } else { m })
        Neg(inner) => Abs(inner)
        _ => Abs(x)
      }
    }
    Wrap(a, w) => {
      let x = simplify_with(a, sorts)
      match x {
        Lit(m) => lit(wrap(m, w))
        Var(id) =>
          // The variable already ranges over its sort's width.
          match sorts.get(id) {
            Some(@core.Sort::Int(bits)) => if bits == w { x } else { Wrap(x, w) }
            _ => Wrap(x, w)
          }
        _ => Wrap(x, w)
      }
    }
    Ite(c, a, b) => {
      let p = simplify_with(c, sorts)
      let x = simplify_with(a, sorts)
      let y = simplify_with(b, sorts)
      match p {
        True => x
        False => y
        _ =>
          if x == y {
            x
          } else {
            Ite(p, x, y)
          }
      }
    }
    Lt(a, b) => cmp_term(simplify_with(a, sorts), simplify_with(b, sorts), CompareOp::Lt)
    Le(a, b) => cmp_term(simplify_with(a, sorts), simplify_with(b, sorts), CompareOp::Le)
    Eq(a, b) => cmp_term(simplify_with(a, sorts), simplify_with(b, sorts), CompareOp::Eq)
    Ne(a, b) => {
      match cmp_term(simplify_with(a, sorts), simplify_with(b, sorts), CompareOp::Eq) {
        True => False
        False => True
        other => Not(other)
      }
    }
    Not(a) => {
      let x = simplify_with(a, sorts)
      match x {
        True => False
        False => True
        Not(inner) => inner
        // De Morgan, then push onto the comparison: the narrowing pass understands
        // `Le(Lit(n), Var)` but not `Not(Lt(Var, Lit))`, and a violation query is
        // built by negating the conclusion.
        And(p, q) => simplify_with(Or(Not(p), Not(q)), sorts)
        Or(p, q) => simplify_with(And(Not(p), Not(q)), sorts)
        Lt(p, q) => simplify_with(Le(q, p), sorts)
        Le(p, q) => simplify_with(Lt(q, p), sorts)
        Eq(p, q) => simplify_with(Ne(p, q), sorts)
        Ne(p, q) => simplify_with(Eq(p, q), sorts)
        _ => Not(x)
      }
    }
    And(a, b) => {
      let x = simplify_with(a, sorts)
      let y = simplify_with(b, sorts)
      match (x, y) {
        (False, _) | (_, False) => False
        (True, other) | (other, True) => other
        (_, _) => if x == y { x } else { And(x, y) }
      }
    }
    Or(a, b) => {
      let x = simplify_with(a, sorts)
      let y = simplify_with(b, sorts)
      match (x, y) {
        (True, _) | (_, True) => True
        (False, other) | (other, False) => other
        (_, _) => if x == y { x } else { Or(x, y) }
      }
    }
  }
}

///|
priv enum CompareOp {
  Lt
  Le
  Eq
}

///|
fn cmp_term(a : @core.Term, b : @core.Term, op : CompareOp) -> @core.Term {
  match (a, b) {
    (Lit(m), Lit(n)) => {
      let holds = match op {
        CompareOp::Lt => m < n
        CompareOp::Le => m <= n
        CompareOp::Eq => m == n
      }
      if holds {
        True
      } else {
        False
      }
    }
    (_, _) =>
      match op {
        // `x < x` is false and `x <= x` is true for every value: a rule that
        // costs nothing and decides the most common shape of a wrong assertion.
        CompareOp::Lt => if a == b { False } else { Lt(a, b) }
        CompareOp::Le => if a == b { True } else { Le(a, b) }
        CompareOp::Eq => if a == b { True } else { Eq(a, b) }
      }
  }
}

///|
/// A literal term, written without `Lit(...)` noise at the call sites above.
fn lit(n : Int) -> @core.Term {
  Lit(n)
}

///|
/// Euclidean division: rounds toward negative infinity, so the remainder is
/// always non-negative. This is the semantics MoonBit's integer division and
/// modulo have, and the one a reader expects from `a / b` in a proof.
pub fn euclid_div(a : Int, b : Int) -> Int {
  if b == 0 {
    return 0
  }
  let mut q = a / b
  let r = a - q * b
  if r < 0 {
    if b > 0 {
      q = q - 1
    } else {
      q = q + 1
    }
  }
  q
}

///|
/// Euclidean remainder, always in `[0, |b|)`.
pub fn euclid_mod(a : Int, b : Int) -> Int {
  if b == 0 {
    return 0
  }
  let mut r = a - euclid_div(a, b) * b
  if r < 0 {
    r = r + (if b < 0 { 0 - b } else { b })
  }
  r
}

///|
/// Wrap `n` into the signed range of a `w`-bit two's complement integer.
///
/// Done in 64-bit arithmetic, and `2^w` is built by repeated multiplication
/// rather than a shift: the shift operator here takes an `Int`, and `2^32` does
/// not fit one. Clamping the width instead would silently change the answer at
/// exactly the boundary this function exists to get right.
pub fn wrap(n : Int, w : Int) -> Int {
  if w <= 0 || w > 62 {
    return n
  }
  let mut modulus : Int64 = 1L
  let mut i = 0
  while i < w {
    modulus = modulus * 2L
    i = i + 1
  }
  let half : Int64 = modulus / 2L
  let value : Int64 = n.to_int64() % modulus
  let positive : Int64 = if value < 0L { value + modulus } else { value }
  let signed : Int64 = if positive >= half { positive - modulus } else { positive }
  signed.to_int()
}

///|
/// True when the term mentions no variable, so its value is already known.
pub fn is_constant(t : @core.Term) -> Bool {
  match simplify(t) {
    Lit(_) | True | False => true
    _ => false
  }
}

///|
/// The integer a constant term denotes. Only valid when `is_constant` is true;
/// a non-constant term answers 0, which callers must not rely on.
pub fn const_value(t : @core.Term) -> Int {
  match simplify(t) {
    Lit(n) => n
    True => 1
    False => 0
    _ => 0
  }
}
