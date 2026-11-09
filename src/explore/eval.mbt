// Surface expression → logical term.
//
// This is where the verifier's honesty lives. Every construct either maps to a
// term with the *same* meaning at the program's bit width, or the translation
// fails and the statement is reported as unsupported. There is no third option:
// a "close enough" term is how a verifier ends up proving something false.

///|
/// Translate an expression under a symbolic store.
///
/// `None` means "outside the logic" — an unknown name, a call whose value is not
/// modelled, or a division with a symbolic divisor (which the solver handles but
/// whose definedness would need a separate guard this version does not emit).
fn eval_expr(
  engine : Engine,
  expr : @symir.Expr,
  store : Map[String, SymVal],
) -> @core.Term? {
  match expr {
    @symir.Expr::IntLit(lit) => Some(@core.Term::Lit(lit.value))
    @symir.Expr::VarRef(v) =>
      match store.get(v.name) {
        Some(value) => Some(value.term)
        None => None
      }
    @symir.Expr::Len(len_) =>
      // A length is its own fresh symbolic variable, non-negative by the `Nat`
      // assumption the function's parameter list carries. Two `len(a)` in one
      // function must name the same length, so the variable is cached by name.
      Some(len_term(engine, len_.name))
    @symir.Expr::Bin(bin) =>
      match (eval_expr(engine, bin.lhs, store), eval_expr(engine, bin.rhs, store)) {
        (Some(l), Some(r)) => bin_term(bin.op, l, r, width_of(store))
        (_, _) => None
      }
    @symir.Expr::Un(un) =>
      match eval_expr(engine, un.operand, store) {
        None => None
        Some(t) =>
          match un.op {
            @symir.UnOp::Neg => Some(@core.Term::Neg(t))
            @symir.UnOp::Not => Some(@core.Term::Not(t))
          }
      }
    @symir.Expr::Ite(ite) =>
      match (
        eval_expr(engine, ite.cond, store),
        eval_expr(engine, ite.then_, store),
        eval_expr(engine, ite.else_, store),
      ) {
        (Some(c), Some(a), Some(b)) => Some(@core.Term::Ite(c, a, b))
        (_, _, _) => None
      }
    @symir.Expr::App(_) => None
  }
}

///|
/// The width every arithmetic term is wrapped to. Derived from the store's
/// integer sorts, so a function verified at 32 bits wraps at 32.
fn width_of(store : Map[String, SymVal]) -> Int {
  let mut width = 32
  store.each(fn(_name, value) {
    match value.sort {
      @core.Sort::Int(bits) => width = bits
      _ => ()
    }
  })
  width
}

///|
/// A binary operator as a term.
///
/// Addition and multiplication wrap: at a fixed width, `a + b` is
/// `wrap(a + b)`, and forgetting that is the classic way to "prove" a bound that
/// overflows. Comparison yields 0/1, which matches MoonBit's `Bool` being a
/// distinct type only at the surface: the solver speaks integers, so the
/// translation is `ite(c, 1, 0)` where a boolean is needed.
fn bin_term(
  op : @symir.BinOp,
  l : @core.Term,
  r : @core.Term,
  width : Int,
) -> @core.Term? {
  match op {
    @symir.BinOp::Add => Some(@core.Term::Wrap(@core.Term::Add(l, r), width))
    @symir.BinOp::Sub => Some(@core.Term::Wrap(@core.Term::Sub(l, r), width))
    @symir.BinOp::Mul =>
      match r {
        @core.Term::Lit(k) => Some(@core.Term::Wrap(@core.Term::MulLit(l, k), width))
        _ =>
          match l {
            @core.Term::Lit(k) => Some(@core.Term::Wrap(@core.Term::MulLit(r, k), width))
            // A product of two symbolic values is outside the logic on purpose:
            // the solver would have to be non-linear, and a bound proved by a
            // non-linear solver that is not complete is not a proof.
            _ => None
          }
      }
    @symir.BinOp::Div =>
      match r {
        @core.Term::Lit(k) => if k == 0 { None } else { Some(@core.Term::DivLit(l, k)) }
        _ => None
      }
    @symir.BinOp::Mod =>
      match r {
        @core.Term::Lit(k) => if k == 0 { None } else { Some(@core.Term::ModLit(l, k)) }
        _ => None
      }
    @symir.BinOp::Lt => Some(@core.Term::Lt(l, r))
    @symir.BinOp::Le => Some(@core.Term::Le(l, r))
    @symir.BinOp::Gt => Some(@core.Term::Lt(r, l))
    @symir.BinOp::Ge => Some(@core.Term::Le(r, l))
    @symir.BinOp::Eq => Some(@core.Term::Eq(l, r))
    @symir.BinOp::Ne => Some(@core.Term::Ne(l, r))
    @symir.BinOp::And => Some(@core.Term::And(truthy(l), truthy(r)))
    @symir.BinOp::Or => Some(@core.Term::Or(truthy(l), truthy(r)))
  }
}

///|
/// Treat an integer term as a boolean: non-zero is true.
///
/// The surface language has no separate boolean sort (a comparison *is* an
/// integer 0/1 in the term language), so this is the identity for comparisons
/// and a `!= 0` test otherwise.
fn truthy(t : @core.Term) -> @core.Term {
  match t {
    @core.Term::Lt(_, _) | @core.Term::Le(_, _) | @core.Term::Eq(_, _) |
    @core.Term::Ne(_, _) | @core.Term::And(_, _) | @core.Term::Or(_, _) |
    @core.Term::Not(_) | @core.Term::True | @core.Term::False => t
    _ => @core.Term::Ne(t, @core.Term::Lit(0))
  }
}

///|
/// A length used as a symbolic value.
///
/// Cached per name so `len(a)` in a precondition and `len(a)` in the body are the
/// same variable — otherwise every proof about an array would be vacuous because
/// the two lengths could differ.
fn len_term(engine : Engine, name : String) -> @core.Term {
  let key = "len(" + name + ")"
  match engine.len_cache.get(key) {
    Some(id) => @core.Term::Var(id)
    None => {
      let id = fresh(engine, key, @core.Sort::Nat)
      engine.len_cache.set(key, id)
      @core.Term::Var(id)
    }
  }
}
