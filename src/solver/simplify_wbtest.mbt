// The simplifier's contract, checked against brute force.
//
// Every rewrite rule claims to preserve the meaning of a term. The test below
// evaluates the original and the simplified form on every assignment in a small
// grid and requires agreement, which is the only property that matters.

///|
fn terms_agree(t : @core.Term) -> Bool {
  let simplified = simplify(t)
  let mut a = -6
  while a <= 6 {
    let mut b = -6
    while b <= 6 {
      let env : Map[Int32, Int] = Map([])
      env.set(1, a)
      env.set(2, b)
      let left = eval_int_opt(t, env)
      let right = eval_int_opt(simplified, env)
      match (left, right) {
        (Some(x), Some(y)) => if x != y { return false }
        (None, None) => ()
        (_, _) => return false
      }
      b = b + 1
    }
    a = a + 1
  }
  true
}

///|
test "additive identities preserve meaning" {
  let x : @core.Term = Var(1)
  assert_true(terms_agree(Add(x, Lit(0))))
  assert_true(terms_agree(Sub(x, Lit(0))))
  assert_true(terms_agree(Add(Lit(3), Lit(4))))
  assert_true(terms_agree(Sub(Lit(3), Lit(10))))
}

///|
test "multiplicative identities preserve meaning" {
  let x : @core.Term = Var(1)
  assert_true(terms_agree(MulLit(x, 0)))
  assert_true(terms_agree(MulLit(x, 1)))
  assert_true(terms_agree(MulLit(x, 7)))
  assert_true(terms_agree(MulLit(Lit(6), 7)))
}

///|
test "division and remainder preserve meaning" {
  let x : @core.Term = Var(1)
  assert_true(terms_agree(DivLit(x, 3)))
  assert_true(terms_agree(ModLit(x, 3)))
  assert_true(terms_agree(DivLit(Lit(0 - 7), 3)))
  assert_true(terms_agree(ModLit(Lit(0 - 7), 3)))
  assert_true(terms_agree(Div(x, Var(2))))
  assert_true(terms_agree(Rem(x, Var(2))))
}

///|
test "negation and absolute value preserve meaning" {
  let x : @core.Term = Var(1)
  assert_true(terms_agree(Neg(x)))
  assert_true(terms_agree(Neg(Neg(x))))
  assert_true(terms_agree(Abs(x)))
  assert_true(terms_agree(Abs(Neg(x))))
}

///|
test "wrapping preserves meaning" {
  let x : @core.Term = Var(1)
  assert_true(terms_agree(Wrap(x, 32)))
  assert_true(terms_agree(Wrap(Lit(2147483647), 32)))
  assert_true(terms_agree(Wrap(Add(Lit(2147483647), Lit(1)), 32)))
}

///|
test "conditional folding preserves meaning" {
  let x : @core.Term = Var(1)
  assert_true(terms_agree(Ite(Lt(x, Lit(0)), Lit(1), Lit(2))))
  assert_true(terms_agree(Ite(True, x, Lit(2))))
  assert_true(terms_agree(Ite(False, Lit(1), x)))
}

///|
test "euclidean division has the documented sign" {
  assert_eq(euclid_div(7, 3), 2)
  assert_eq(euclid_div(0 - 7, 3), 0 - 3)
  assert_eq(euclid_mod(7, 3), 1)
  assert_eq(euclid_mod(0 - 7, 3), 2)
  assert_eq(euclid_mod(6, 3), 0)
}

///|
test "wrapping lands in the signed range" {
  let half : Int = 2147483647
  assert_eq(wrap(half + 1, 32), 0 - half - 1)
  assert_eq(wrap(half, 32), half)
  assert_eq(wrap(0 - 2147483647, 32), 0 - 2147483647)
  assert_eq(wrap(half, 32), half)
  assert_eq(wrap(0 - 2147483647 - 1, 32), 0 - 2147483647 - 1)
  assert_eq(wrap(0, 32), 0)
}

///|
test "a comparison between literals folds" {
  assert_eq(simplify(Lt(Lit(1), Lit(2))), True)
  assert_eq(simplify(Lt(Lit(2), Lit(1))), False)
  assert_eq(simplify(Le(Lit(2), Lit(2))), True)
  assert_eq(simplify(Eq(Lit(2), Lit(2))), True)
}

///|
test "boolean identities fold" {
  let x : @core.Term = Var(1)
  assert_eq(simplify(And(x, True)), x)
  assert_eq(simplify(And(x, False)), False)
  assert_eq(simplify(Or(x, True)), True)
  assert_eq(simplify(Or(x, False)), x)
  assert_eq(simplify(Not(Not(x))), x)
}

///|
test "is_constant and const_value agree" {
  assert_true(is_constant(Add(Lit(2), Lit(3))))
  assert_eq(const_value(Add(Lit(2), Lit(3))), 5)
  assert_false(is_constant(Var(1)))
}
