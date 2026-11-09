// Fourier–Motzkin, checked against cases whose answer a reader can verify by hand.

///|
fn con(a : Array[@core.Term]) -> Refuted {
  refute(a)
}

///|
test "x < 0 and x > 5 is refuted" {
  // x < 0 and 5 < x cannot both hold.
  assert_eq(con([@core.Lt(@core.Var(1), @core.Lit(0)), @core.Lt(@core.Lit(5), @core.Var(1))]), Refuted::Yes)
}

///|
test "x < 0 and x < 5 is not refuted" {
  assert_eq(con([@core.Lt(@core.Var(1), @core.Lit(0)), @core.Lt(@core.Var(1), @core.Lit(5))]), Refuted::No)
}

///|
test "x == 3 and x != 3 is not seen by elimination, and that is honest" {
  // `!=` is outside the linear-conjunction fragment this pass handles.
  assert_eq(con([@core.Eq(@core.Var(1), @core.Lit(3)), @core.Ne(@core.Var(1), @core.Lit(3))]), Refuted::Outside)
}

///|
test "a single contradictory constant is refuted" {
  assert_eq(con([@core.False]), Refuted::Yes)
}

///|
test "x <= 3 and 4 <= x is refuted" {
  assert_eq(con([@core.Le(@core.Var(1), @core.Lit(3)), @core.Le(@core.Lit(4), @core.Var(1))]), Refuted::Yes)
}

///|
test "x <= 3 and 3 <= x is not refuted" {
  assert_eq(con([@core.Le(@core.Var(1), @core.Lit(3)), @core.Le(@core.Lit(3), @core.Var(1))]), Refuted::No)
}

///|
test "two variables: x + y <= 0, x - y <= 0, 1 <= x is refuted" {
  let x : @core.Term = @core.Var(1)
  let y : @core.Term = @core.Var(2)
  // x + y <= 0, x - y <= 0  =>  x <= 0;  with 1 <= x that is a contradiction.
  assert_eq(
    con([
      @core.Le(@core.Add(x, y), @core.Lit(0)),
      @core.Le(@core.Sub(x, y), @core.Lit(0)),
      @core.Le(@core.Lit(1), x),
    ]),
    Refuted::Yes,
  )
}

///|
test "multiplication by a literal is linear" {
  let x : @core.Term = @core.Var(1)
  // `x * 3 < x` is `2x < 0`, i.e. `x < 0`, which contradicts x >= 0.
  assert_eq(con([@core.Lt(@core.MulLit(x, 3), x), @core.Le(@core.Lit(0), x)]), Refuted::Yes)
  // Without the lower bound it is satisfiable: x = -1.
  assert_eq(con([@core.Lt(@core.MulLit(x, 3), x)]), Refuted::No)
}

///|
test "a ternary is outside the fragment" {
  assert_eq(
    con([@core.Lt(@core.Ite(@core.Lt(@core.Var(1), @core.Lit(0)), @core.Lit(1), @core.Lit(2)), @core.Lit(0))]),
    Refuted::Outside,
  )
}

///|
test "x <= y and y < x is refuted" {
  let x : @core.Term = @core.Var(2)
  let y : @core.Term = @core.Var(3)
  assert_eq(con([@core.Not(@core.Lt(y, x)), @core.Lt(y, x)]), Refuted::Yes)
}

///|
test "a negated conjunction is refuted against its own conjunct" {
  let x : @core.Term = @core.Var(2)
  let y : @core.Term = @core.Var(3)
  // {x <= y, !(x <= x && x <= y)} must be unsatisfiable.
  assert_eq(
    con([@core.Le(x, y), @core.Not(@core.And(@core.Le(x, x), @core.Le(x, y)))]),
    Refuted::Yes,
  )
}

