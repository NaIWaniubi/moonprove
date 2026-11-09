// EXPECT proven=2 violated=0 undecided=0
// The absolute value never overflows: the branch pins the sign before negating.
fn abs(x : Int, nat : nat) -> Int {
  if x < 0 {
    assert 0 - x > 0
    return 0 - x
  }
  assert x >= 0
  return x
}
