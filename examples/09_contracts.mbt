// EXPECT proven=3 violated=0 undecided=0
// A contract that a caller can actually establish.
require n >= 0
ensure 1 == 1
fn double(n : nat) -> Int {
  assert n + n >= 0
  return n + n
}
