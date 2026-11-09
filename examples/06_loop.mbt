// EXPECT proven=3 violated=0 undecided=0
// A loop with a true invariant: the counter never goes negative.
fn count_up(n : nat) -> Int {
  let mut i = 0
  while i < n invariant i >= 0 {
    i = i + 1
  }
  assert i >= 0
  return i
}
