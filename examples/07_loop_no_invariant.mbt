// EXPECT proven=1 violated=0 undecided=1
// The same loop with no invariant: the tool must say it cannot decide, not
// silently assume the counter behaves.
fn count_up_unchecked(n : nat) -> Int {
  let mut i = 0
  while i < n {
    i = i + 1
  }
  assert i >= 0
  return i
}
