// EXPECT proven=1 violated=0 undecided=0
// The same sum with bounds that keep it inside the range: provable.
fn bounded_sum(x : Int, y : Int) -> Int {
  if x > 0 && y >= 0 && x <= 100 && y <= 100 {
    assert x + y > 0
  }
  return 0
}
