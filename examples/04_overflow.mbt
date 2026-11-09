// EXPECT proven=0 violated=0 undecided=1
// A sum that can overflow: the tool must not claim it is positive.
fn unbounded_sum(x : Int, y : Int) -> Int {
  if x > 0 && y > 0 {
    assert x + y > 0
  }
  return 0
}
