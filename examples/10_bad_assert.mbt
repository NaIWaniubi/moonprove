// EXPECT proven=0 violated=1 undecided=0
// A wrong assertion: the tool must find the counterexample.
fn wrong(x : Int) -> Int {
  assert x > 100
  return x
}
