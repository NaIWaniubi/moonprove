// EXPECT proven=1 violated=0 undecided=0
// A quotient of a non-negative value stays non-negative.
fn half_of_nonneg(x : Int) -> Int {
  if x >= 0 {
    assert x / 2 >= 0
  }
  return 0
}
