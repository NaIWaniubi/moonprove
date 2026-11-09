// EXPECT proven=2 violated=0 undecided=1
// Clamping puts a value back in range, which is what its contract promises.
fn clamp(x : Int, lo : Int, hi : Int) -> Int {
  if lo <= hi {
    if x < lo {
      assert lo <= lo && lo <= hi
      return lo
    }
    if x > hi {
      assert lo <= hi && hi <= hi
      return hi
    }
    assert x >= lo && x <= hi && lo <= hi
    return x
  }
  return x
}
