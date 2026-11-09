// EXPECT proven=1 violated=0 undecided=1
// A binary search's midpoint is in range, which is the invariant that makes the
// loop terminate without reading out of bounds.
fn mid(lo : Int, hi : Int) -> Int {
  if lo >= 0 && hi >= lo && hi <= 1000 {
    assert (lo + hi) / 2 >= lo
    assert (lo + hi) / 2 <= hi
  }
  return 0
}
