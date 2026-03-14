// Segment Tree -- Runtime spec tests

// Copy spec function from task.dfy
function SumRange(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0 else a[lo] + SumRange(a, lo + 1, hi)
}

method Main()
{
  // Test SumRange function
  expect SumRange([1, 2, 3, 4], 0, 4) == 10, "Sum of [1,2,3,4] should be 10";
  expect SumRange([1, 2, 3, 4], 0, 0) == 0, "Empty range sum should be 0";
  expect SumRange([1, 2, 3, 4], 0, 1) == 1, "Sum of [1] should be 1";
  expect SumRange([1, 2, 3, 4], 1, 3) == 5, "Sum of [2,3] should be 5";
  expect SumRange([1, 2, 3, 4], 2, 4) == 7, "Sum of [3,4] should be 7";
  expect SumRange([5], 0, 1) == 5, "Sum of [5] should be 5";
  expect SumRange([-1, -2, 3], 0, 3) == 0, "Sum of [-1,-2,3] should be 0";

  // Negative tests
  expect SumRange([1, 2, 3, 4], 0, 4) != 11, "Sum of [1,2,3,4] should not be 11";
  expect SumRange([1, 2, 3, 4], 1, 3) != 6, "Sum of [2,3] should not be 6";

  // Test additivity: SumRange(a, lo, mid) + SumRange(a, mid, hi) == SumRange(a, lo, hi)
  var a := [1, 2, 3, 4, 5];
  expect SumRange(a, 0, 2) + SumRange(a, 2, 5) == SumRange(a, 0, 5),
    "Sum should be additive over split ranges";
  expect SumRange(a, 0, 3) + SumRange(a, 3, 5) == SumRange(a, 0, 5),
    "Sum should be additive over different split";

  // Test that updating one element changes the sum correctly
  var b := [1, 2, 3, 4, 5];
  var c := [1, 2, 10, 4, 5]; // changed index 2 from 3 to 10
  expect SumRange(c, 0, 5) == SumRange(b, 0, 5) + 7,
    "After update +7 at index 2, total sum should increase by 7";

  print "All spec tests passed\n";
}
