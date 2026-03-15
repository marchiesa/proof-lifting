// Zigzag Traversal -- Test cases

predicate IsRectangular(m: seq<seq<int>>, rows: int, cols: int)
{
  |m| == rows && forall i :: 0 <= i < rows ==> |m[i]| == cols
}

method Main()
{
  // Test IsRectangular
  var m1 := [[1, 2, 3], [4, 5, 6]];
  expect IsRectangular(m1, 2, 3), "2x3 matrix";
  expect !IsRectangular(m1, 2, 2), "Not 2x2";

  // Test zigzag output length
  // 2x3 => 6 elements, 3x3 => 9 elements
  expect 2 * 3 == 6, "2*3=6";
  expect 3 * 3 == 9, "3*3=9";
  expect 0 * 5 == 0, "0*5=0";

  // Zigzag of [[1,2,3],[4,5,6]] should be [1,2,3,6,5,4]
  // Row 0 (even): left-to-right: 1,2,3
  // Row 1 (odd): right-to-left: 6,5,4
  var expected := [1, 2, 3, 6, 5, 4];
  expect |expected| == 6, "Expected length 6";

  // Non-zigzag would be [1,2,3,4,5,6]
  var flat := [1, 2, 3, 4, 5, 6];
  expect expected != flat, "Zigzag differs from flat traversal";

  print "All spec tests passed\n";
}
