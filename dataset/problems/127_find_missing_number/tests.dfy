// Find Missing Number -- Test cases

predicate AllInRange(a: seq<int>, n: int)
{
  forall i :: 0 <= i < |a| ==> 0 <= a[i] <= n
}

predicate AllDistinct(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] != a[j]
}

predicate Contains(a: seq<int>, v: int)
{
  exists i :: 0 <= i < |a| && a[i] == v
}

method Main()
{
  // Test AllInRange
  expect AllInRange([0, 1, 2], 3), "[0,1,2] in range [0,3]";
  expect !AllInRange([0, 4], 3), "[0,4] not in range [0,3]";

  // Test AllDistinct
  expect AllDistinct([0, 1, 2]), "[0,1,2] distinct";
  expect !AllDistinct([0, 1, 0]), "[0,1,0] not distinct";

  // Test Contains - positive
  expect Contains([3, 1, 2], 1), "1 in [3,1,2]";
  expect Contains([0], 0), "0 in [0]";

  // Test Contains - negative
  expect !Contains([3, 1, 2], 0), "0 not in [3,1,2]";
  expect !Contains([], 0), "0 not in []";

  // Test spec: [1, 2, 0] is missing 3 from [0..3]
  var a1 := [1, 2, 0];
  expect AllInRange(a1, 3);
  expect AllDistinct(a1);
  expect !Contains(a1, 3);
  expect Contains(a1, 0);
  expect Contains(a1, 1);
  expect Contains(a1, 2);

  // Test spec: [0, 2] is missing 1 from [0..2]
  var a2 := [0, 2];
  expect AllInRange(a2, 2);
  expect AllDistinct(a2);
  expect !Contains(a2, 1);

  print "All spec tests passed\n";
}
