// Find Peak Element -- Runtime spec tests

// Copy spec from task.dfy
predicate IsPeak(a: array<int>, i: int)
  reads a
  requires 0 <= i < a.Length
{
  (i == 0 || a[i] > a[i - 1]) && (i == a.Length - 1 || a[i] > a[i + 1])
}

method Main()
{
  // Test 1: middle peak [1, 3, 2] => index 1 is a peak
  var a1 := new int[] [1, 3, 2];
  expect IsPeak(a1, 1), "In [1,3,2], index 1 should be a peak";

  // Test 2: not a peak
  expect !IsPeak(a1, 0), "In [1,3,2], index 0 should not be a peak";
  expect !IsPeak(a1, 2), "In [1,3,2], index 2 should not be a peak";

  // Test 3: left peak [5, 1, 2]
  var a2 := new int[] [5, 1, 2];
  expect IsPeak(a2, 0), "In [5,1,2], index 0 should be a peak";
  expect !IsPeak(a2, 1), "In [5,1,2], index 1 should not be a peak";

  // Test 4: right peak [1, 2, 5]
  var a3 := new int[] [1, 2, 5];
  expect IsPeak(a3, 2), "In [1,2,5], index 2 should be a peak";
  expect !IsPeak(a3, 0), "In [1,2,5], index 0 should not be a peak";

  // Test 5: single element is always a peak
  var a4 := new int[] [42];
  expect IsPeak(a4, 0), "Single element should be a peak";

  // Test 6: two elements [3, 1]
  var a5 := new int[] [3, 1];
  expect IsPeak(a5, 0), "In [3,1], index 0 should be a peak";
  expect !IsPeak(a5, 1), "In [3,1], index 1 should not be a peak";

  // Test 7: two elements [1, 3]
  var a6 := new int[] [1, 3];
  expect !IsPeak(a6, 0), "In [1,3], index 0 should not be a peak";
  expect IsPeak(a6, 1), "In [1,3], index 1 should be a peak";

  // Test 8: multiple peaks [3, 1, 4, 2, 5]
  var a7 := new int[] [3, 1, 4, 2, 5];
  expect IsPeak(a7, 0), "In [3,1,4,2,5], index 0 is a peak";
  expect !IsPeak(a7, 1), "In [3,1,4,2,5], index 1 is not a peak";
  expect IsPeak(a7, 2), "In [3,1,4,2,5], index 2 is a peak";
  expect !IsPeak(a7, 3), "In [3,1,4,2,5], index 3 is not a peak";
  expect IsPeak(a7, 4), "In [3,1,4,2,5], index 4 is a peak";

  print "All spec tests passed\n";
}
