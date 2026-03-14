// Selection Sort -- Runtime spec tests

// Copy spec predicate from task.dfy (rewritten with bounded quantifiers for compilation)
predicate Sorted(a: array<int>, lo: int, hi: int)
  reads a
  requires 0 <= lo <= hi <= a.Length
{
  forall i, j :: lo <= i < j < hi ==> a[i] <= a[j]
}

// Bounded version for runtime checking
method IsSortedCheck(a: array<int>, lo: int, hi: int) returns (result: bool)
  requires 0 <= lo <= hi <= a.Length
{
  var i := lo;
  while i < hi
  {
    var j := i + 1;
    while j < hi
    {
      if a[i] > a[j] { return false; }
      j := j + 1;
    }
    i := i + 1;
  }
  return true;
}

method Main()
{
  // Test 1: Sorted array should satisfy Sorted predicate
  var a1 := new int[] [1, 2, 3, 4, 5];
  var r1 := IsSortedCheck(a1, 0, a1.Length);
  expect r1, "Sorted array [1,2,3,4,5] should be Sorted";

  // Test 2: Unsorted array should NOT satisfy Sorted predicate
  var a2 := new int[] [3, 1, 2];
  var r2 := IsSortedCheck(a2, 0, a2.Length);
  expect !r2, "Unsorted array [3,1,2] should not be Sorted";

  // Test 3: Single-element array is always sorted
  var a3 := new int[] [42];
  var r3 := IsSortedCheck(a3, 0, a3.Length);
  expect r3, "Single-element array should be Sorted";

  // Test 4: Empty range is sorted
  var a4 := new int[] [5, 3, 1];
  var r4 := IsSortedCheck(a4, 0, 0);
  expect r4, "Empty range should be Sorted";

  // Test 5: Partial range sorted
  var a5 := new int[] [1, 2, 5, 3];
  var r5 := IsSortedCheck(a5, 0, 3);
  expect r5, "Partial range [1,2,5] should be Sorted";
  var r5b := IsSortedCheck(a5, 0, 4);
  expect !r5b, "Full range [1,2,5,3] should not be Sorted";

  // Test 6: Array with duplicates
  var a6 := new int[] [1, 1, 2, 2, 3];
  var r6 := IsSortedCheck(a6, 0, a6.Length);
  expect r6, "Array with duplicates [1,1,2,2,3] should be Sorted";

  // Test 7: Reverse sorted is not sorted
  var a7 := new int[] [5, 4, 3, 2, 1];
  var r7 := IsSortedCheck(a7, 0, a7.Length);
  expect !r7, "Reverse sorted [5,4,3,2,1] should not be Sorted";

  // Test 8: multiset preservation check (manual)
  var a8 := new int[] [3, 1, 2];
  var ms_before := multiset(a8[..]);
  // Simulate that a correctly sorted result preserves multiset
  a8[0] := 1; a8[1] := 2; a8[2] := 3;
  var ms_after := multiset(a8[..]);
  expect ms_before == ms_after, "Multiset should be preserved after sorting";

  // Test 9: multiset changes when element altered (negative test)
  var a9 := new int[] [3, 1, 2];
  var ms9_before := multiset(a9[..]);
  a9[0] := 1; a9[1] := 1; a9[2] := 3; // different elements!
  var ms9_after := multiset(a9[..]);
  expect ms9_before != ms9_after, "Multiset should differ when elements change";

  print "All spec tests passed\n";
}
