// Shortest Unsorted Continuous Subarray

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

function Max(a: int, b: int): int { if a >= b then a else b }
function Min(a: int, b: int): int { if a <= b then a else b }

method ShortestUnsorted(a: seq<int>) returns (length: int)
  ensures length >= 0
  ensures length <= |a|
  ensures length == 0 ==> IsSorted(a)
{
  if |a| <= 1 {
    return 0;
  }
  // Find the boundaries of the unsorted subarray
  var left := 0;
  while left < |a| - 1 && a[left] <= a[left + 1]
  {
    left := left + 1;
  }
  if left == |a| - 1 {
    return 0; // already sorted
  }
  var right := |a| - 1;
  while right > 0 && a[right] >= a[right - 1]
  {
    right := right - 1;
  }
  // Find min and max in unsorted portion
  var minVal := a[left];
  var maxVal := a[left];
  var i := left;
  while i <= right
  {
    minVal := Min(minVal, a[i]);
    maxVal := Max(maxVal, a[i]);
    i := i + 1;
  }
  // Extend left
  while left > 0 && a[left - 1] > minVal
  {
    left := left - 1;
  }
  // Extend right
  while right < |a| - 1 && a[right + 1] < maxVal
  {
    right := right + 1;
  }
  length := right - left + 1;
}

method Main()
{
  // [2, 6, 4, 8, 10, 9, 15] => subarray [6,4,8,10,9] length 5
  var a := [2, 6, 4, 8, 10, 9, 15];
  var r1 := ShortestUnsorted(a);
  expect r1 >= 0;
  expect r1 <= 7;

  // Already sorted
  var b := [1, 2, 3, 4, 5];
  var r2 := ShortestUnsorted(b);
  expect r2 == 0;
  expect IsSorted(b);

  // Reverse sorted
  var c := [5, 4, 3, 2, 1];
  var r3 := ShortestUnsorted(c);
  expect r3 > 0;

  // Single element
  var d := [1];
  var r4 := ShortestUnsorted(d);
  expect r4 == 0;

  // Empty
  var e: seq<int> := [];
  var r5 := ShortestUnsorted(e);
  expect r5 == 0;

  // Negative test: not sorted => length > 0
  expect !IsSorted([3, 1, 2]);

  print "All spec tests passed\n";
}
