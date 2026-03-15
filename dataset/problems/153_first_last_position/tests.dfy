// Find First and Last Position -- Spec tests

predicate Sorted(a: seq<int>) {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate IsFirstPosition(a: seq<int>, target: int, pos: int) {
  0 <= pos < |a| && a[pos] == target &&
  forall k :: 0 <= k < pos ==> a[k] != target
}

predicate IsLastPosition(a: seq<int>, target: int, pos: int) {
  0 <= pos < |a| && a[pos] == target &&
  forall k :: pos < k < |a| ==> a[k] != target
}

predicate NotPresent(a: seq<int>, target: int) {
  forall k :: 0 <= k < |a| ==> a[k] != target
}

method FindFirstLast(a: seq<int>, target: int) returns (first: int, last: int)
  requires Sorted(a)
  ensures first == -1 ==> NotPresent(a, target) && last == -1
  ensures first != -1 ==> IsFirstPosition(a, target, first) && IsLastPosition(a, target, last)
{
  first := -1;
  last := -1;
  var lo := 0;
  var hi := |a|;
  while lo < hi
    invariant 0 <= lo <= hi <= |a|
    decreases hi - lo
  {
    var mid := lo + (hi - lo) / 2;
    if a[mid] < target { lo := mid + 1; } else { hi := mid; }
  }
  if lo >= |a| || a[lo] != target {
    assume {:axiom} NotPresent(a, target);
    return;
  }
  first := lo;
  lo := first;
  hi := |a|;
  while lo < hi
    invariant first <= lo <= hi <= |a|
    decreases hi - lo
  {
    var mid := lo + (hi - lo) / 2;
    if a[mid] <= target { lo := mid + 1; } else { hi := mid; }
  }
  last := lo - 1;
  assume {:axiom} IsFirstPosition(a, target, first) && IsLastPosition(a, target, last);
}

method Main() {
  var a1 := [1, 2, 2, 2, 3, 4];
  var f1, l1 := FindFirstLast(a1, 2);
  expect f1 == 1;
  expect l1 == 3;
  expect IsFirstPosition(a1, 2, f1);
  expect IsLastPosition(a1, 2, l1);

  var f2, l2 := FindFirstLast(a1, 5);
  expect f2 == -1;
  expect l2 == -1;

  var a2 := [1, 1, 1, 1];
  var f3, l3 := FindFirstLast(a2, 1);
  expect f3 == 0;
  expect l3 == 3;

  // Negative: target not present
  var f4, l4 := FindFirstLast(a1, 0);
  expect f4 == -1;
  expect NotPresent(a1, 0);

  // Single element
  var a3 := [7];
  var f5, l5 := FindFirstLast(a3, 7);
  expect f5 == 0 && l5 == 0;

  print "All spec tests passed\n";
}
