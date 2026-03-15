// Find First and Last Position of Target -- Reference solution with invariants

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

  // Find first occurrence with binary search
  var lo := 0;
  var hi := |a|;
  while lo < hi
    invariant 0 <= lo <= hi <= |a|
    invariant forall k :: 0 <= k < lo ==> a[k] < target
    invariant forall k :: hi <= k < |a| ==> a[k] >= target
    decreases hi - lo
  {
    var mid := lo + (hi - lo) / 2;
    if a[mid] < target {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }

  if lo >= |a| || a[lo] != target {
    assert forall k :: 0 <= k < |a| ==> a[k] != target by {
      forall k | 0 <= k < |a|
        ensures a[k] != target
      {
        if k < lo {
          assert a[k] < target;
        } else {
          assert a[k] >= target;
          if lo < |a| && a[lo] != target {
            assert a[lo] > target;
            assert a[k] >= a[lo] > target;
          }
        }
      }
    }
    return;
  }
  first := lo;

  // Find last occurrence with binary search
  lo := first;
  hi := |a|;
  while lo < hi
    invariant first <= lo <= hi <= |a|
    invariant forall k :: first <= k < lo ==> a[k] <= target
    invariant forall k :: hi <= k < |a| ==> a[k] > target
    decreases hi - lo
  {
    var mid := lo + (hi - lo) / 2;
    if a[mid] <= target {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  last := lo - 1;
  assert a[last] == target;
  assert forall k :: last < k < |a| ==> a[k] > target;
}
