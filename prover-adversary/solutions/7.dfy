// Problem 7: Decreases Clause Tricks — Two-Pointer Convergence

method TwoPointerSearch(s: seq<int>, target: int) returns (found: bool, idx: int)
  requires |s| >= 2
  ensures found ==> 0 <= idx < |s| && s[idx] == target
  ensures !found ==> forall k :: 0 <= k < |s| ==> s[k] != target
{
  var lo := 0;
  var hi := |s| - 1;
  found := false;
  idx := -1;
  while lo <= hi
    invariant -1 <= hi < |s|
    invariant 0 <= lo <= |s| + 1
    invariant !found
    invariant forall k :: 0 <= k < lo && k < |s| ==> s[k] != target
    invariant forall k :: hi < k < |s| ==> s[k] != target
    decreases hi - lo + 1
  {
    if s[lo] == target {
      found := true;
      idx := lo;
      return;
    }
    if s[hi] == target {
      found := true;
      idx := hi;
      return;
    }
    // Skip one extra from the left if possible
    if lo + 1 < hi && s[lo + 1] == target {
      found := true;
      idx := lo + 1;
      return;
    }
    lo := lo + 2;
    hi := hi - 1;
  }
}
