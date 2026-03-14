// Problem 7: Decreases Clause Tricks — Two-Pointer Convergence
//
// Task: Add decreases clauses, loop invariants, and any needed assertions
// so this method verifies.
//
// The method uses two indices that both start at the ends of a sequence
// and move toward each other, but with an asymmetric step pattern:
// the left pointer may advance by 1 or 2, and the right pointer
// always advances by 1. This makes the termination argument tricky.

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
    // TODO: add invariants and decreases clause
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
