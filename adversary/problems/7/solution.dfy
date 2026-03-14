// Problem 7: Decreases Clause Tricks — Two-Pointer Convergence (SOLUTION)
//
// The loop advances lo by 2 and hi by 1 per iteration, checking s[lo],
// s[lo+1], and s[hi] each time. The decreases clause `hi - lo` is non-obvious
// because:
// 1. lo moves by 2 and hi moves by 1, so hi-lo decreases by 3 per iteration
// 2. But the initial `hi - lo` might not be divisible by 3, so the loop
//    might terminate via the guard condition rather than lo > hi
//
// The critical fix: when lo + 1 >= hi after checking s[lo], s[hi], and
// potentially s[lo+1], we must return early. Without this guard, lo + 2
// could skip past an unchecked index, violating the invariant
// `forall k :: 0 <= k < lo ==> s[k] != target`.
//
// An LLM will likely write the correct invariants but miss this guard,
// getting a misleading "invariant not maintained" error.

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
    invariant 0 <= lo <= |s|
    invariant !found
    invariant forall k :: 0 <= k < lo && k < |s| ==> s[k] != target
    invariant forall k :: hi < k < |s| ==> s[k] != target
    // Termination: hi - lo decreases by 3 each full iteration
    decreases hi - lo
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
    if lo + 1 < hi && s[lo + 1] == target {
      found := true;
      idx := lo + 1;
      return;
    }
    // KEY FIX: Guard against skipping unchecked elements.
    // If lo + 1 >= hi, then lo and hi are adjacent or equal.
    // We've already checked both s[lo] and s[hi], and if lo+1 < hi
    // we checked s[lo+1] too. So all remaining elements are checked.
    if lo + 1 >= hi {
      return;
    }
    lo := lo + 2;
    hi := hi - 1;
  }
}
