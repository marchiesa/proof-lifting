// Difficulty: Easy (single loop, search)
// Expected: LLM should succeed
method LinearSearch(s: seq<int>, target: int) returns (found: bool, idx: int)
  ensures found ==> 0 <= idx < |s| && s[idx] == target
  ensures !found ==> forall i :: 0 <= i < |s| ==> s[i] != target
{
  found := false;
  idx := 0;

  while idx < |s| && !found
  // INVARIANTS
  {
    if s[idx] == target {
      found := true;
    } else {
      idx := idx + 1;
    }
  }
}
