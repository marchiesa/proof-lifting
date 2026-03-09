// Difficulty: Medium (single loop, binary search with more complex invariants)
// Expected: LLM might struggle with binary search invariants
method BinarySearch(s: seq<int>, target: int) returns (found: bool, idx: int)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]  // sorted
  ensures found ==> 0 <= idx < |s| && s[idx] == target
  ensures !found ==> forall i :: 0 <= i < |s| ==> s[i] != target
{
  if |s| == 0 {
    return false, 0;
  }

  var lo := 0;
  var hi := |s|;

  while lo < hi
  // INVARIANTS
  {
    var mid := (lo + hi) / 2;
    if s[mid] < target {
      lo := mid + 1;
    } else if s[mid] > target {
      hi := mid;
    } else {
      return true, mid;
    }
  }

  return false, 0;
}
