// Difficulty: Medium (nested loop, good initialization)
// Expected: LLM should succeed with proper invariants
method MaxPairSum(s: seq<int>) returns (maxSum: int)
  requires |s| >= 2
  requires forall k :: 0 <= k < |s| ==> s[k] > 0
  ensures forall i, j :: 0 <= i < j < |s| ==> maxSum >= s[i] + s[j]
  ensures exists i, j :: 0 <= i < j < |s| && maxSum == s[i] + s[j]
{
  maxSum := s[0] + s[1];
  var a := 0;

  while a < |s| - 1
  // OUTER INVARIANTS
  {
    var b := a + 1;

    while b < |s|
    // INNER INVARIANTS
    {
      if s[a] + s[b] > maxSum {
        maxSum := s[a] + s[b];
      }
      b := b + 1;
    }

    a := a + 1;
  }
}
