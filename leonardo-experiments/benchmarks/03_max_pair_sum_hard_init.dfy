// Difficulty: Hard (nested loop, bad initialization)
// Expected: LLM will likely fail due to existence witness problem
method MaxPairSum(s: seq<int>) returns (maxSum: int)
  requires |s| >= 2
  requires forall k :: 0 <= k < |s| ==> s[k] > 0
  ensures forall i, j :: 0 <= i < j < |s| ==> maxSum >= s[i] + s[j]
  ensures exists i, j :: 0 <= i < j < |s| && maxSum == s[i] + s[j]
{
  maxSum := 0;
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
