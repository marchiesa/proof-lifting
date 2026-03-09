// Difficulty: Easy (single loop, sum - not idempotent)
// Expected: LLM should succeed (no existence witness needed)
method SumElements(s: seq<int>) returns (sum: int)
  requires |s| > 0
  ensures sum == SumSeq(s)
{
  sum := 0;
  var idx := 0;

  while idx < |s|
  // INVARIANTS
  {
    sum := sum + s[idx];
    idx := idx + 1;
  }
}

// Helper function for specification
function SumSeq(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + SumSeq(s[1..])
}
