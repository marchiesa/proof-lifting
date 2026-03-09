// Difficulty: Easy (single loop)
// Expected: LLM should succeed
method MaxElement(s: seq<int>) returns (max: int)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures forall i :: 0 <= i < |s| ==> max >= s[i]
  ensures exists i :: 0 <= i < |s| && max == s[i]
{
  max := 0;
  var idx := 0;

  while idx < |s|
  // INVARIANTS
  {
    if s[idx] > max {
      max := s[idx];
    }
    idx := idx + 1;
  }
}
