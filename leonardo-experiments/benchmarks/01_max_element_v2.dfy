// Difficulty: Easy (single loop) - variant with max := s[0]
// Expected: LLM should succeed more easily
method MaxElement(s: seq<int>) returns (max: int)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures forall i :: 0 <= i < |s| ==> max >= s[i]
  ensures exists i :: 0 <= i < |s| && max == s[i]
{
  max := s[0];
  var idx := 1;

  while idx < |s|
  // INVARIANTS
  {
    if s[idx] > max {
      max := s[idx];
    }
    idx := idx + 1;
  }
}
