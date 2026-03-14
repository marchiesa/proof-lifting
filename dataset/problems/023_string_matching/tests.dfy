// String Matching (Naive) -- Test cases

predicate MatchAt(text: seq<int>, pattern: seq<int>, pos: int)
  requires |pattern| > 0
  requires 0 <= pos <= |text| - |pattern|
{
  text[pos..pos + |pattern|] == pattern
}

method {:axiom} Match(text: seq<int>, pattern: seq<int>) returns (index: int)
  requires |pattern| > 0
  ensures index == -1 ==>
    forall k {:trigger MatchAt(text, pattern, k)} :: 0 <= k <= |text| - |pattern| ==> !MatchAt(text, pattern, k)
  ensures 0 <= index ==> (index <= |text| - |pattern| &&
    MatchAt(text, pattern, index))
  ensures 0 <= index ==>
    forall k {:trigger MatchAt(text, pattern, k)} :: 0 <= k < index ==> !MatchAt(text, pattern, k)

method TestFound()
{
  var text := [1, 2, 3, 4, 5];
  var pattern := [3, 4];
  var idx := Match(text, pattern);
  if idx >= 0 {
    assert MatchAt(text, pattern, idx);
  }
}

method TestNotFound()
{
  var text := [1, 2, 3];
  var pattern := [4, 5];
  var idx := Match(text, pattern);
  // If found, it matches at index
  if idx >= 0 {
    assert MatchAt(text, pattern, idx);
  }
}

method TestSingleMatch()
{
  var text := [1];
  var pattern := [1];
  var idx := Match(text, pattern);
  if idx >= 0 {
    assert MatchAt(text, pattern, idx);
  }
}

method TestPatternLongerThanText()
{
  var text := [1];
  var pattern := [1, 2];
  var idx := Match(text, pattern);
  // pattern is longer than text, so no match possible
  assert !(0 <= idx);
}
