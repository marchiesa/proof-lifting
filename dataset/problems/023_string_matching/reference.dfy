// String Matching (Naive) -- Reference solution with invariants

predicate MatchAt(text: seq<int>, pattern: seq<int>, pos: int)
  requires |pattern| > 0
  requires 0 <= pos <= |text| - |pattern|
{
  text[pos..pos + |pattern|] == pattern
}

method Match(text: seq<int>, pattern: seq<int>) returns (index: int)
  requires |pattern| > 0
  ensures index == -1 ==>
    forall k {:trigger MatchAt(text, pattern, k)} :: 0 <= k <= |text| - |pattern| ==> !MatchAt(text, pattern, k)
  ensures 0 <= index ==> (index <= |text| - |pattern| &&
    MatchAt(text, pattern, index))
  ensures 0 <= index ==>
    forall k {:trigger MatchAt(text, pattern, k)} :: 0 <= k < index ==> !MatchAt(text, pattern, k)
{
  if |pattern| > |text| {
    return -1;
  }

  var i := 0;
  while i <= |text| - |pattern|
    invariant 0 <= i <= |text| - |pattern| + 1
    invariant forall k {:trigger MatchAt(text, pattern, k)} :: 0 <= k < i ==> !MatchAt(text, pattern, k)
    decreases |text| - |pattern| - i + 1
  {
    var j := 0;
    while j < |pattern| && text[i + j] == pattern[j]
      invariant 0 <= j <= |pattern|
      invariant text[i..i + j] == pattern[..j]
      decreases |pattern| - j
    {
      assert text[i..i + j + 1] == text[i..i + j] + [text[i + j]];
      assert pattern[..j + 1] == pattern[..j] + [pattern[j]];
      j := j + 1;
    }
    if j == |pattern| {
      assert text[i..i + |pattern|] == pattern[..|pattern|] == pattern;
      assert MatchAt(text, pattern, i);
      return i;
    }
    // j < |pattern| and text[i+j] != pattern[j], so this position doesn't match
    assert !MatchAt(text, pattern, i) by {
      assert text[i..i + |pattern|][j] == text[i + j];
      assert pattern[j] != text[i + j];
      assert text[i..i + |pattern|] != pattern;
    }
    i := i + 1;
  }
  return -1;
}
