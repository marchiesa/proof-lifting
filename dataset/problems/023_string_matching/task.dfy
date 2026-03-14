// String Matching (Naive)
// Task: Add loop invariants so that Dafny can verify this program.

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
  {
    var j := 0;
    while j < |pattern| && text[i + j] == pattern[j]
    {
      j := j + 1;
    }
    if j == |pattern| {
      return i;
    }
    i := i + 1;
  }
  return -1;
}
