// Remove Consecutive Duplicates
// Task: Add loop invariants so that Dafny can verify this program.
// Remove consecutive duplicate elements from a sequence.

predicate NoConsecutiveDups(s: seq<int>)
{
  forall i :: 0 < i < |s| ==> s[i] != s[i-1]
}

predicate IsSubseqOf(sub: seq<int>, s: seq<int>)
{
  |sub| <= |s| &&
  exists indices: seq<int> ::
    |indices| == |sub| &&
    (forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |s|) &&
    (forall i :: 0 <= i < |indices| ==> sub[i] == s[indices[i]]) &&
    (forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j])
}

method RemoveConsecutiveDups(a: seq<int>) returns (result: seq<int>)
  ensures NoConsecutiveDups(result)
  ensures |a| == 0 ==> |result| == 0
  ensures |a| > 0 ==> |result| > 0 && result[0] == a[0] && result[|result|-1] == a[|a|-1]
{
  if |a| == 0 {
    return [];
  }
  result := [a[0]];
  var i := 1;
  while i < |a|
  {
    if a[i] != a[i-1] {
      result := result + [a[i]];
    }
    i := i + 1;
  }
}
