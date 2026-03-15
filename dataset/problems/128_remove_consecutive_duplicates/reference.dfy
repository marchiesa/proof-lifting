// Remove Consecutive Duplicates -- Reference solution with invariants

predicate NoConsecutiveDups(s: seq<int>)
{
  forall i :: 0 < i < |s| ==> s[i] != s[i-1]
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
    invariant 1 <= i <= |a|
    invariant |result| >= 1
    invariant result[0] == a[0]
    invariant result[|result|-1] == a[i-1]
    invariant NoConsecutiveDups(result)
    decreases |a| - i
  {
    if a[i] != a[i-1] {
      assert result[|result|-1] == a[i-1];
      assert a[i] != a[i-1];
      assert result[|result|-1] != a[i];
      result := result + [a[i]];
    }
    i := i + 1;
  }
}
