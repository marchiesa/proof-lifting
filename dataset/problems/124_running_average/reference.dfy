// Running Average (Partial Sums) -- Reference solution with invariants

function Sum(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else s[0] + Sum(s[1..])
}

predicate IsPartialSums(a: seq<int>, result: seq<int>)
{
  |result| == |a| &&
  forall i :: 0 <= i < |a| ==> result[i] == Sum(a[..i+1])
}

lemma SumAppend(s: seq<int>, v: int)
  ensures Sum(s + [v]) == Sum(s) + v
  decreases |s|
{
  if |s| == 0 {
    assert s + [v] == [v];
  } else {
    assert (s + [v])[1..] == s[1..] + [v];
    SumAppend(s[1..], v);
  }
}

lemma SumPrefix(a: seq<int>, i: int)
  requires 0 <= i < |a|
  ensures Sum(a[..i+1]) == Sum(a[..i]) + a[i]
{
  assert a[..i+1] == a[..i] + [a[i]];
  SumAppend(a[..i], a[i]);
}

method PartialSums(a: seq<int>) returns (result: seq<int>)
  ensures IsPartialSums(a, result)
{
  result := [];
  var running := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant running == Sum(a[..i])
    invariant forall j :: 0 <= j < i ==> result[j] == Sum(a[..j+1])
    decreases |a| - i
  {
    SumPrefix(a, i);
    running := running + a[i];
    result := result + [running];
    i := i + 1;
  }
}
