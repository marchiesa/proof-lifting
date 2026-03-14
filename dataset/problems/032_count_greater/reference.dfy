// Count Elements Greater Than Threshold -- Reference solution with invariants

function CountGreater(s: seq<int>, threshold: int): nat
{
  if |s| == 0 then 0
  else (if s[0] > threshold then 1 else 0) + CountGreater(s[1..], threshold)
}

lemma CountGreaterSplit(s: seq<int>, threshold: int, k: int)
  requires 0 <= k <= |s|
  ensures CountGreater(s, threshold) == CountGreater(s[..k], threshold) + CountGreater(s[k..], threshold)
{
  if k == 0 {
    assert s[..0] == [];
    assert s[0..] == s;
  } else if k == |s| {
    assert s[..|s|] == s;
    assert s[|s|..] == [];
  } else {
    assert s[..k] == [s[0]] + s[1..k];
    CountGreaterSplit(s[1..], threshold, k - 1);
    assert s[1..][..k-1] == s[1..k];
    assert s[1..][k-1..] == s[k..];
  }
}

method CountGreaterThan(a: seq<int>, threshold: int) returns (count: nat)
  ensures count == CountGreater(a, threshold)
{
  count := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant count == CountGreater(a[..i], threshold)
    decreases |a| - i
  {
    assert a[..i+1] == a[..i] + [a[i]];
    CountGreaterSplit(a[..i+1], threshold, i);
    assert a[..i+1][..i] == a[..i];
    assert a[..i+1][i..] == [a[i]];
    if a[i] > threshold {
      count := count + 1;
    }
    i := i + 1;
  }
  assert a[..|a|] == a;
}
