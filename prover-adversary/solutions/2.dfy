// Problem 2: Missing Triggers — Partition Into Evens and Odds

method Partition(s: seq<int>) returns (evens: seq<int>, odds: seq<int>)
  ensures |evens| + |odds| == |s|
  ensures forall x :: x in evens ==> x % 2 == 0
  ensures forall x :: x in odds ==> x % 2 != 0
  ensures multiset(evens) + multiset(odds) == multiset(s)
{
  evens := [];
  odds := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |evens| + |odds| == i
    invariant forall x :: x in evens ==> x % 2 == 0
    invariant forall x :: x in odds ==> x % 2 != 0
    invariant multiset(evens) + multiset(odds) == multiset(s[..i])
  {
    if s[i] % 2 == 0 {
      evens := evens + [s[i]];
    } else {
      odds := odds + [s[i]];
    }
    i := i + 1;
    assert s[..i] == s[..i-1] + [s[i-1]];
  }
  assert s[..i] == s;
}
