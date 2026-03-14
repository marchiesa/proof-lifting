// Problem 2: Missing Triggers — Partition Into Evens and Odds (SOLUTION)
//
// The obvious invariant is:
//   multiset(evens) + multiset(odds) == multiset(s[..i])
//
// This is logically correct but the inductive step fails. Z3 cannot
// automatically deduce that multiset(s[..i+1]) == multiset(s[..i]) + multiset{s[i]}
// because this requires knowing that s[..i+1] == s[..i] + [s[i]], which is a
// sequence identity that Z3 doesn't have a trigger for in the multiset context.
//
// Fix: Add the assertion `s[..i+1] == s[..i] + [s[i]]` inside the loop.
// This gives Z3 the connection between the slice at i+1 and the slice at i,
// which then triggers the multiset decomposition axiom.

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
    // This single assertion is the entire fix — it triggers the
    // multiset decomposition axiom that Z3 can't find on its own
    assert s[..i+1] == s[..i] + [s[i]];
    if s[i] % 2 == 0 {
      evens := evens + [s[i]];
    } else {
      odds := odds + [s[i]];
    }
    i := i + 1;
  }
  assert s[..|s|] == s;
}
