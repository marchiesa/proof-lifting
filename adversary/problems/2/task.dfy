// Problem 2: Missing Triggers — Partition Into Evens and Odds
//
// Task: Add invariants and any needed assertions so this method verifies.
// The method partitions a sequence into even and odd elements, and must prove
// that every element from the original appears in exactly one partition.

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
    // TODO: add invariants here
  {
    if s[i] % 2 == 0 {
      evens := evens + [s[i]];
    } else {
      odds := odds + [s[i]];
    }
    i := i + 1;
  }
}
