// Problem 5: Map/Set Reasoning Gaps — Histogram (SOLUTION)
//
// The obvious invariants are:
//   forall x :: x in hist <==> x in s[..i]
//   forall x :: x in hist ==> hist[x] == CountIn(s[..i], x)
//
// These are correct but Z3 cannot prove maintenance because:
// 1. CountIn is recursive and Z3 can't unfold it for s[..i+1] vs s[..i]
// 2. Map domain reasoning (what's in hist after an update) is weak
// 3. When key !in hist, Z3 can't derive CountIn(s[..i], key) == 0
//
// Fix: Multiple helper lemmas + explicit forall proofs inside the loop.

function CountIn(s: seq<int>, x: int): nat
{
  if |s| == 0 then 0
  else (if s[0] == x then 1 else 0) + CountIn(s[1..], x)
}

lemma CountInStep(s: seq<int>, i: nat, x: int)
  requires 0 <= i < |s|
  ensures CountIn(s[..i+1], x) == CountIn(s[..i], x) + (if s[i] == x then 1 else 0)
{
  if i == 0 {
    assert s[..1] == [s[0]];
    assert s[..0] == [];
  } else {
    assert s[..i+1][0] == s[0];
    assert s[..i+1][1..] == s[1..][..i];
    assert s[..i][0] == s[0];
    assert s[..i][1..] == s[1..][..i-1];
    CountInStep(s[1..], i-1, x);
  }
}

lemma CountInZero(s: seq<int>, x: int)
  requires x !in s
  ensures CountIn(s, x) == 0
{
  if |s| > 0 {
    assert s[0] != x;
    CountInZero(s[1..], x);
  }
}

method Histogram(s: seq<int>) returns (hist: map<int, nat>)
  ensures forall x :: x in hist <==> x in s
  ensures forall x :: x in hist ==> hist[x] == CountIn(s, x)
{
  hist := map[];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall x :: x in hist <==> x in s[..i]
    invariant forall x :: x in hist ==> hist[x] == CountIn(s[..i], x)
  {
    var key := s[i];
    CountInStep(s, i, key);

    if key in hist {
      hist := hist[key := hist[key] + 1];
      // Prove count invariant maintained for ALL keys after map update
      forall x | x in hist
        ensures hist[x] == CountIn(s[..i+1], x)
      {
        if x == key {
        } else {
          CountInStep(s, i, x);
        }
      }
    } else {
      // When key wasn't in hist, we need to know CountIn(s[..i], key) == 0
      CountInZero(s[..i], key);
      hist := hist[key := 1];
      forall x | x in hist
        ensures hist[x] == CountIn(s[..i+1], x)
      {
        if x == key {
        } else {
          CountInStep(s, i, x);
        }
      }
    }
    // Prove domain invariant maintained
    assert forall x :: x in hist <==> x in s[..i+1] by {
      forall x
        ensures x in hist <==> x in s[..i+1]
      {
        assert s[..i+1] == s[..i] + [s[i]];
      }
    }
    i := i + 1;
  }
  assert s[..|s|] == s;
}
