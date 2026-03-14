// Problem 1: Fuel Trap — Recursive Flatten Length (SOLUTION)
//
// The obvious invariants are:
//   invariant total == FlatLen(ss[..i])
//   invariant total == |Flatten(ss[..i])|
//
// These fail because the recursive functions are defined by peeling off
// the FIRST element (ss[0] + recurse(ss[1..])), but the loop appends
// at position i. Dafny's fuel can't bridge the gap between
// ss[..i+1] and ss[..i] — it would need to fully unroll the recursion
// from index 0 to i+1 to see that FlatLen(ss[..i+1]) == FlatLen(ss[..i]) + |ss[i]|.
//
// Fix: Provide explicit inductive lemmas that prove the step property.

function Flatten(ss: seq<seq<int>>): seq<int>
{
  if |ss| == 0 then []
  else ss[0] + Flatten(ss[1..])
}

function FlatLen(ss: seq<seq<int>>): nat
{
  if |ss| == 0 then 0
  else |ss[0]| + FlatLen(ss[1..])
}

lemma FlatLenStep(ss: seq<seq<int>>, i: nat)
  requires 0 <= i < |ss|
  ensures FlatLen(ss[..i+1]) == FlatLen(ss[..i]) + |ss[i]|
{
  if i == 0 {
    assert ss[..1] == [ss[0]];
    assert ss[..0] == [];
  } else {
    assert ss[..i+1][0] == ss[0];
    assert ss[..i+1][1..] == ss[1..][..i];
    assert ss[..i][0] == ss[0];
    assert ss[..i][1..] == ss[1..][..i-1];
    FlatLenStep(ss[1..], i - 1);
  }
}

lemma FlattenStep(ss: seq<seq<int>>, i: nat)
  requires 0 <= i < |ss|
  ensures Flatten(ss[..i+1]) == Flatten(ss[..i]) + ss[i]
{
  if i == 0 {
    assert ss[..1] == [ss[0]];
    assert ss[..0] == [];
  } else {
    assert ss[..i+1][0] == ss[0];
    assert ss[..i+1][1..] == ss[1..][..i];
    assert ss[..i][0] == ss[0];
    assert ss[..i][1..] == ss[1..][..i-1];
    FlattenStep(ss[1..], i - 1);
  }
}

method ComputeFlatLen(ss: seq<seq<int>>) returns (total: nat)
  ensures total == FlatLen(ss)
  ensures total == |Flatten(ss)|
{
  total := 0;
  var i := 0;
  while i < |ss|
    invariant 0 <= i <= |ss|
    invariant total == FlatLen(ss[..i])
    invariant total == |Flatten(ss[..i])|
  {
    FlatLenStep(ss, i);
    FlattenStep(ss, i);
    total := total + |ss[i]|;
    i := i + 1;
  }
  assert ss[..|ss|] == ss;
}
