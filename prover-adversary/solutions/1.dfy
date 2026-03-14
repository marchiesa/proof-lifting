// Problem 1: Fuel Trap — Recursive Flatten Length

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

lemma FlatLenIsLen(ss: seq<seq<int>>)
  ensures FlatLen(ss) == |Flatten(ss)|
{
  if |ss| == 0 {
  } else {
    FlatLenIsLen(ss[1..]);
  }
}

lemma FlatLenStep(ss: seq<seq<int>>, i: nat)
  requires 0 <= i < |ss|
  ensures FlatLen(ss[..i+1]) == FlatLen(ss[..i]) + |ss[i]|
{
  if i == 0 {
    assert ss[..1] == [ss[0]];
    assert ss[..0] == [];
  } else {
    assert ss[..i+1] == [ss[0]] + ss[1..i+1];
    assert ss[..i+1][0] == ss[0];
    assert ss[..i+1][1..] == ss[1..i+1];
    assert ss[1..][..i] == ss[1..i+1];
    FlatLenStep(ss[1..], i - 1);
    assert FlatLen(ss[1..][..i]) == FlatLen(ss[1..][..i-1]) + |ss[1..][i-1]|;
    assert ss[1..][i-1] == ss[i];
    assert ss[..i][0] == ss[0];
    assert ss[..i][1..] == ss[1..i];
    assert ss[1..][..i-1] == ss[1..i];
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
  {
    FlatLenStep(ss, i);
    total := total + |ss[i]|;
    i := i + 1;
  }
  assert ss[..i] == ss;
  FlatLenIsLen(ss);
}
