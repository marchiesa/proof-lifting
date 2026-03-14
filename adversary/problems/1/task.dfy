// Problem 1: Fuel Trap — Recursive Flatten Length
//
// Task: Add invariants (and any needed helper lemmas) so this method verifies.
// The method computes the total number of elements across all inner sequences
// (i.e., the length of the flattened sequence).

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

method ComputeFlatLen(ss: seq<seq<int>>) returns (total: nat)
  ensures total == FlatLen(ss)
  ensures total == |Flatten(ss)|
{
  total := 0;
  var i := 0;
  while i < |ss|
    // TODO: add invariants here
  {
    total := total + |ss[i]|;
    i := i + 1;
  }
}
