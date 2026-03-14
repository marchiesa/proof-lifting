// Reverse Sequence -- Reference solution with invariants

function ReverseSpec(a: seq<int>): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else ReverseSpec(a[1..]) + [a[0]]
}

method ReverseSeq(a: seq<int>) returns (r: seq<int>)
  ensures |r| == |a|
  ensures forall i :: 0 <= i < |a| ==> r[i] == a[|a| - 1 - i]
{
  r := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |r| == i
    invariant forall j :: 0 <= j < i ==> r[j] == a[|a| - 1 - j]
    decreases |a| - i
  {
    r := r + [a[|a| - 1 - i]];
    i := i + 1;
  }
}
