// Run-Length Compress -- Test cases

function Expand(vals: seq<int>, counts: seq<nat>): seq<int>
  requires |vals| == |counts|
  decreases |vals|
{
  if |vals| == 0 then []
  else Repeat(vals[0], counts[0]) + Expand(vals[1..], counts[1..])
}

function Repeat(v: int, n: nat): seq<int>
  decreases n
{
  if n == 0 then [] else [v] + Repeat(v, n - 1)
}

predicate NoAdjacentDups(vals: seq<int>)
{
  forall i :: 0 <= i < |vals| - 1 ==> vals[i] != vals[i + 1]
}

predicate AllPositive(counts: seq<nat>)
{
  forall i :: 0 <= i < |counts| ==> counts[i] > 0
}

method {:axiom} Compress(s: seq<int>) returns (vals: seq<int>, counts: seq<nat>)
  ensures |vals| == |counts|
  ensures NoAdjacentDups(vals)
  ensures AllPositive(counts)
  ensures Expand(vals, counts) == s

method TestBasic()
{
  var vals, counts := Compress([1, 1, 2, 3, 3, 3]);
  assert Expand(vals, counts) == [1, 1, 2, 3, 3, 3];
}

method TestSingle()
{
  var vals, counts := Compress([5]);
  assert Expand(vals, counts) == [5];
}

method TestEmpty()
{
  var vals, counts := Compress([]);
  assert |vals| == 0;
}
