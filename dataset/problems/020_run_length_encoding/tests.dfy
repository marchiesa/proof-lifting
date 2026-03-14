// Run-Length Encoding -- Test cases

function Repeat(v: int, n: int): seq<int>
  requires n > 0
  decreases n
{
  if n == 1 then [v]
  else [v] + Repeat(v, n - 1)
}

function Expand(values: seq<int>, counts: seq<int>): seq<int>
  requires |values| == |counts|
  requires forall i :: 0 <= i < |counts| ==> counts[i] > 0
  decreases |values|
{
  if |values| == 0 then []
  else Repeat(values[0], counts[0]) + Expand(values[1..], counts[1..])
}

method {:axiom} RLE(a: seq<int>) returns (values: seq<int>, counts: seq<int>)
  ensures |values| == |counts|
  ensures forall i :: 0 <= i < |counts| ==> counts[i] > 0
  ensures forall i :: 0 <= i < |values| - 1 ==> values[i] != values[i + 1]
  ensures Expand(values, counts) == a

method TestWithRuns()
{
  var a := [1, 1, 2, 2, 2, 3];
  var vals, cnts := RLE(a);
  assert Expand(vals, cnts) == a;
}

method TestSingle()
{
  var a := [5];
  var vals, cnts := RLE(a);
  assert Expand(vals, cnts) == a;
  assert |vals| == |cnts|;
}

method TestEmpty()
{
  var a: seq<int> := [];
  var vals, cnts := RLE(a);
  assert Expand(vals, cnts) == a;
  assert |vals| == 0;
}

method TestAlternating()
{
  var a := [1, 2, 1];
  var vals, cnts := RLE(a);
  assert Expand(vals, cnts) == a;
}
