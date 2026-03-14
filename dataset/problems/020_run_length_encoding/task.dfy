// Run-Length Encoding
// Task: Add loop invariants so that Dafny can verify this program.

// Expand an RLE encoding back to the original sequence
function Expand(values: seq<int>, counts: seq<int>): seq<int>
  requires |values| == |counts|
  requires forall i :: 0 <= i < |counts| ==> counts[i] > 0
  decreases |values|
{
  if |values| == 0 then []
  else Repeat(values[0], counts[0]) + Expand(values[1..], counts[1..])
}

// Repeat a value n times
function Repeat(v: int, n: int): seq<int>
  requires n > 0
  decreases n
{
  if n == 1 then [v]
  else [v] + Repeat(v, n - 1)
}

method RLE(a: seq<int>) returns (values: seq<int>, counts: seq<int>)
  ensures |values| == |counts|
  ensures forall i :: 0 <= i < |counts| ==> counts[i] > 0
  ensures forall i :: 0 <= i < |values| - 1 ==> values[i] != values[i + 1]
  ensures Expand(values, counts) == a
{
  if |a| == 0 {
    values := [];
    counts := [];
    return;
  }

  values := [a[0]];
  counts := [1];
  var i := 1;

  while i < |a|
  {
    if a[i] == values[|values| - 1] {
      counts := counts[|counts| - 1 := counts[|counts| - 1] + 1];
    } else {
      values := values + [a[i]];
      counts := counts + [1];
    }
    i := i + 1;
  }
}
