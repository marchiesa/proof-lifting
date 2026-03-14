// Sliding Window Maximum -- Test cases

function SeqMax(s: seq<int>): int
  requires |s| > 0
{
  if |s| == 1 then s[0]
  else
    var rest := SeqMax(s[1..]);
    if s[0] > rest then s[0] else rest
}

method {:axiom} SlidingMax(a: seq<int>, w: int) returns (result: seq<int>)
  requires |a| > 0
  requires 1 <= w <= |a|
  ensures |result| == |a| - w + 1
  ensures forall i :: 0 <= i < |result| ==> result[i] == SeqMax(a[i..i + w])

method TestBasic()
{
  var a := [1, 3, -1, -3, 5, 3, 6, 7];
  var r := SlidingMax(a, 3);
  assert |r| == 6;
}

method TestWindowOne()
{
  var a := [1, 2, 3];
  var r := SlidingMax(a, 1);
  assert |r| == 3;
  // Each window is a single element
  assert a[0..1] == [1];
  assert SeqMax([1]) == 1;
  assert r[0] == 1;
}

method TestFullWindow()
{
  var a := [1, 2, 3];
  var r := SlidingMax(a, 3);
  assert |r| == 1;
}

method TestSingleElement()
{
  var a := [42];
  var r := SlidingMax(a, 1);
  assert |r| == 1;
  assert a[0..1] == [42];
  assert r[0] == SeqMax([42]);
}
