// Move Zeroes to End -- Test cases

function NonZeroes(a: seq<int>): seq<int>
{
  if |a| == 0 then []
  else if a[0] != 0 then [a[0]] + NonZeroes(a[1..])
  else NonZeroes(a[1..])
}

method {:axiom} MoveZeroes(a: seq<int>) returns (result: seq<int>)
  ensures |result| == |a|
  ensures |NonZeroes(a)| <= |result|
  ensures forall i :: 0 <= i < |NonZeroes(a)| ==> result[i] == NonZeroes(a)[i]
  ensures forall i :: |NonZeroes(a)| <= i < |result| ==> result[i] == 0

method TestMixed()
{
  var a := [0, 1, 0, 3, 12];
  var r := MoveZeroes(a);
  assert |r| == 5;
}

method TestAllZeroes()
{
  var a := [0, 0, 0];
  var r := MoveZeroes(a);
  assert |r| == 3;
  assert r[0] == 0;
}

method TestNoZeroes()
{
  var a := [1, 2, 3];
  var r := MoveZeroes(a);
  assert |r| == 3;
}

method TestEmpty()
{
  var a: seq<int> := [];
  var r := MoveZeroes(a);
  assert |r| == 0;
}
