// Flatten Matrix -- Test cases

predicate ValidMatrix(m: seq<seq<int>>, rows: int, cols: int)
{
  |m| == rows && rows >= 0 && cols >= 0 &&
  forall i :: 0 <= i < rows ==> |m[i]| == cols
}

function FlattenSpec(m: seq<seq<int>>): seq<int>
{
  if |m| == 0 then []
  else m[0] + FlattenSpec(m[1..])
}

method {:axiom} Flatten(m: seq<seq<int>>, rows: int, cols: int) returns (result: seq<int>)
  requires ValidMatrix(m, rows, cols)
  ensures result == FlattenSpec(m)
  ensures |result| == rows * cols

method TestBasic()
{
  var m := [[1, 2, 3], [4, 5, 6]];
  var r := Flatten(m, 2, 3);
  assert |r| == 6;
}

method TestSingleRow()
{
  var m := [[1, 2, 3]];
  var r := Flatten(m, 1, 3);
  assert |r| == 3;
}

method TestEmpty()
{
  var m: seq<seq<int>> := [];
  var r := Flatten(m, 0, 0);
  assert |r| == 0;
}

method TestSingleElement()
{
  var m := [[42]];
  var r := Flatten(m, 1, 1);
  assert |r| == 1;
}
