// Flatten Matrix -- Runtime spec tests

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

// Bounded ValidMatrix for runtime
function ValidMatrixBounded(m: seq<seq<int>>, rows: int, cols: int): bool
{
  |m| == rows && rows >= 0 && cols >= 0 &&
  ValidMatrixRows(m, rows, cols, 0)
}

function ValidMatrixRows(m: seq<seq<int>>, rows: int, cols: int, i: int): bool
  requires 0 <= i <= |m|
  decreases |m| - i
{
  if i == rows then true
  else if i >= |m| then true
  else |m[i]| == cols && ValidMatrixRows(m, rows, cols, i + 1)
}

method Main()
{
  // FlattenSpec: basic 2x3 matrix
  var m := [[1, 2, 3], [4, 5, 6]];
  expect FlattenSpec(m) == [1, 2, 3, 4, 5, 6], "Flatten 2x3 matrix";

  // FlattenSpec: single row
  expect FlattenSpec([[1, 2, 3]]) == [1, 2, 3], "Flatten single row";

  // FlattenSpec: single column
  expect FlattenSpec([[1], [2], [3]]) == [1, 2, 3], "Flatten single column";

  // FlattenSpec: single element
  expect FlattenSpec([[42]]) == [42], "Flatten single element";

  // FlattenSpec: empty
  expect FlattenSpec([]) == [], "Flatten empty matrix";

  // FlattenSpec: negative test
  expect FlattenSpec([[1, 2], [3, 4]]) != [1, 3, 2, 4], "Flatten should be row-major, not column-major";
  expect FlattenSpec([[1, 2], [3, 4]]) == [1, 2, 3, 4], "Flatten is row-major";

  // FlattenSpec: length check
  expect |FlattenSpec([[1, 2, 3], [4, 5, 6]])| == 6, "Flatten length should be rows * cols";

  print "All spec tests passed\n";
}
