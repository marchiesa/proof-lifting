// Rotate Matrix 90 Degrees -- Test cases

predicate IsSquare(m: seq<seq<int>>)
{
  forall i :: 0 <= i < |m| ==> |m[i]| == |m|
}

predicate IsRotated90(orig: seq<seq<int>>, rotated: seq<seq<int>>)
  requires IsSquare(orig) && IsSquare(rotated) && |orig| == |rotated|
{
  forall i, j :: 0 <= i < |orig| && 0 <= j < |orig| ==>
    rotated[j][|orig| - 1 - i] == orig[i][j]
}

method Main()
{
  // 2x2 rotation
  var m := [[1, 2], [3, 4]];
  var r := [[3, 1], [4, 2]];
  expect IsSquare(m), "m is square";
  expect IsSquare(r), "r is square";
  expect IsRotated90(m, r), "r is m rotated 90 degrees";

  // Negative: wrong rotation
  var wrong := [[1, 3], [2, 4]];
  expect IsSquare(wrong);
  expect !IsRotated90(m, wrong), "wrong is not a 90 degree rotation";

  // 1x1 rotation
  var m1 := [[5]];
  expect IsSquare(m1);
  expect IsRotated90(m1, m1), "1x1 rotation is identity";

  // Empty
  var empty: seq<seq<int>> := [];
  expect IsSquare(empty);

  print "All spec tests passed\n";
}
