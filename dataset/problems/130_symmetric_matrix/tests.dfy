// Check if Matrix is Symmetric -- Test cases

predicate IsSquare(m: seq<seq<int>>)
{
  forall i :: 0 <= i < |m| ==> |m[i]| == |m|
}

predicate IsSymmetric(m: seq<seq<int>>)
  requires IsSquare(m)
{
  forall i, j :: 0 <= i < |m| && 0 <= j < |m| ==> m[i][j] == m[j][i]
}

method Main()
{
  // Test IsSquare
  var m1: seq<seq<int>> := [];
  expect IsSquare(m1), "Empty is square";
  var m2 := [[1]];
  expect IsSquare(m2), "1x1 is square";
  var m3 := [[1, 2], [3, 4]];
  expect IsSquare(m3), "2x2 is square";
  var m4 := [[1, 2], [3]];
  expect !IsSquare(m4), "Jagged is not square";

  // Test IsSymmetric - positive
  expect IsSymmetric(m1), "Empty is symmetric";
  expect IsSymmetric(m2), "1x1 is symmetric";
  var s1 := [[1, 2], [2, 3]];
  expect IsSquare(s1);
  expect IsSymmetric(s1), "[[1,2],[2,3]] is symmetric";
  var s2 := [[1, 0, 3], [0, 5, 0], [3, 0, 7]];
  expect IsSquare(s2);
  expect IsSymmetric(s2), "3x3 symmetric matrix";

  // Test IsSymmetric - negative
  expect IsSquare(m3);
  expect !IsSymmetric(m3), "[[1,2],[3,4]] not symmetric (2 != 3)";
  var ns := [[1, 2, 3], [2, 5, 6], [3, 7, 9]];
  expect IsSquare(ns);
  expect !IsSymmetric(ns), "[[1,2,3],[2,5,6],[3,7,9]] not symmetric (6 != 7)";

  print "All spec tests passed\n";
}
