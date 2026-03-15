// Rotate Matrix 90 Degrees
// Task: Add loop invariants so that Dafny can verify this program.
// Rotate an n x n matrix 90 degrees clockwise.

predicate IsSquare(m: seq<seq<int>>)
{
  forall i :: 0 <= i < |m| ==> |m[i]| == |m|
}

predicate IsRotated90(orig: seq<seq<int>>, rotated: seq<seq<int>>)
  requires IsSquare(orig)
  requires IsSquare(rotated)
  requires |orig| == |rotated|
{
  forall i, j :: 0 <= i < |orig| && 0 <= j < |orig| ==>
    rotated[j][|orig| - 1 - i] == orig[i][j]
}

method RotateMatrix(m: seq<seq<int>>) returns (r: seq<seq<int>>)
  requires IsSquare(m)
  ensures IsSquare(r)
  ensures |r| == |m|
  ensures IsRotated90(m, r)
{
  var n := |m|;
  r := [];
  var i := 0;
  while i < n
  {
    var row: seq<int> := [];
    var j := 0;
    while j < n
    {
      row := row + [m[n - 1 - j][i]];
      j := j + 1;
    }
    r := r + [row];
    i := i + 1;
  }
}
