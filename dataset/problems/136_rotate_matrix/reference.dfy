// Rotate Matrix 90 Degrees -- Reference solution with invariants

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
    invariant 0 <= i <= n
    invariant |r| == i
    invariant forall k :: 0 <= k < i ==> |r[k]| == n
    invariant forall k, l :: 0 <= k < i && 0 <= l < n ==> r[k][l] == m[n - 1 - l][k]
    decreases n - i
  {
    var row: seq<int> := [];
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |row| == j
      invariant forall l :: 0 <= l < j ==> row[l] == m[n - 1 - l][i]
      decreases n - j
    {
      row := row + [m[n - 1 - j][i]];
      j := j + 1;
    }
    r := r + [row];
    i := i + 1;
  }
}
