// Check if Matrix is Symmetric
// Task: Add loop invariants so that Dafny can verify this program.
// A matrix (represented as seq<seq<int>>) is symmetric if m[i][j] == m[j][i].

predicate IsSquare(m: seq<seq<int>>)
{
  forall i :: 0 <= i < |m| ==> |m[i]| == |m|
}

predicate IsSymmetric(m: seq<seq<int>>)
  requires IsSquare(m)
{
  forall i, j :: 0 <= i < |m| && 0 <= j < |m| ==> m[i][j] == m[j][i]
}

method CheckSymmetric(m: seq<seq<int>>) returns (result: bool)
  requires IsSquare(m)
  ensures result == IsSymmetric(m)
{
  var n := |m|;
  var i := 0;
  while i < n
  {
    var j := i + 1;
    while j < n
    {
      if m[i][j] != m[j][i] {
        return false;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return true;
}
