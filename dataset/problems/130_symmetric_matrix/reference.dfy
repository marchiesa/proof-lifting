// Check if Matrix is Symmetric -- Reference solution with invariants

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
    invariant 0 <= i <= n
    invariant forall r, c :: 0 <= r < i && 0 <= c < n ==> m[r][c] == m[c][r]
    decreases n - i
  {
    var j := i + 1;
    while j < n
      invariant i + 1 <= j <= n
      invariant forall c :: i + 1 <= c < j ==> m[i][c] == m[c][i]
      decreases n - j
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
