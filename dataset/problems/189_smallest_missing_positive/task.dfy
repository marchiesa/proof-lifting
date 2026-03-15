// Smallest Missing Positive Integer
// Task: Add loop invariants so that Dafny can verify this program.

method SmallestMissing(a: seq<int>) returns (result: int)
  ensures result >= 1
  ensures forall i :: 0 <= i < |a| ==> a[i] != result
  ensures forall w :: 1 <= w < result ==> w in a
{
  result := 1;
  while result <= |a|
  {
    var found := false;
    var j := 0;
    while j < |a|
    {
      if a[j] == result {
        found := true;
        break;
      }
      j := j + 1;
    }
    if !found {
      return;
    }
    result := result + 1;
  }
}
