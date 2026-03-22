method FindWitness(a: seq<int>, v: int) returns (found: bool)
  requires |a| > 0
  requires exists i :: 0 <= i < |a| && a[i] == v
  ensures found ==> exists i :: 0 <= i < |a| && a[i] == v
{
  found := false;
  var j := 0;
  while j < |a|
    invariant 0 <= j <= |a|
    invariant found ==> exists i :: 0 <= i < |a| && a[i] == v
  {
    if a[j] == v {
      assert exists i :: 0 <= i < |a| && a[i] == v;
      found := true;
    }
    j := j + 1;
  }
}