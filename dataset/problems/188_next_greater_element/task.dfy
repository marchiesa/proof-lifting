// Next Greater Element
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsNextGreater(a: seq<int>, i: int, v: int)
  requires 0 <= i < |a|
{
  if v == -1 then
    forall j :: i < j < |a| ==> a[j] <= a[i]
  else
    exists j :: i < j < |a| && a[j] == v && a[j] > a[i] &&
      forall k :: i < k < j ==> a[k] <= a[i]
}

method NextGreaterElement(a: seq<int>) returns (result: seq<int>)
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |a| ==> (result[i] == -1 ==> forall j :: i < j < |a| ==> a[j] <= a[i])
  ensures forall i :: 0 <= i < |a| ==> (result[i] != -1 ==> result[i] > a[i])
{
  result := [];
  var i := 0;
  while i < |a|
  {
    var found := -1;
    var j := i + 1;
    while j < |a|
    {
      if a[j] > a[i] {
        found := a[j];
        break;
      }
      j := j + 1;
    }
    result := result + [found];
    i := i + 1;
  }
}
