// Next Greater Element -- Reference solution with invariants

method NextGreaterElement(a: seq<int>) returns (result: seq<int>)
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |a| ==> (result[i] == -1 ==> forall j :: i < j < |a| ==> a[j] <= a[i])
  ensures forall i :: 0 <= i < |a| ==> (result[i] != -1 ==> result[i] > a[i])
{
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> (result[k] == -1 ==> forall j :: k < j < |a| ==> a[j] <= a[k])
    invariant forall k :: 0 <= k < i ==> (result[k] != -1 ==> result[k] > a[k])
    decreases |a| - i
  {
    var found := -1;
    var j := i + 1;
    while j < |a|
      invariant i + 1 <= j <= |a|
      invariant found == -1 ==> forall k :: i + 1 <= k < j ==> a[k] <= a[i]
      invariant found != -1 ==> found > a[i]
      decreases |a| - j
    {
      if a[j] > a[i] && found == -1 {
        found := a[j];
      }
      j := j + 1;
    }
    result := result + [found];
    i := i + 1;
  }
}
