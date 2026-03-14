// Partition Around Pivot
// Task: Add loop invariants so that Dafny can verify this program.

method Partition(a: seq<int>, pivot: int) returns (result: seq<int>, splitIdx: int)
  ensures |result| == |a|
  ensures 0 <= splitIdx <= |a|
  ensures forall i :: 0 <= i < splitIdx ==> result[i] <= pivot
  ensures forall i :: splitIdx <= i < |result| ==> result[i] > pivot
  ensures multiset(result) == multiset(a)
{
  var lo: seq<int> := [];
  var hi: seq<int> := [];
  var i := 0;
  while i < |a|
  {
    if a[i] <= pivot {
      lo := lo + [a[i]];
    } else {
      hi := hi + [a[i]];
    }
    i := i + 1;
  }
  result := lo + hi;
  splitIdx := |lo|;
}
