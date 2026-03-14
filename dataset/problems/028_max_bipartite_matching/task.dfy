// Counting Sort
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method CountingSort(a: seq<int>, maxVal: int) returns (result: seq<int>)
  requires maxVal > 0
  requires forall i :: 0 <= i < |a| ==> 0 <= a[i] < maxVal
  ensures IsSorted(result)
  ensures |result| == |a|
  ensures multiset(result) == multiset(a)
{
  // Count occurrences
  var counts := seq(maxVal, _ => 0);
  var i := 0;
  while i < |a|
  {
    counts := counts[a[i] := counts[a[i]] + 1];
    i := i + 1;
  }

  // Build result from counts
  result := [];
  var v := 0;
  while v < maxVal
  {
    var c := 0;
    while c < counts[v]
    {
      result := result + [v];
      c := c + 1;
    }
    v := v + 1;
  }
}
