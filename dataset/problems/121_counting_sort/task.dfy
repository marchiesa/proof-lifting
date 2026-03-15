// Counting Sort
// Task: Add loop invariants so that Dafny can verify this program.
// Sort integers known to be in range [0, k) using counting sort.

predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate InRange(s: seq<int>, k: int)
{
  forall i :: 0 <= i < |s| ==> 0 <= s[i] < k
}

method CountingSort(a: seq<int>, k: int) returns (result: seq<int>)
  requires k > 0
  requires InRange(a, k)
  ensures IsSorted(result)
  ensures |result| == |a|
  ensures multiset(result) == multiset(a)
{
  var counts := new int[k](i => 0);

  var i := 0;
  while i < |a|
  {
    counts[a[i]] := counts[a[i]] + 1;
    i := i + 1;
  }

  result := [];
  var c := 0;
  while c < k
  {
    var j := 0;
    while j < counts[c]
    {
      result := result + [c];
      j := j + 1;
    }
    c := c + 1;
  }
}
