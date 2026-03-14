// Kth Smallest Element (Selection via sorting)
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// The kth smallest: at most k elements are strictly less than it
predicate IsKthSmallest(val: int, a: seq<int>, k: nat)
{
  val in multiset(a) &&
  |set i | 0 <= i < |a| && a[i] < val| <= k &&
  |set i | 0 <= i < |a| && a[i] <= val| > k
}

method KthSmallest(a: seq<int>, k: nat) returns (result: int)
  requires |a| > 0
  requires 0 <= k < |a|
  ensures result in multiset(a)
{
  // Simple approach: selection sort to find kth element
  var arr := new int[|a|];
  var idx := 0;
  while idx < |a|
  {
    arr[idx] := a[idx];
    idx := idx + 1;
  }

  // Selection sort partial: just find the min k+1 times
  var i := 0;
  while i <= k
  {
    var minIdx := i;
    var j := i + 1;
    while j < arr.Length
    {
      if arr[j] < arr[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    arr[minIdx], arr[i] := arr[i], arr[minIdx];
    i := i + 1;
  }
  result := arr[k];
}
