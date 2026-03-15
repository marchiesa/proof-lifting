// Maximum Gap Between Sorted Elements
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate IsPermutation(a: seq<int>, b: seq<int>)
{
  multiset(a) == multiset(b)
}

method MaxGap(a: seq<int>) returns (gap: int)
  requires |a| >= 2
  ensures gap >= 0
{
  // First sort the array
  var sorted := a;
  var i := 0;
  while i < |sorted|
  {
    var minIdx := i;
    var j := i + 1;
    while j < |sorted|
    {
      if sorted[j] < sorted[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    if minIdx != i {
      var tmp := sorted[i];
      sorted := sorted[..i] + [sorted[minIdx]] + sorted[i+1..minIdx] + [tmp] + sorted[minIdx+1..];
    }
    i := i + 1;
  }

  // Find max gap
  gap := 0;
  i := 1;
  while i < |sorted|
  {
    var diff := sorted[i] - sorted[i-1];
    if diff > gap {
      gap := diff;
    }
    i := i + 1;
  }
}
