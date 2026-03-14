// Merge Two Sorted Arrays Into One Sorted Array
// Task: Add loop invariants so that Dafny can verify this program.
// (Similar to 015 but operates on arrays instead of sequences)

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method MergeArrays(a: array<int>, b: array<int>) returns (c: array<int>)
  requires IsSorted(a[..])
  requires IsSorted(b[..])
  ensures IsSorted(c[..])
  ensures c.Length == a.Length + b.Length
  ensures multiset(c[..]) == multiset(a[..]) + multiset(b[..])
{
  c := new int[a.Length + b.Length];
  var i := 0;
  var j := 0;
  var k := 0;
  while k < c.Length
  {
    if i < a.Length && (j >= b.Length || a[i] <= b[j]) {
      c[k] := a[i];
      i := i + 1;
    } else {
      c[k] := b[j];
      j := j + 1;
    }
    k := k + 1;
  }
}
