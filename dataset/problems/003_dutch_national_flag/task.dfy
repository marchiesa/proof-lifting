// Dutch National Flag
// Task: Add loop invariants so that Dafny can verify this program.

predicate ValidColor(c: int)
{
  c == 0 || c == 1 || c == 2
}

predicate AllValidColors(a: array<int>)
  reads a
{
  forall i :: 0 <= i < a.Length ==> ValidColor(a[i])
}

predicate IsSortedColors(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

method DutchFlag(a: array<int>)
  requires AllValidColors(a)
  modifies a
  ensures IsSortedColors(a)
  ensures AllValidColors(a)
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var lo := 0;
  var mid := 0;
  var hi := a.Length;
  while mid < hi
  {
    if a[mid] == 0 {
      a[lo], a[mid] := a[mid], a[lo];
      lo := lo + 1;
      mid := mid + 1;
    } else if a[mid] == 1 {
      mid := mid + 1;
    } else {
      hi := hi - 1;
      a[mid], a[hi] := a[hi], a[mid];
    }
  }
}
