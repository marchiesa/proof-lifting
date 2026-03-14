// Dutch National Flag -- Test cases

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

method {:axiom} DutchFlag(a: array<int>)
  requires AllValidColors(a)
  modifies a
  ensures IsSortedColors(a)
  ensures AllValidColors(a)
  ensures multiset(a[..]) == old(multiset(a[..]))

method TestMixed()
{
  var a := new int[] [2, 0, 1, 2, 0, 1];
  DutchFlag(a);
  assert IsSortedColors(a);
}

method TestAllSame()
{
  var a := new int[] [1, 1, 1];
  DutchFlag(a);
  assert IsSortedColors(a);
}

method TestAlreadySorted()
{
  var a := new int[] [0, 0, 1, 2, 2];
  DutchFlag(a);
  assert IsSortedColors(a);
}

method TestReversed()
{
  var a := new int[] [2, 1, 0];
  DutchFlag(a);
  assert IsSortedColors(a);
}

method TestEmpty()
{
  var a := new int[] [];
  DutchFlag(a);
  assert IsSortedColors(a);
}
