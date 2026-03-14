// Find Peak Element -- Test cases

predicate IsPeak(a: array<int>, i: int)
  reads a
  requires 0 <= i < a.Length
{
  (i == 0 || a[i] > a[i - 1]) && (i == a.Length - 1 || a[i] > a[i + 1])
}

method {:axiom} FindPeak(a: array<int>) returns (p: int)
  requires a.Length >= 1
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] != a[j]
  ensures 0 <= p < a.Length
  ensures IsPeak(a, p)

method TestMiddlePeak()
{
  var a := new int[] [1, 3, 2];
  var p := FindPeak(a);
  assert IsPeak(a, p);
}

method TestLeftPeak()
{
  var a := new int[] [5, 1, 2];
  var p := FindPeak(a);
  assert IsPeak(a, p);
}

method TestRightPeak()
{
  var a := new int[] [1, 2, 5];
  var p := FindPeak(a);
  assert IsPeak(a, p);
}

method TestSingleElement()
{
  var a := new int[] [42];
  var p := FindPeak(a);
  assert p == 0;
  assert IsPeak(a, p);
}
