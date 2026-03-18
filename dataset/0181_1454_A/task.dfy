ghost predicate InRange(p: seq<int>, n: int)
{
  forall i | 0 <= i < |p| :: 1 <= p[i] <= n
}

ghost predicate AllDistinct(p: seq<int>)
{
  forall i, j | 0 <= i < |p| && 0 <= j < |p| && i != j :: p[i] != p[j]
}

ghost predicate IsPermutation(p: seq<int>, n: int)
{
  |p| == n && InRange(p, n) && AllDistinct(p)
}

ghost predicate NoFixedPoint(p: seq<int>)
{
  forall i | 0 <= i < |p| :: p[i] != i + 1
}

method SpecialPermutation(n: int) returns (p: seq<int>)
  requires n > 1
  ensures IsPermutation(p, n)
  ensures NoFixedPoint(p)
{
  p := [n];
  var i := 1;
  while i < n {
    p := p + [i];
    i := i + 1;
  }
}

method BuildExpected(n: int) returns (e: seq<int>)
{
  e := [n];
  var i := 1;
  while i < n {
    e := e + [i];
    i := i + 1;
  }
}