ghost function DotProduct(a: seq<int>, b: seq<int>): int
  requires |a| == |b|
  decreases |a|
{
  if |a| == 0 then 0
  else DotProduct(a[..|a|-1], b[..|b|-1]) + a[|a|-1] * b[|b|-1]
}

ghost predicate AllNonZero(s: seq<int>) {
  forall i | 0 <= i < |s| :: s[i] != 0
}

ghost predicate AllBounded(s: seq<int>, bound: int) {
  forall i | 0 <= i < |s| :: -bound <= s[i] <= bound
}

ghost predicate ValidSolution(a: seq<int>, b: seq<int>) {
  |a| == |b|
  && AllNonZero(b)
  && AllBounded(b, 100)
  && DotProduct(a, b) == 0
}

method FindSasuke(a: seq<int>) returns (b: seq<int>)
  requires |a| % 2 == 0
  requires AllNonZero(a)
  requires AllBounded(a, 100)
  ensures ValidSolution(a, b)
{
  b := [];
  var i := 0;
  while i < |a|
  {
    if i % 2 == 0 {
      b := b + [a[i + 1]];
    } else {
      b := b + [-a[i - 1]];
    }
    i := i + 1;
  }
}