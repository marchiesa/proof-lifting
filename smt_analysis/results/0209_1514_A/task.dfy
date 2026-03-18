ghost function Pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

ghost predicate BitSet(mask: nat, i: nat)
{
  (mask / Pow2(i)) % 2 == 1
}

ghost function SubseqProduct(a: seq<int>, mask: nat): int
  decreases |a|
{
  if |a| == 0 then 1
  else if BitSet(mask, |a| - 1) then SubseqProduct(a[..|a|-1], mask) * a[|a|-1]
  else SubseqProduct(a[..|a|-1], mask)
}

ghost predicate IsPerfectSquare(x: int)
{
  x >= 0 && exists s: nat :: s * s == x
}

ghost predicate HasNonPerfectSquareSubseqProduct(a: seq<int>)
{
  exists mask: nat | 1 <= mask < Pow2(|a|) :: !IsPerfectSquare(SubseqProduct(a, mask))
}

method PerfectlyImperfectArray(a: seq<int>) returns (result: bool)
  ensures result == HasNonPerfectSquareSubseqProduct(a)
{
  result := false;
  var i := 0;
  while i < |a|
  {
    var x := a[i];
    var s := 0;
    while s * s < x
    {
      s := s + 1;
    }
    if s * s != x {
      result := true;
      return;
    }
    i := i + 1;
  }
}