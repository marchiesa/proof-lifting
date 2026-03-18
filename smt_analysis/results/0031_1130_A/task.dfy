ghost predicate IsPositiveAfterDiv(x: int, d: int)
  requires d != 0
{
  (x > 0 && d > 0) || (x < 0 && d < 0)
}

ghost function CountPositiveAfterDiv(a: seq<int>, d: int): int
  requires d != 0
  decreases |a|
{
  if |a| == 0 then 0
  else CountPositiveAfterDiv(a[..|a|-1], d)
       + (if IsPositiveAfterDiv(a[|a|-1], d) then 1 else 0)
}

ghost function CeilHalf(n: int): int
{
  (n + 1) / 2
}

method BePositive(a: seq<int>) returns (d: int)
  ensures d != 0 ==> -1000 <= d <= 1000
                      && CountPositiveAfterDiv(a, d) >= CeilHalf(|a|)
  ensures d == 0 ==> (forall d' :: d' == 0 || CountPositiveAfterDiv(a, d') < CeilHalf(|a|))
{
  var n := |a|;
  var pcount := 0;
  var ncount := 0;
  var zcount := 0;
  var i := 0;
  while i < n
  {
    if a[i] > 0 {
      pcount := pcount + 1;
    } else if a[i] < 0 {
      ncount := ncount + 1;
    } else {
      zcount := zcount + 1;
    }
    i := i + 1;
  }
  var half := (n + 1) / 2;
  if pcount >= half {
    d := 1;
  } else if ncount >= half {
    d := -1;
  } else {
    d := 0;
  }
}