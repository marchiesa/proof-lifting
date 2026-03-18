ghost function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

ghost predicate NoLoss(price: int, a: seq<int>)
  requires |a| > 0
{
  price * |a| >= Sum(a)
}

ghost predicate IsMinimalEqualPrice(price: int, a: seq<int>)
  requires |a| > 0
{
  NoLoss(price, a) && !NoLoss(price - 1, a)
}

method EqualizePrice(a: seq<int>) returns (price: int)
  requires |a| > 0
  ensures IsMinimalEqualPrice(price, a)
{
  var s := 0;
  var n := |a|;
  var i := 0;
  while i < n
  {
    s := s + a[i];
    i := i + 1;
  }
  price := (s + n - 1) / n;
}