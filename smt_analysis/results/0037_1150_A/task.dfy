ghost function Outcome(r: int, buyPrice: int, sellPrice: int, shares: int): int
{
  r - shares * buyPrice + shares * sellPrice
}

ghost predicate ValidTrade(r: int, buyPrice: int, shares: int)
{
  buyPrice > 0 && shares >= 0 && shares * buyPrice <= r
}

ghost predicate IsAchievable(result: int, r: int, s: seq<int>, b: seq<int>)
{
  result == r
  ||
  (exists i | 0 <= i < |s| :: exists j | 0 <= j < |b| :: exists k: nat ::
    ValidTrade(r, s[i], k) && result == Outcome(r, s[i], b[j], k))
}

ghost predicate IsOptimal(result: int, r: int, s: seq<int>, b: seq<int>)
{
  result >= r
  &&
  (forall i | 0 <= i < |s| :: forall j | 0 <= j < |b| :: forall k: nat ::
    ValidTrade(r, s[i], k) ==> Outcome(r, s[i], b[j], k) <= result)
}

method StockArbitraging(n: int, m: int, r: int, s: seq<int>, b: seq<int>) returns (maxBourles: int)
  requires |s| == n && n >= 1
  requires |b| == m && m >= 1
  requires r >= 1
  requires forall i | 0 <= i < n :: s[i] >= 1
  requires forall j | 0 <= j < m :: b[j] >= 1
  ensures IsAchievable(maxBourles, r, s, b)
  ensures IsOptimal(maxBourles, r, s, b)
{
  var minS := s[0];
  var i := 1;
  while i < |s|
  {
    if s[i] < minS {
      minS := s[i];
    }
    i := i + 1;
  }

  var maxB := b[0];
  i := 1;
  while i < |b|
  {
    if b[i] > maxB {
      maxB := b[i];
    }
    i := i + 1;
  }

  var profit := r % minS + (r / minS) * maxB;
  if profit > r {
    maxBourles := profit;
  } else {
    maxBourles := r;
  }
}