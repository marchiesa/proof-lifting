ghost function Max(x: int, y: int): int {
  if x >= y then x else y
}

// The maximum number of games purchasable from costs c using bills a
// (in order). At each game, we may buy it (if the current bill covers
// the cost, consuming that bill) or skip it. This explores ALL valid
// purchasing strategies and returns the maximum count.
ghost function MaxPurchases(c: seq<int>, a: seq<int>): int
  decreases |c|
{
  if |c| == 0 || |a| == 0 then 0
  else if a[0] >= c[0] then
    Max(1 + MaxPurchases(c[1..], a[1..]), MaxPurchases(c[1..], a))
  else
    MaxPurchases(c[1..], a)
}

method GameShopping(c: seq<int>, a: seq<int>) returns (count: int)
  ensures count == MaxPurchases(c, a)
  ensures 0 <= count <= |c|
  ensures count <= |a|
{
  count := 0;
  var i := 0;
  var j := 0;
  while i < |c| && j < |a|
  {
    if a[j] >= c[i] {
      count := count + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}