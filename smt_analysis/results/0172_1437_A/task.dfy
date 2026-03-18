// Models the greedy customer behavior described in the problem:
// buy floor(x/a) packs, then if remainder >= a/2, buy one more full pack
ghost function CansActuallyBought(x: int, a: int): int
  requires a >= 1
{
  var packs := x / a;
  var remainder := x % a;
  if 2 * remainder >= a then
    (packs + 1) * a   // remainder >= a/2, so buys an extra full pack
  else
    packs * a + remainder  // buys remaining cans individually
}

// A customer wanting x cans ends up buying strictly more than x
ghost predicate CustomerBuysMore(x: int, a: int)
  requires a >= 1
{
  CansActuallyBought(x, a) > x
}

// Pack size a is valid: every customer wanting l..r cans buys more than wanted
ghost predicate AllCustomersBuyMore(l: int, r: int, a: int)
  requires l >= 1
  requires l <= r
  requires a >= 1
{
  forall x :: l <= x <= r ==> CustomerBuysMore(x, a)
}

// There exists a pack size making every customer in [l, r] buy more
// Bound: a > 2*r never works (x mod a = x, so 2*x <= 2*r < a, contradiction)
ghost predicate SchemeExists(l: int, r: int)
  requires l >= 1
  requires l <= r
{
  exists a :: a >= 1 && AllCustomersBuyMore(l, r, a)
}

method MarketingScheme(l: int, r: int) returns (result: bool)
  requires l >= 1
  requires l <= r
  ensures result == SchemeExists(l, r)
{
  result := l * 2 > r;
}