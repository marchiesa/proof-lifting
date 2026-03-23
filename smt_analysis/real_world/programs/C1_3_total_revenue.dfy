// Pattern: Compute total revenue = sum of (price * quantity) pairs
// Source: e-commerce, billing, inventory systems
// Real-world: shopping cart total, invoice computation, payroll

ghost function Revenue(prices: seq<int>, quantities: seq<int>): int
  requires |prices| == |quantities|
{
  if |prices| == 0 then 0
  else Revenue(prices[..|prices|-1], quantities[..|quantities|-1])
       + prices[|prices|-1] * quantities[|quantities|-1]
}

method TotalRevenue(prices: seq<int>, quantities: seq<int>) returns (total: int)
  requires |prices| == |quantities|
  requires forall i :: 0 <= i < |prices| ==> prices[i] >= 0
  requires forall i :: 0 <= i < |quantities| ==> quantities[i] >= 0
  ensures total == Revenue(prices, quantities)
{
  total := 0;
  var i := 0;
  while i < |prices|
    invariant 0 <= i <= |prices|
    invariant total == Revenue(prices[..i], quantities[..i])
  {
    assert prices[..i+1] == prices[..i] + [prices[i]];    // SMT QUIRK: B1 extensionality
    assert quantities[..i+1] == quantities[..i] + [quantities[i]];  // SMT QUIRK: B1 extensionality
    total := total + prices[i] * quantities[i];
    i := i + 1;
  }
  assert prices[..|prices|] == prices;        // SMT QUIRK: B1 take-full
  assert quantities[..|quantities|] == quantities;  // SMT QUIRK: B1 take-full
}
