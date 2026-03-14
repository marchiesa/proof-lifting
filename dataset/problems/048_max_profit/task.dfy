// Stock Buy/Sell - Maximum Profit (One Transaction)
// Task: Add loop invariants so that Dafny can verify this program.

function MaxProfit(prices: seq<int>): int
  requires |prices| > 0
{
  MaxProfitHelper(prices, 0, prices[0])
}

function MaxProfitHelper(prices: seq<int>, i: int, minSoFar: int): int
  requires 0 <= i <= |prices|
  requires |prices| > 0
{
  if i == |prices| then 0
  else
    var newMin := if prices[i] < minSoFar then prices[i] else minSoFar;
    var profitHere := prices[i] - minSoFar;
    var rest := MaxProfitHelper(prices, i + 1, newMin);
    if profitHere > rest then profitHere else rest
}

method BestProfit(prices: seq<int>) returns (profit: int)
  requires |prices| > 0
  ensures profit >= 0
  ensures forall i, j :: 0 <= i < j < |prices| ==> profit >= prices[j] - prices[i]
{
  profit := 0;
  var minPrice := prices[0];
  var i := 1;
  while i < |prices|
  {
    if prices[i] - minPrice > profit {
      profit := prices[i] - minPrice;
    }
    if prices[i] < minPrice {
      minPrice := prices[i];
    }
    i := i + 1;
  }
}
