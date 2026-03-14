// Stock Buy/Sell Maximum Profit -- Runtime spec tests

function MaxProfit(prices: seq<int>): int
  requires |prices| > 0
{
  MaxProfitHelper(prices, 0, prices[0])
}

function MaxProfitHelper(prices: seq<int>, i: int, minSoFar: int): int
  requires 0 <= i <= |prices|
  requires |prices| > 0
  decreases |prices| - i
{
  if i == |prices| then 0
  else
    var newMin := if prices[i] < minSoFar then prices[i] else minSoFar;
    var profitHere := prices[i] - minSoFar;
    var rest := MaxProfitHelper(prices, i + 1, newMin);
    if profitHere > rest then profitHere else rest
}

method Main() {
  // MaxProfit spec function tests
  expect MaxProfit([7, 1, 5, 3, 6, 4]) == 5, "classic: buy at 1, sell at 6";
  expect MaxProfit([7, 6, 4, 3, 1]) == 0, "decreasing: no profit";
  expect MaxProfit([5]) == 0, "single price: no profit";
  expect MaxProfit([3, 3, 3]) == 0, "all same: no profit";
  expect MaxProfit([1, 2]) == 1, "simple gain of 1";
  expect MaxProfit([2, 1]) == 0, "simple loss: no profit";
  expect MaxProfit([1, 5, 2, 8]) == 7, "buy at 1, sell at 8";

  // Wrong answer check
  expect MaxProfit([7, 1, 5, 3, 6, 4]) != 4, "profit is not 4";
  expect MaxProfit([7, 1, 5, 3, 6, 4]) != 6, "profit is not 6";

  print "All spec tests passed\n";
}
