// Stock Buy/Sell Maximum Profit -- Test cases

method {:axiom} BestProfit(prices: seq<int>) returns (profit: int)
  requires |prices| > 0
  ensures profit >= 0
  ensures forall i, j :: 0 <= i < j < |prices| ==> profit >= prices[j] - prices[i]

method TestClassic()
{
  var p := BestProfit([7, 1, 5, 3, 6, 4]);
  assert p >= 0;
  // Best: buy at 1, sell at 6, profit = 5
  var prices := [7, 1, 5, 3, 6, 4];
  assert prices[1] == 1;
  assert prices[4] == 6;
  assert 0 <= 1 < 4 < |prices|;
  assert p >= prices[4] - prices[1];
}

method TestDecreasing()
{
  var p := BestProfit([7, 6, 4, 3, 1]);
  assert p >= 0;
}

method TestSingle()
{
  var p := BestProfit([5]);
  assert p >= 0;
}

method TestAllSame()
{
  var p := BestProfit([3, 3, 3]);
  assert p >= 0;
}
