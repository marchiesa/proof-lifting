// Stock Buy/Sell - Maximum Profit (One Transaction) -- Reference solution with invariants

method BestProfit(prices: seq<int>) returns (profit: int)
  requires |prices| > 0
  ensures profit >= 0
  ensures forall i, j :: 0 <= i < j < |prices| ==> profit >= prices[j] - prices[i]
{
  profit := 0;
  var minPrice := prices[0];
  var i := 1;
  while i < |prices|
    invariant 1 <= i <= |prices|
    invariant profit >= 0
    invariant forall k :: 0 <= k < i ==> minPrice <= prices[k]
    invariant exists k :: 0 <= k < i && minPrice == prices[k]
    invariant forall p, q :: 0 <= p < q < i ==> profit >= prices[q] - prices[p]
    decreases |prices| - i
  {
    if prices[i] - minPrice > profit {
      profit := prices[i] - minPrice;
    }
    // Now profit >= prices[i] - minPrice >= prices[i] - prices[p] for all p < i
    assert forall p, q :: 0 <= p < q < i + 1 ==> profit >= prices[q] - prices[p] by {
      forall p, q | 0 <= p < q < i + 1
        ensures profit >= prices[q] - prices[p]
      {
        if q == i {
          // profit >= prices[i] - minPrice >= prices[i] - prices[p]
          assert minPrice <= prices[p];
        }
        // else both < i, covered by old invariant
      }
    }
    if prices[i] < minPrice {
      minPrice := prices[i];
    }
    i := i + 1;
  }
}
