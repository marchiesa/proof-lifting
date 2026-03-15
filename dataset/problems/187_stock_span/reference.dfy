// Stock Span Problem -- Reference solution with invariants

method StockSpan(prices: seq<int>) returns (spans: seq<int>)
  requires |prices| > 0
  ensures |spans| == |prices|
  ensures forall i :: 0 <= i < |spans| ==> spans[i] >= 1
{
  spans := [];
  var i := 0;
  while i < |prices|
    invariant 0 <= i <= |prices|
    invariant |spans| == i
    invariant forall k :: 0 <= k < i ==> spans[k] >= 1
    decreases |prices| - i
  {
    var span := 1;
    var j := i - 1;
    while j >= 0 && prices[j] <= prices[i]
      invariant -1 <= j <= i - 1
      invariant span == i - j
      decreases j + 1
    {
      span := span + 1;
      j := j - 1;
    }
    spans := spans + [span];
    i := i + 1;
  }
}
