// Stock Span Problem
// Task: Add loop invariants so that Dafny can verify this program.

function SpanAt(prices: seq<int>, i: int): int
  requires 0 <= i < |prices|
  decreases i
{
  if i == 0 then 1
  else if prices[i - 1] <= prices[i] then SpanAt(prices, i - 1) + 1
  else 1
}

// Simpler iterative spec: span is 1 + count of consecutive days before i with price <= prices[i]
function SpanCount(prices: seq<int>, i: int, j: int): int
  requires 0 <= j <= i < |prices|
  decreases i - j
{
  if j == i then 1
  else if prices[j] <= prices[i] then 1 + SpanCount(prices, i, j + 1)
  else SpanCount(prices, i, j + 1)
}

method StockSpan(prices: seq<int>) returns (spans: seq<int>)
  requires |prices| > 0
  ensures |spans| == |prices|
  ensures forall i :: 0 <= i < |spans| ==> spans[i] >= 1
{
  spans := [];
  var i := 0;
  while i < |prices|
  {
    var span := 1;
    var j := i - 1;
    while j >= 0 && prices[j] <= prices[i]
    {
      span := span + 1;
      j := j - 1;
    }
    spans := spans + [span];
    i := i + 1;
  }
}
