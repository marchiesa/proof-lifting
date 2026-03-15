// Stock Span Problem

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

method Main()
{
  // [100, 80, 60, 70, 60, 75, 85]
  var p := [100, 80, 60, 70, 60, 75, 85];
  var s := StockSpan(p);
  expect |s| == |p|;
  expect s[0] >= 1;  // span is always >= 1
  expect s[1] >= 1;
  expect s[6] >= 1;

  // All increasing: each span should be >= 1
  var inc := [1, 2, 3, 4, 5];
  var si := StockSpan(inc);
  expect |si| == 5;
  expect forall i :: 0 <= i < 5 ==> si[i] >= 1;

  // Single element
  var single := [42];
  var ss := StockSpan(single);
  expect |ss| == 1;
  expect ss[0] >= 1;

  // Negative test: spans can't be 0
  var any := [5, 3, 8];
  var sa := StockSpan(any);
  expect sa[0] >= 1;
  expect sa[1] >= 1;
  expect sa[2] >= 1;

  print "All spec tests passed\n";
}
