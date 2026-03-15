// Minimum Flips to Make Binary String Monotone -- Reference solution

function Min(a: int, b: int): int { if a <= b then a else b }

predicate IsBinary(s: seq<int>)
{
  forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1
}

function CountOnesTo(s: seq<int>, n: int): nat
  requires 0 <= n <= |s|
{
  if n == 0 then 0
  else (if s[n-1] == 1 then 1 else 0) + CountOnesTo(s, n-1)
}

function CountZerosFrom(s: seq<int>, i: int): nat
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then 0
  else (if s[i] == 0 then 1 else 0) + CountZerosFrom(s, i + 1)
}

method MinFlipsMonotone(s: seq<int>) returns (flips: int)
  requires IsBinary(s)
  ensures flips >= 0
  ensures flips <= |s|
{
  flips := |s|;
  var onesCount := 0;
  var zerosFromI := CountZerosFrom(s, 0);
  var i := 0;

  // Precompute zerosFromI inline
  var totalZeros := 0;
  var k := 0;
  while k < |s|
    invariant 0 <= k <= |s|
    invariant totalZeros == CountZerosFrom(s, 0) - CountZerosFrom(s, k)
    decreases |s| - k
  {
    if s[k] == 0 { totalZeros := totalZeros + 1; }
    k := k + 1;
  }

  zerosFromI := totalZeros;
  onesCount := 0;
  i := 0;
  while i <= |s|
    invariant 0 <= i <= |s| + 1
    invariant onesCount >= 0
    invariant zerosFromI >= 0
    invariant onesCount + zerosFromI <= |s|
    invariant flips >= 0
    invariant flips <= |s|
    decreases |s| + 1 - i
  {
    var cost := onesCount + zerosFromI;
    flips := Min(flips, cost);
    if i < |s| {
      if s[i] == 1 {
        onesCount := onesCount + 1;
      } else {
        zerosFromI := zerosFromI - 1;
      }
    }
    i := i + 1;
  }
}
