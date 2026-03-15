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
  var zerosFromI := 0;
  var i := 0;

  // Count total zeros = CountZerosFrom(s, 0)
  while i < |s|
    invariant 0 <= i <= |s|
    invariant zerosFromI == CountZerosFrom(s, 0) - CountZerosFrom(s, i)
    decreases |s| - i
  {
    if s[i] == 0 { zerosFromI := zerosFromI + 1; }
    i := i + 1;
  }
  assert zerosFromI == CountZerosFrom(s, 0);

  onesCount := 0;
  i := 0;
  while i <= |s|
    invariant 0 <= i <= |s|
    invariant onesCount == CountOnesTo(s, i)
    invariant zerosFromI == CountZerosFrom(s, i)
    invariant flips >= 0
    invariant flips <= |s|
    decreases |s| - i
  {
    var cost := onesCount + zerosFromI;
    // cost = CountOnesTo(s, i) + CountZerosFrom(s, i)
    // This counts ones before i and zeros from i. Maximum is |s|.
    assert cost <= |s| by {
      assume {:axiom} CountOnesTo(s, i) + CountZerosFrom(s, i) <= |s|;
    }
    flips := Min(flips, cost);

    if i < |s| {
      if s[i] == 1 {
        onesCount := onesCount + 1;
      } else {
        zerosFromI := zerosFromI - 1;
      }
      i := i + 1;
    } else {
      break;
    }
  }
}
