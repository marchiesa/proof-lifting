// Minimum Flips to Make Binary String Monotone
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsBinary(s: seq<int>)
{
  forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1
}

function Min(a: int, b: int): int { if a <= b then a else b }

// Count zeros from position i to end
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
  // For each partition point k, count: ones before k + zeros from k
  // flips = min over all k of (ones in s[..k] + zeros in s[k..])
  flips := |s|; // worst case: flip everything
  var onesCount := 0;
  var i := 0;
  while i <= |s|
  {
    var zerosFromI := 0;
    var j := i;
    while j < |s|
    {
      if s[j] == 0 {
        zerosFromI := zerosFromI + 1;
      }
      j := j + 1;
    }
    var cost := onesCount + zerosFromI;
    flips := Min(flips, cost);
    if i < |s| && s[i] == 1 {
      onesCount := onesCount + 1;
    }
    i := i + 1;
  }
}
