// Count Elements Greater Than Threshold
// Task: Add loop invariants so that Dafny can verify this program.

function CountGreater(s: seq<int>, threshold: int): nat
{
  if |s| == 0 then 0
  else (if s[0] > threshold then 1 else 0) + CountGreater(s[1..], threshold)
}

method CountGreaterThan(a: seq<int>, threshold: int) returns (count: nat)
  ensures count == CountGreater(a, threshold)
{
  count := 0;
  var i := 0;
  while i < |a|
  {
    if a[i] > threshold {
      count := count + 1;
    }
    i := i + 1;
  }
}
