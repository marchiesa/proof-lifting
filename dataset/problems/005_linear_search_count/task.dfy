// Count Occurrences
// Task: Add loop invariants so that Dafny can verify this program.

function CountSpec(a: seq<int>, target: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[0] == target then 1 else 0) + CountSpec(a[1..], target)
}

method CountOccurrences(a: seq<int>, target: int) returns (count: int)
  ensures count == CountSpec(a, target)
{
  count := 0;
  var i := 0;
  while i < |a|
  {
    if a[i] == target {
      count := count + 1;
    }
    i := i + 1;
  }
}
