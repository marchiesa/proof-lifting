// Majority Element (Boyer-Moore Voting Algorithm)
// Task: Add loop invariants so that Dafny can verify this program.

function Count(a: seq<int>, val: int): nat
{
  if |a| == 0 then 0
  else (if a[0] == val then 1 else 0) + Count(a[1..], val)
}

predicate IsMajority(a: seq<int>, val: int)
{
  2 * Count(a, val) > |a|
}

method FindMajority(a: seq<int>) returns (candidate: int)
  requires |a| > 0
  requires exists v :: IsMajority(a, v)
  ensures candidate in a
{
  candidate := a[0];
  var count := 1;
  var i := 1;

  while i < |a|
  {
    if a[i] == candidate {
      count := count + 1;
    } else if count == 0 {
      candidate := a[i];
      count := 1;
    } else {
      count := count - 1;
    }
    i := i + 1;
  }
}
