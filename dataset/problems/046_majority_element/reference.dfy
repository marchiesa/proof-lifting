// Majority Element (Boyer-Moore Voting Algorithm) -- Reference solution with invariants

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
    invariant 1 <= i <= |a|
    invariant count >= 0
    invariant candidate in a[..i]
    decreases |a| - i
  {
    if a[i] == candidate {
      count := count + 1;
    } else if count == 0 {
      candidate := a[i];
      count := 1;
    } else {
      count := count - 1;
    }
    assert candidate in a[..i+1] by {
      if candidate in a[..i] {
        assert a[..i+1] == a[..i] + [a[i]];
      }
    }
    i := i + 1;
  }
  assert a[..|a|] == a;
}
