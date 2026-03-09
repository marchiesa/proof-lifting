// Simple counting loop with linear invariants
method CountLoop(n: nat) returns (count: int)
  ensures count == n
{
  count := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant count == i
  {
    count := count + 1;
    i := i + 1;
  }
  assert n >= i;  // Matches Farkas proof goal exactly
  assert i >= n;  // Together prove i == n
  assert count == n;
}
