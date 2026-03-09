// Sum with count - linear arithmetic invariants
method SumWithCount(n: nat) returns (sum: int, count: int)
  ensures count == n
  ensures sum == n * (n - 1) / 2
{
  sum := 0;
  count := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant count == i
    invariant 2 * sum == i * (i - 1)
  {
    sum := sum + i;
    count := count + 1;
    i := i + 1;
  }
}
