ghost function BitAnd(a: int, b: int): int
  requires a >= 0 && b >= 0
  decreases a + b
{
  if a == 0 || b == 0 then 0
  else 2 * BitAnd(a / 2, b / 2) + (if a % 2 == 1 && b % 2 == 1 then 1 else 0)
}

ghost function AndRange(lo: int, hi: int): int
  requires 0 <= lo <= hi
  decreases hi - lo
{
  if lo == hi then hi
  else BitAnd(AndRange(lo, hi - 1), hi)
}

method AndThenThereWereK(n: int) returns (k: int)
  requires n >= 1
  ensures 0 <= k <= n
  ensures AndRange(k, n) == 0
  ensures forall k' :: k < k' <= n ==> AndRange(k', n) != 0
{
  var p := 1;
  while p * 2 <= n
    decreases n - p
  {
    p := p * 2;
  }
  k := p - 1;
}