// Integer Square Root (Binary Search on Answer) -- Reference solution with invariants

method IntSqrt(n: nat) returns (r: nat)
  ensures r * r <= n
  ensures (r + 1) * (r + 1) > n
{
  var lo: nat := 0;
  var hi: nat := n + 1;
  while lo + 1 < hi
    invariant lo * lo <= n
    invariant hi * hi > n
    invariant lo < hi
    decreases hi - lo
  {
    var mid := lo + (hi - lo) / 2;
    if mid * mid <= n {
      lo := mid;
    } else {
      hi := mid;
    }
  }
  r := lo;
}
