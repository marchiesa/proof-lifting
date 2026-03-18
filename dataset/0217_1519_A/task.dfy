ghost function Abs(x: int): int {
  if x >= 0 then x else -x
}

ghost function Min(a: int, b: int): int {
  if a <= b then a else b
}

// A single packet is valid if it has >=1 of each color and the counts differ by at most d.
ghost predicate ValidPacket(ri: int, bi: int, d: int) {
  ri >= 1 && bi >= 1 && Abs(ri - bi) <= d
}

// Can we distribute exactly r red and b blue beans into exactly n valid packets?
// We choose how many red (ri) and blue (bi) beans go in the first packet,
// then recursively distribute the rest into n-1 packets.
ghost predicate CanDistributeInN(r: int, b: int, d: int, n: nat)
  decreases n
{
  if n == 0 then
    r == 0 && b == 0
  else if r < n || b < n then
    false  // not enough beans for each remaining packet to get at least 1
  else if n == 1 then
    ValidPacket(r, b, d)
  else
    exists ri | 1 <= ri <= r - (n - 1) ::
      exists bi | 1 <= bi <= b - (n - 1) ::
        ValidPacket(ri, bi, d) &&
        CanDistributeInN(r - ri, b - bi, d, n - 1)
}

// Can we distribute r red and b blue beans into some number of valid packets?
ghost predicate CanDistribute(r: int, b: int, d: int) {
  exists n | 1 <= n <= Min(r, b) :: CanDistributeInN(r, b, d, n)
}

method RedAndBlueBeans(r: int, b: int, d: int) returns (result: bool)
  requires r >= 1 && b >= 1 && d >= 0
  ensures result == CanDistribute(r, b, d)
{
  var rr := r;
  var bb := b;
  if rr > bb {
    var tmp := rr;
    rr := bb;
    bb := tmp;
  }
  result := rr * (d + 1) >= bb;
}