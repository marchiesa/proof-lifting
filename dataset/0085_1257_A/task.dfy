// --- Specification ---

ghost function Abs(x: int): int
{
  if x >= 0 then x else -x
}

// Whether the relative order of two students flips from (a,b) to (pa,pb)
ghost predicate OrderFlipped(a: int, b: int, pa: int, pb: int)
{
  (a < b && pa > pb) || (a > b && pa < pb)
}

// Minimum adjacent swaps needed to move two specific students from positions
// (a, b) to positions (pa, pb) in a row. Each student requires |orig - target|
// swaps with intermediate neighbors. If their relative order must flip, one of
// those swaps is shared (they swap with each other), saving 1.
ghost function SwapCost(a: int, b: int, pa: int, pb: int): int
{
  Abs(a - pa) + Abs(b - pb) - (if OrderFlipped(a, b, pa, pb) then 1 else 0)
}

// There exist valid target positions that achieve exactly distance d
// using at most x adjacent swaps
ghost predicate IsAchievable(n: int, x: int, a: int, b: int, d: int)
  requires n >= 2 && 1 <= a <= n && 1 <= b <= n && a != b && x >= 0
{
  exists pa: int, pb: int | 1 <= pa <= n && 1 <= pb <= n ::
    pa != pb && Abs(pa - pb) == d && SwapCost(a, b, pa, pb) <= x
}

// d is the maximum distance achievable: it is achievable, and no reachable
// configuration yields a greater distance
ghost predicate IsMaxDistance(n: int, x: int, a: int, b: int, d: int)
  requires n >= 2 && 1 <= a <= n && 1 <= b <= n && a != b && x >= 0
{
  IsAchievable(n, x, a, b, d) &&
  forall pa: int, pb: int | 1 <= pa <= n && 1 <= pb <= n ::
    (pa != pb && SwapCost(a, b, pa, pb) <= x) ==> Abs(pa - pb) <= d
}

// --- Implementation ---

method TwoRivalStudents(n: int, x: int, a: int, b: int) returns (distance: int)
  requires n >= 2 && 1 <= a <= n && 1 <= b <= n && a != b && x >= 0
  ensures IsMaxDistance(n, x, a, b, distance)
{
  var la := a;
  var lb := b;
  var rx := x;
  if la > lb {
    var tmp := la;
    la := lb;
    lb := tmp;
  }
  var da := if la - 1 < rx then la - 1 else rx;
  la := la - da;
  rx := rx - da;
  var db := if n - lb < rx then n - lb else rx;
  lb := lb + db;
  distance := lb - la;
}