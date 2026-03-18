// Specification: Grid reachability with exact cost.
//
// On an n × m grid, from cell (x, y) you can:
//   - move right to (x, y+1), paying x burles
//   - move down to (x+1, y), paying y burles
//
// CanReach(x, y, n, m, cost) is true iff there exists a sequence of such moves
// leading from (x, y) to (n, m) with total cost exactly equal to `cost`.
ghost predicate CanReach(x: int, y: int, n: int, m: int, cost: int)
  requires 1 <= x <= n && 1 <= y <= m
  decreases (n - x) + (m - y)
{
  // Already at the destination with zero remaining cost
  (x == n && y == m && cost == 0)
  ||
  // Move right from (x, y) to (x, y+1), paying x burles
  (y < m && CanReach(x, y + 1, n, m, cost - x))
  ||
  // Move down from (x, y) to (x+1, y), paying y burles
  (x < n && CanReach(x + 1, y, n, m, cost - y))
}

method {:verify false} TheCakeIsALie(n: int, m: int, k: int) returns (result: bool)
  requires n >= 1 && m >= 1
  ensures result == CanReach(1, 1, n, m, k)
{
  var remaining := k - (1 * (m - 1) + m * (n - 1));
  result := remaining == 0;
}