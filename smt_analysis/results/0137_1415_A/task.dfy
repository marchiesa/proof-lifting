ghost predicate InGrid(n: int, m: int, i: int, j: int)
{
  1 <= i <= n && 1 <= j <= m
}

// Set of cells from which (ti, tj) is reachable in at most t steps,
// where each step moves to an orthogonally adjacent cell or stays.
// Computed by BFS-like expansion from the target.
ghost function ReachableWithin(n: int, m: int, ti: int, tj: int, t: int): set<(int, int)>
  requires n >= 1 && m >= 1
  requires InGrid(n, m, ti, tj)
  requires t >= 0
  decreases t
{
  if t == 0 then
    {(ti, tj)}
  else
    var prev := ReachableWithin(n, m, ti, tj, t - 1);
    set i: int, j: int | 1 <= i <= n && 1 <= j <= m &&
      // (i,j) already reachable, OR prisoner at (i,j) moves to a neighbor in prev
      ((i, j) in prev ||
       (i - 1 >= 1 && (i - 1, j) in prev) ||
       (i + 1 <= n && (i + 1, j) in prev) ||
       (j - 1 >= 1 && (i, j - 1) in prev) ||
       (j + 1 <= m && (i, j + 1) in prev))
    :: (i, j)
}

// Every cell in the grid can reach (ti, tj) within t steps.
ghost predicate AllReachWithin(n: int, m: int, ti: int, tj: int, t: int)
  requires n >= 1 && m >= 1
  requires InGrid(n, m, ti, tj)
  requires t >= 0
{
  var reach := ReachableWithin(n, m, ti, tj, t);
  forall i, j :: 1 <= i <= n && 1 <= j <= m ==> (i, j) in reach
}

method PrisonBreak(n: int, m: int, r: int, c: int) returns (time: int)
  requires n >= 1 && m >= 1
  requires InGrid(n, m, r, c)
  ensures time >= 0
  ensures AllReachWithin(n, m, r, c, time)
  ensures time == 0 || !AllReachWithin(n, m, r, c, time - 1)
{
  var dr: int;
  if r - 1 > n - r { dr := r - 1; } else { dr := n - r; }
  var dc: int;
  if c - 1 > m - c { dc := c - 1; } else { dc := m - c; }
  time := dr + dc;
}