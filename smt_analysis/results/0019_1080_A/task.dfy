// A valid notebook purchase provides enough sheets of each color for n invitations.
// Each invitation requires 2 red, 5 green, and 8 blue sheets.
// Each notebook contains k sheets of a single color.
ghost predicate SufficientNotebooks(r: int, g: int, b: int, n: int, k: int)
{
  r >= 0 && g >= 0 && b >= 0 &&
  r * k >= 2 * n &&
  g * k >= 5 * n &&
  b * k >= 8 * n
}

// m is the minimum non-negative integer such that m * k >= need:
// the fewest k-sheet notebooks to obtain at least `need` sheets.
ghost predicate IsMinCover(m: int, need: int, k: int)
  requires k >= 1
{
  m >= 0 &&
  m * k >= need &&
  (m == 0 || (m - 1) * k < need)
}

// The minimum total notebooks for n invitations with k-sheet notebooks.
// Since colors are independent (notebooks are single-color), the global
// minimum equals the sum of per-color minima.
ghost predicate IsMinTotalNotebooks(total: int, n: int, k: int)
  requires n >= 1 && k >= 1
{
  exists r: nat ::
    exists g: nat ::
      exists b: nat ::
        IsMinCover(r, 2 * n, k) &&
        IsMinCover(g, 5 * n, k) &&
        IsMinCover(b, 8 * n, k) &&
        SufficientNotebooks(r, g, b, n, k) &&
        total == r + g + b
}

method PetyaAndOrigami(n: int, k: int) returns (notebooks: int)
  requires n >= 1 && k >= 1
  ensures IsMinTotalNotebooks(notebooks, n, k)
{
  notebooks := ((n * 2 + k - 1) / k) + ((n * 5 + k - 1) / k) + ((n * 8 + k - 1) / k);
}