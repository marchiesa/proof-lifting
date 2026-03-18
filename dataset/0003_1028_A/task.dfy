ghost predicate ValidGrid(n: int, m: int, grid: seq<string>)
{
  n > 0 && m > 0 && |grid| == n &&
  (forall i | 0 <= i < n :: |grid[i]| == m) &&
  (forall i | 0 <= i < n :: forall j | 0 <= j < m ::
    grid[i][j] == 'W' || grid[i][j] == 'B')
}

// A cell (i,j) lies inside the axis-aligned square with given center and half-side-length
ghost predicate CellInSquare(i: int, j: int, centerRow: int, centerCol: int, half: int)
{
  centerRow - half <= i <= centerRow + half &&
  centerCol - half <= j <= centerCol + half
}

// The grid consists of exactly one black square of side length 2*half+1 (odd)
// centered at (centerRow, centerCol) in 0-indexed coordinates, with all other cells white
ghost predicate IsBlackSquareCenteredAt(n: int, m: int, grid: seq<string>,
                                   centerRow: int, centerCol: int, half: int)
  requires |grid| == n && n > 0 && m > 0
  requires forall i | 0 <= i < n :: |grid[i]| == m
{
  half >= 0 &&
  centerRow - half >= 0 && centerRow + half < n &&
  centerCol - half >= 0 && centerCol + half < m &&
  (forall i | 0 <= i < n ::
    forall j | 0 <= j < m ::
      if CellInSquare(i, j, centerRow, centerCol, half)
      then grid[i][j] == 'B'
      else grid[i][j] == 'W')
}

// There exists some black square painted on the grid
ghost predicate HasBlackSquare(n: int, m: int, grid: seq<string>)
  requires |grid| == n && n > 0 && m > 0
  requires forall i | 0 <= i < n :: |grid[i]| == m
{
  exists cr | 0 <= cr < n ::
    exists cc | 0 <= cc < m ::
      exists h: nat ::
        IsBlackSquareCenteredAt(n, m, grid, cr, cc, h)
}

method FindSquare(n: int, m: int, grid: seq<string>) returns (r: int, c: int)
  requires ValidGrid(n, m, grid)
  requires HasBlackSquare(n, m, grid)
  ensures 1 <= r <= n && 1 <= c <= m
  ensures exists h: nat ::
            IsBlackSquareCenteredAt(n, m, grid, r - 1, c - 1, h)
{
  var ly := 0;
  while ly < |grid| && 'B' !in grid[ly] {
    ly := ly + 1;
  }

  var ry := ly + 1;
  while ry < |grid| && 'B' in grid[ry] {
    ry := ry + 1;
  }

  var lx := 0;
  while lx < |grid[ly]| && grid[ly][lx] != 'B' {
    lx := lx + 1;
  }

  var rx := lx + 1;
  while rx < |grid[ly]| && grid[ly][rx] == 'B' {
    rx := rx + 1;
  }

  var y := (ly + ry) / 2;
  var x := (lx + rx) / 2;
  r := y + 1;
  c := x + 1;
}