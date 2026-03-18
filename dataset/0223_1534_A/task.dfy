// ── Problem-modeling predicates ──

ghost predicate IsGrid(grid: seq<seq<char>>, n: int, m: int)
{
  n >= 0 && m >= 0 && |grid| == n &&
  forall i | 0 <= i < n :: |grid[i]| == m
}

ghost predicate ValidInput(grid: seq<seq<char>>, n: int, m: int)
{
  IsGrid(grid, n, m) &&
  forall i, j | 0 <= i < n && 0 <= j < m ::
    grid[i][j] == 'R' || grid[i][j] == 'W' || grid[i][j] == '.'
}

ghost predicate FullyColored(grid: seq<seq<char>>, n: int, m: int)
{
  IsGrid(grid, n, m) &&
  forall i, j | 0 <= i < n && 0 <= j < m ::
    grid[i][j] == 'R' || grid[i][j] == 'W'
}

// Every edge-adjacent pair of cells has different colors.
ghost predicate NeighborsAlternate(grid: seq<seq<char>>, n: int, m: int)
{
  IsGrid(grid, n, m) &&
  (forall i, j | 0 <= i < n && 0 <= j < m - 1 :: grid[i][j] != grid[i][j + 1]) &&
  (forall i, j | 0 <= i < n - 1 && 0 <= j < m :: grid[i][j] != grid[i + 1][j])
}

// The coloring preserves every already-coloured cell from the input.
ghost predicate ExtendsInput(coloring: seq<seq<char>>, input: seq<seq<char>>, n: int, m: int)
{
  IsGrid(coloring, n, m) && IsGrid(input, n, m) &&
  forall i, j | 0 <= i < n && 0 <= j < m ::
    input[i][j] != '.' ==> coloring[i][j] == input[i][j]
}

// A grid is a solution iff it is fully coloured R/W, every neighbour
// pair alternates, and it extends (does not recolour) the input.
ghost predicate IsSolution(coloring: seq<seq<char>>, input: seq<seq<char>>, n: int, m: int)
{
  FullyColored(coloring, n, m) &&
  NeighborsAlternate(coloring, n, m) &&
  ExtendsInput(coloring, input, n, m)
}

// ── Candidate enumeration ──
// A rectangular grid graph is bipartite with exactly two proper 2-colourings,
// parameterised by parity w ∈ {0,1}.  BuildGrid constructs them so the
// ensures clause can enumerate all candidates with a bounded existential.

ghost function CellColor(i: int, j: int, w: int): char
  requires w == 0 || w == 1
{
  if (i + j) % 2 == w then 'R' else 'W'
}

ghost function BuildRow(row: int, len: int, w: int): seq<char>
  requires len >= 0
  requires w == 0 || w == 1
  decreases len
{
  if len == 0 then []
  else BuildRow(row, len - 1, w) + [CellColor(row, len - 1, w)]
}

ghost function BuildGrid(n: int, m: int, w: int): seq<seq<char>>
  requires n >= 0 && m >= 0
  requires w == 0 || w == 1
  decreases n
{
  if n == 0 then []
  else BuildGrid(n - 1, m, w) + [BuildRow(n - 1, m, w)]
}

method ColourTheFlag(grid: seq<seq<char>>, n: int, m: int) returns (possible: bool, result: seq<seq<char>>)
  requires ValidInput(grid, n, m)
  ensures possible ==> IsSolution(result, grid, n, m)
  ensures !possible ==> result == []
  ensures possible == (exists w | 0 <= w <= 1 :: IsSolution(BuildGrid(n, m, w), grid, n, m))
{
  var w := 0;
  var i := 0;
  while i < n {
    var j := 0;
    while j < m {
      if grid[i][j] == 'R' {
        w := (i + j) % 2;
      } else if grid[i][j] == 'W' {
        w := 1 - (i + j) % 2;
      }
      j := j + 1;
    }
    i := i + 1;
  }

  var bad := false;
  result := [];
  i := 0;
  while i < n {
    var row: seq<char> := [];
    var j := 0;
    while j < m {
      var c: char;
      if (i + j) % 2 == w {
        c := 'R';
      } else {
        c := 'W';
      }
      if grid[i][j] != '.' && c != grid[i][j] {
        bad := true;
      }
      row := row + [c];
      j := j + 1;
    }
    result := result + [row];
    i := i + 1;
  }

  if bad {
    possible := false;
    result := [];
  } else {
    possible := true;
  }
}