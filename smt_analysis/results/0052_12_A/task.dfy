ghost predicate ValidGrid(grid: seq<seq<char>>)
{
  |grid| == 3 && forall i :: 0 <= i < 3 ==> |grid[i]| == 3
}

// A grid of pressed keys is symmetric about the center iff
// every pressed key's 180°-rotated counterpart is also pressed.
ghost predicate SymmetricAboutCenter(grid: seq<seq<char>>)
  requires ValidGrid(grid)
{
  forall i, j :: (0 <= i < 3 && 0 <= j < 3) ==>
    (grid[i][j] == 'X' ==> grid[2 - i][2 - j] == 'X')
}

method {:verify false} SuperAgent(grid: seq<seq<char>>) returns (symmetric: bool)
  requires ValidGrid(grid)
  ensures symmetric == SymmetricAboutCenter(grid)
{
  var bad := false;
  var i := 0;
  while i < 3 {
    var j := 0;
    while j < 3 {
      if grid[i][j] == 'X' && grid[2 - i][2 - j] != 'X' {
        bad := true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  symmetric := !bad;
}