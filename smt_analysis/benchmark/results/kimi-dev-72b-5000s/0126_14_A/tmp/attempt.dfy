// The grid has uniform row width (a rectangular sheet)
ghost predicate Rectangular(grid: seq<string>)
{
  |grid| > 0 &&
  forall i | 0 <= i < |grid| :: |grid[i]| == |grid[0]|
}

// The grid contains at least one shaded cell ('*')
ghost predicate HasStar(grid: seq<string>)
{
  exists r | 0 <= r < |grid| ::
    exists c | 0 <= c < |grid[r]| ::
      grid[r][c] == '*'
}

// The result is the sub-rectangle of grid spanning rows [top..bottom) and columns [left..right)
ghost predicate IsSubRectangle(grid: seq<string>, result: seq<string>,
                         top: int, bottom: int, left: int, right: int)
{
  0 <= top < bottom <= |grid| &&
  0 <= left < right &&
  (forall r | top <= r < bottom :: right <= |grid[r]|) &&
  |result| == bottom - top &&
  (forall i | 0 <= i < bottom - top :: result[i] == grid[top + i][left..right])
}

// Every shaded cell in the entire grid lies within the rectangle [top..bottom) x [left..right)
ghost predicate ContainsAllShaded(grid: seq<string>,
                            top: int, bottom: int, left: int, right: int)
{
  forall r | 0 <= r < |grid| ::
    forall c | 0 <= c < |grid[r]| ::
      grid[r][c] == '*' ==> (top <= r < bottom && left <= c < right)
}

// The rectangle is tight: each of its four edges touches at least one shaded cell.
// For axis-aligned rectangles, this is equivalent to having minimum area among all
// rectangles that contain every shaded cell.
ghost predicate TightBounds(grid: seq<string>,
                      top: int, bottom: int, left: int, right: int)
{
  0 <= top < bottom <= |grid| &&
  0 <= left < right &&
  (forall r | top <= r < bottom :: right <= |grid[r]|) &&
  // Top edge touches a shaded cell
  (exists c | left <= c < right :: grid[top][c] == '*') &&
  // Bottom edge touches a shaded cell
  (exists c | left <= c < right :: grid[bottom - 1][c] == '*') &&
  // Left edge touches a shaded cell
  (exists r | top <= r < bottom :: grid[r][left] == '*') &&
  // Right edge touches a shaded cell
  (exists r | top <= r < bottom :: grid[r][right - 1] == '*')
}

// The result is the minimum-cost rectangle cut from the grid containing all shaded cells
ghost predicate IsMinimalBoundingBox(grid: seq<string>, result: seq<string>,
                               top: int, bottom: int, left: int, right: int)
{
  IsSubRectangle(grid, result, top, bottom, left, right) &&
  ContainsAllShaded(grid, top, bottom, left, right) &&
  TightBounds(grid, top, bottom, left, right)
}

method Letter(grid: seq<string>) returns (result: seq<string>)
  decreases *
  requires Rectangular(grid)
  requires HasStar(grid)
  ensures exists top | 0 <= top < |grid| ::
            exists bottom | 0 <= bottom <= |grid| ::
              exists left | 0 <= left < |grid[0]| ::
                exists right | 0 <= right <= |grid[0]| ::
                  IsMinimalBoundingBox(grid, result, top, bottom, left, right)
{
  var n := |grid|;
  var m := |grid[0]|;

  // === FIND TOP: first row containing a '*' ===
  var top := 0;
  var topDone := false;
  while top < n && !topDone
    invariant 0 <= top <= n
    invariant !topDone ==> forall r | 0 <= r < top :: forall c | 0 <= c < |grid[r]| :: grid[r][c] != '*'
    invariant topDone ==> top < n
    invariant topDone ==> exists c | 0 <= c < |grid[top]| :: grid[top][c] == '*'
    invariant topDone ==> forall r | 0 <= r < top :: forall c | 0 <= c < |grid[r]| :: grid[r][c] != '*'
    decreases n - top, !topDone
  {

    var j := 0;
    var jDone := false;
    while j < m && !jDone
      invariant 0 <= j <= m
      invariant !jDone ==> forall c | 0 <= c < j :: grid[top][c] != '*'
      invariant jDone ==> 0 <= j < m && grid[top][j] == '*'
      decreases m - j, !jDone
    {
      if grid[top][j] == '*' {
        jDone := true;
      } else {
        j := j + 1;
      }
    }
    if jDone {
      topDone := true;
    } else {
      assert forall c | 0 <= c < |grid[top]| :: grid[top][c] != '*';
      top := top + 1;
    }
  }
  if !topDone {
    assert forall r | 0 <= r < |grid| :: forall c | 0 <= c < |grid[r]| :: grid[r][c] != '*';
    assert !HasStar(grid);
    assert false;
    result := []; return;
  }

  // === FIND BOTTOM: last row containing a '*' ===
  var bot := n - 1;
  var botDone := false;
  while bot >= 0 && !botDone
    invariant -1 <= bot <= n - 1
    invariant !botDone ==> forall r | bot < r < n :: forall c | 0 <= c < |grid[r]| :: grid[r][c] != '*'
    invariant botDone ==> 0 <= bot < n
    invariant botDone ==> exists c | 0 <= c < |grid[bot]| :: grid[bot][c] == '*'
    invariant botDone ==> forall r | bot < r < n :: forall c | 0 <= c < |grid[r]| :: grid[r][c] != '*'
    decreases bot + 1, !botDone
  {
    assert |grid[bot]| == m;
    var