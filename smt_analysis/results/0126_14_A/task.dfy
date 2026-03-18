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
  var lines := grid;

  while true
    decreases *
  {
    if |lines| == 0 { break; }

    // Check if any line starts with '*'
    var a := false;
    var i := 0;
    while i < |lines|
      decreases |lines| - i
    {
      if |lines[i]| > 0 && lines[i][0] == '*' {
        a := true;
        break;
      }
      i := i + 1;
    }
    if !a {
      var newLines: seq<string> := [];
      i := 0;
      while i < |lines|
        decreases |lines| - i
      {
        if |lines[i]| > 0 {
          newLines := newLines + [lines[i][1..]];
        }
        i := i + 1;
      }
      lines := newLines;
      continue;
    }

    // Check if any line ends with '*'
    var b := false;
    i := 0;
    while i < |lines|
      decreases |lines| - i
    {
      if |lines[i]| > 0 && lines[i][|lines[i]| - 1] == '*' {
        b := true;
        break;
      }
      i := i + 1;
    }
    if !b {
      var newLines: seq<string> := [];
      i := 0;
      while i < |lines|
        decreases |lines| - i
      {
        if |lines[i]| > 0 {
          newLines := newLines + [lines[i][..|lines[i]| - 1]];
        }
        i := i + 1;
      }
      lines := newLines;
      continue;
    }

    // Check if first row is all dots
    var allDots := true;
    var j := 0;
    while j < |lines[0]|
      decreases |lines[0]| - j
    {
      if lines[0][j] != '.' {
        allDots := false;
        break;
      }
      j := j + 1;
    }
    if allDots {
      lines := lines[1..];
      continue;
    }

    // Check if last row is all dots
    allDots := true;
    j := 0;
    while j < |lines[|lines| - 1]|
      decreases |lines[|lines| - 1]| - j
    {
      if lines[|lines| - 1][j] != '.' {
        allDots := false;
        break;
      }
      j := j + 1;
    }
    if allDots {
      lines := lines[..|lines| - 1];
      continue;
    }

    break;
  }

  result := lines;
}