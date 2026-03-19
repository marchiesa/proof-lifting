ghost predicate Rectangular(grid: seq<string>)
{
  |grid| > 0 &&
  forall i | 0 <= i < |grid| :: |grid[i]| == |grid[0]|
}

ghost predicate HasStar(grid: seq<string>)
{
  exists r | 0 <= r < |grid| ::
    exists c | 0 <= c < |grid[r]| ::
      grid[r][c] == '*'
}

ghost predicate IsSubRectangle(grid: seq<string>, result: seq<string>,
                         top: int, bottom: int, left: int, right: int)
{
  0 <= top < bottom <= |grid| &&
  0 <= left < right &&
  (forall r | top <= r < bottom :: right <= |grid[r]|) &&
  |result| == bottom - top &&
  (forall i | 0 <= i < bottom - top :: result[i] == grid[top + i][left..right])
}

ghost predicate ContainsAllShaded(grid: seq<string>,
                            top: int, bottom: int, left: int, right: int)
{
  forall r | 0 <= r < |grid| ::
    forall c | 0 <= c < |grid[r]| ::
      grid[r][c] == '*' ==> (top <= r < bottom && left <= c < right)
}

ghost predicate TightBounds(grid: seq<string>,
                      top: int, bottom: int, left: int, right: int)
{
  0 <= top < bottom <= |grid| &&
  0 <= left < right &&
  (forall r | top <= r < bottom :: right <= |grid[r]|) &&
  (exists c | left <= c < right :: grid[top][c] == '*') &&
  (exists c | left <= c < right :: grid[bottom - 1][c] == '*') &&
  (exists r | top <= r < bottom :: grid[r][left] == '*') &&
  (exists r | top <= r < bottom :: grid[r][right - 1] == '*')
}

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
    var j := 0;
    var jDone := false;
    while j < m && !jDone
      invariant 0 <= j <= m
      invariant !jDone ==> forall c | 0 <= c < j :: grid[bot][c] != '*'
      invariant jDone ==> 0 <= j < m && grid[bot][j] == '*'
      decreases m - j, !jDone
    {
      if grid[bot][j] == '*' {
        jDone := true;
      } else {
        j := j + 1;
      }
    }
    if jDone {
      botDone := true;
    } else {
      bot := bot - 1;
    }
  }
  if !botDone {
    assert forall r | 0 <= r < n :: forall c | 0 <= c < |grid[r]| :: grid[r][c] != '*';
    assert false;
    result := []; return;
  }
  var bottom := bot + 1;

  // top <= bot because row top has a star but rows > bot don't
  if top > bot {
    assert forall c | 0 <= c < |grid[top]| :: grid[top][c] != '*';
  }

  // === FIND LEFT: first column containing a '*' ===
  var left := 0;
  var leftDone := false;
  while left < m && !leftDone
    invariant 0 <= left <= m
    invariant !leftDone ==> forall r | 0 <= r < n :: forall c | 0 <= c < left :: grid[r][c] != '*'
    invariant leftDone ==> 0 <= left < m
    invariant leftDone ==> exists r | 0 <= r < n :: grid[r][left] == '*'
    invariant leftDone ==> forall r | 0 <= r < n :: forall c | 0 <= c < left :: grid[r][c] != '*'
    decreases m - left, !leftDone
  {
    var r := 0;
    var rDone := false;
    while r < n && !rDone
      invariant 0 <= r <= n
      invariant !rDone ==> forall rr | 0 <= rr < r :: grid[rr][left] != '*'
      invariant rDone ==> 0 <= r < n && grid[r][left] == '*'
      decreases n - r, !rDone
    {
      if grid[r][left] == '*' {
        rDone := true;
      } else {
        r := r + 1;
      }
    }
    if rDone {
      leftDone := true;
    } else {
      assert forall rr | 0 <= rr < n :: grid[rr][left] != '*';
      left := left + 1;
    }
  }
  if !leftDone {
    result := []; return;
  }

  // === FIND RIGHT: last column containing a '*' ===
  var ri := m - 1;
  var rightDone := false;
  while ri >= 0 && !rightDone
    invariant -1 <= ri <= m - 1
    invariant !rightDone ==> forall r | 0 <= r < n :: forall c | ri < c < m :: grid[r][c] != '*'
    invariant rightDone ==> 0 <= ri < m
    invariant rightDone ==> exists r | 0 <= r < n :: grid[r][ri] == '*'
    invariant rightDone ==> forall r | 0 <= r < n :: forall c | ri < c < m :: grid[r][c] != '*'
    decreases ri + 1, !rightDone
  {
    var r := 0;
    var rDone := false;
    while r < n && !rDone
      invariant 0 <= r <= n
      invariant !rDone ==> forall rr | 0 <= rr < r :: grid[rr][ri] != '*'
      invariant rDone ==> 0 <= r < n && grid[r][ri] == '*'
      decreases n - r, !rDone
    {
      if grid[r][ri] == '*' {
        rDone := true;
      } else {
        r := r + 1;
      }
    }
    if rDone {
      rightDone := true;
    } else {
      assert forall rr | 0 <= rr < n :: grid[rr][ri] != '*';
      ri := ri - 1;
    }
  }
  if !rightDone {
    assert false;
    result := []; return;
  }
  var right := ri + 1;

  // left <= ri because column left has a star but columns > ri don't
  if left > ri {
    assert false;
  }

  // === PROVE CONTAINSALLSHADED ===
  // All shaded cells are within the rectangle
  assert forall r | 0 <= r < n :: forall c | 0 <= c < |grid[r]| ::
    grid[r][c] == '*' ==> (top <= r < bottom && left <= c < right);

  // === PROVE TIGHTBOUNDS ===
  // Top edge touches a shaded cell
  assert exists c | left <= c < right :: grid[top][c] == '*';
  // Bottom edge touches a shaded cell
  assert exists c | left <= c < right :: grid[bottom - 1][c] == '*';
  // Left edge touches a shaded cell
  assert exists r | top <= r < bottom :: grid[r][left] == '*';
  // Right edge touches a shaded cell
  assert exists r | top <= r < bottom :: grid[r][right - 1] == '*';

  assert forall r | top <= r < bottom :: right <= |grid[r]| by {
    assert |grid[r]| == m;
  }

  // === EXTRACT SUB-RECTANGLE ===
  result := [];
  var idx := top;
  while idx < bottom
    invariant top <= idx <= bottom
    invariant |result| == idx - top
    invariant forall k | 0 <= k < idx - top :: result[k] == grid[top + k][left..right]
    decreases bottom - idx
  {
    assert |grid[idx]| == m;
    result := result + [grid[idx][left..right]];
    idx := idx + 1;
  }

  // === PROVE POSTCONDITION ===
  assert IsSubRectangle(grid, result, top, bottom, left, right);
  assert 0 <= bottom <= |grid|;
  assert 0 <= left < |grid[0]|;
  assert 0 <= right <= |grid[0]|;
}