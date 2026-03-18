// --- Specification ---

ghost function Min2(x: int, y: int): int {
  if x <= y then x else y
}

// Given that segments horizI and horizJ are the horizontal pair,
// returns the indices of the complementary (vertical) pair.
ghost function ComplementPair(horizI: int, horizJ: int): (int, int)
  requires 0 <= horizI < horizJ < 4
{
  if horizI == 0 && horizJ == 1 then (2, 3)
  else if horizI == 0 && horizJ == 2 then (1, 3)
  else if horizI == 0 && horizJ == 3 then (1, 2)
  else if horizI == 1 && horizJ == 2 then (0, 3)
  else if horizI == 1 && horizJ == 3 then (0, 2)
  else (0, 1)
}

// Rectangle width: limited by the shorter horizontal segment.
ghost function RectWidth(a: seq<int>, horizI: int, horizJ: int): int
  requires |a| == 4
  requires 0 <= horizI < horizJ < 4
{
  Min2(a[horizI], a[horizJ])
}

// Rectangle height: limited by the shorter vertical segment.
ghost function RectHeight(a: seq<int>, horizI: int, horizJ: int): int
  requires |a| == 4
  requires 0 <= horizI < horizJ < 4
{
  var vp := ComplementPair(horizI, horizJ);
  Min2(a[vp.0], a[vp.1])
}

// Area of the rectangle enclosed when segments horizI, horizJ are horizontal
// and the remaining two segments are vertical.
ghost function AssignmentArea(a: seq<int>, horizI: int, horizJ: int): int
  requires |a| == 4
  requires 0 <= horizI < horizJ < 4
{
  RectWidth(a, horizI, horizJ) * RectHeight(a, horizI, horizJ)
}

// True when 'area' is the maximum rectangle area over all ways to
// partition the four segments into a horizontal pair and a vertical pair.
ghost predicate IsOptimalArea(a: seq<int>, area: int)
  requires |a| == 4
{
  // Achievable: some assignment of 2 horizontal + 2 vertical yields this area
  (exists i | 0 <= i < 4 :: exists j | i + 1 <= j < 4 ::
    area == AssignmentArea(a, i, j))
  &&
  // Optimal: no assignment yields a larger area
  (forall i | 0 <= i < 4 :: forall j | i + 1 <= j < 4 ::
    area >= AssignmentArea(a, i, j))
}

// --- Implementation ---

method FourSegments(a: seq<int>) returns (area: int)
  requires |a| == 4
  requires forall i | 0 <= i < 4 :: a[i] > 0
  ensures IsOptimalArea(a, area)
{
  // Find max value and its index
  var maxVal := a[0];
  var maxIdx := 0;
  var i := 1;
  while i < |a|
  {
    if a[i] > maxVal {
      maxVal := a[i];
      maxIdx := i;
    }
    i := i + 1;
  }

  // Build remaining sequence without the first max
  var remaining: seq<int> := [];
  i := 0;
  while i < |a|
  {
    if i != maxIdx {
      remaining := remaining + [a[i]];
    }
    i := i + 1;
  }

  // Find min and max of remaining
  var lo := remaining[0];
  var hi := remaining[0];
  i := 1;
  while i < |remaining|
  {
    if remaining[i] < lo {
      lo := remaining[i];
    }
    if remaining[i] > hi {
      hi := remaining[i];
    }
    i := i + 1;
  }

  area := lo * hi;
  return;
}