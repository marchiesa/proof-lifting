// Two rectangles placed side by side (separated along x-axis) in a square of side s.
// Total width = w1 + w2; each height must fit within s.
ghost predicate FitsSideBySide(w1: int, h1: int, w2: int, h2: int, s: int)
{
  w1 + w2 <= s && h1 <= s && h2 <= s
}

// Two rectangles stacked (separated along y-axis) in a square of side s.
// Total height = h1 + h2; each width must fit within s.
ghost predicate FitsStacked(w1: int, h1: int, w2: int, h2: int, s: int)
{
  w1 <= s && w2 <= s && h1 + h2 <= s
}

// Whether two identical a×b rectangles (axis-parallel, possibly rotated) can be
// placed inside a square of side s without overlapping.
// By the separating axis theorem, non-overlapping axis-aligned rectangles are
// separated along at least one axis. We enumerate all orientation pairs
// {(a,b),(b,a)}^2 and both separation directions.
ghost predicate CanFitInSquare(a: int, b: int, s: int)
{
  FitsSideBySide(a, b, a, b, s) || FitsStacked(a, b, a, b, s) ||
  FitsSideBySide(a, b, b, a, s) || FitsStacked(a, b, b, a, s) ||
  FitsSideBySide(b, a, a, b, s) || FitsStacked(b, a, a, b, s) ||
  FitsSideBySide(b, a, b, a, s) || FitsStacked(b, a, b, a, s)
}

// s is the smallest square side length that can contain two a×b rectangles
ghost predicate IsMinimalSide(a: int, b: int, s: int)
{
  CanFitInSquare(a, b, s) && forall s' :: 1 <= s' < s ==> !CanFitInSquare(a, b, s')
}

method MinimalSquare(a: int, b: int) returns (area: int)
  requires 1 <= a && 1 <= b
  ensures exists s :: 1 <= s && area == s * s && IsMinimalSide(a, b, s)
{
  var lo := if a < b then a else b;
  var hi := if a < b then b else a;
  var val := if 2 * lo > hi then 2 * lo else hi;
  area := val * val;
}