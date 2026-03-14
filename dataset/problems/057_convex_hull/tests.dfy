// Convex Hull (Upper Hull) -- Runtime spec tests

function Cross(p1x: int, p1y: int, p2x: int, p2y: int, p3x: int, p3y: int): int
{
  (p2x - p1x) * (p3y - p1y) - (p2y - p1y) * (p3x - p1x)
}

predicate SortedByX(xs: seq<int>)
{
  forall i, j | 0 <= i < j < |xs| :: xs[i] <= xs[j]
}

method Main() {
  // Cross product tests
  // Cross((0,0), (1,0), (0,1)) = (1-0)*(1-0) - (0-0)*(0-0) = 1
  expect Cross(0, 0, 1, 0, 0, 1) == 1, "left turn cross product = 1";
  // Cross((0,0), (1,0), (0,-1)) = (1-0)*(-1-0) - (0-0)*(0-0) = -1
  expect Cross(0, 0, 1, 0, 0, -1) == -1, "right turn cross product = -1";
  // Collinear: Cross((0,0), (1,1), (2,2)) = (1)*(2) - (1)*(2) = 0
  expect Cross(0, 0, 1, 1, 2, 2) == 0, "collinear cross product = 0";
  // Cross((0,0), (2,0), (1,1)) = 2*1 - 0*1 = 2
  expect Cross(0, 0, 2, 0, 1, 1) == 2, "left turn = 2";
  // Cross((0,0), (2,0), (1,-1)) = 2*(-1) - 0*1 = -2
  expect Cross(0, 0, 2, 0, 1, -1) == -2, "right turn = -2";

  // SortedByX positive
  expect SortedByX([0, 1, 2, 3]), "ascending x sorted";
  expect SortedByX([1, 1, 2, 3]), "non-decreasing x sorted";
  expect SortedByX([]), "empty sorted by x";
  expect SortedByX([5]), "singleton sorted by x";

  // SortedByX negative
  expect !SortedByX([3, 1, 2]), "unsorted x";
  expect !SortedByX([2, 1]), "descending x not sorted";

  print "All spec tests passed\n";
}
