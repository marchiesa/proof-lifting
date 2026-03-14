// Convex Hull (Upper Hull) -- Runtime spec tests

function Cross(x1: int, y1: int, x2: int, y2: int, x3: int, y3: int): int
{
  (x2 - x1) * (y3 - y1) - (y2 - y1) * (x3 - x1)
}

method Main()
{
  // Test Cross product function
  // Cross of (0,0)->(1,0) and (0,0)->(0,1) should be positive (left turn)
  expect Cross(0, 0, 1, 0, 0, 1) == 1, "left turn cross product is positive";

  // Cross of (0,0)->(1,0) and (0,0)->(0,-1) should be negative (right turn)
  expect Cross(0, 0, 1, 0, 0, -1) == -1, "right turn cross product is negative";

  // Cross of collinear points should be 0
  expect Cross(0, 0, 1, 1, 2, 2) == 0, "collinear points give 0 cross product";

  // More cross product tests
  expect Cross(0, 0, 1, 0, 1, 1) == 1, "up from x-axis is left turn";
  expect Cross(0, 0, 1, 0, 1, -1) == -1, "down from x-axis is right turn";
  expect Cross(0, 0, 2, 0, 1, 0) == 0, "points on x-axis are collinear";

  // Test for upper hull: convex hull removes points with non-left turns
  // Points: (0,0), (1,2), (2,1), (3,0)
  // Upper hull should include (0,0), (1,2), (3,0)
  // Check: Cross((0,0),(1,2),(2,1)) should be negative (right turn => keep removing)
  expect Cross(0, 0, 1, 2, 2, 1) < 0, "right turn at (1,2) toward (2,1)";

  // Check: Cross((0,0),(1,2),(3,0)) should be negative (right turn)
  expect Cross(0, 0, 1, 2, 3, 0) < 0, "right turn from (0,0)-(1,2) to (3,0)";

  // For non-left turn (>= 0), point should be removed from hull
  expect Cross(0, 0, 1, 1, 2, 2) >= 0, "collinear should be removed (>= 0)";

  // Triangle: (0,0), (2,4), (4,0) - all should be on hull
  // Cross((0,0),(2,4),(4,0)) < 0 means right turn (valid for upper hull)
  expect Cross(0, 0, 2, 4, 4, 0) < 0, "triangle vertices form right turn";

  print "All spec tests passed\n";
}
