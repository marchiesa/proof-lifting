// Absolute difference of two integers
ghost function AbsDiff(x: int, y: int): int
{
  if x >= y then x - y else y - x
}

// Twice the area of a triangle with vertices (x1,y1), (x2,y2), (x3,y3),
// computed via the shoelace formula: 2*Area = |x1(y2-y3) + x2(y3-y1) + x3(y1-y2)|
ghost function TwiceTriangleArea(x1: int, y1: int, x2: int, y2: int, x3: int, y3: int): int
{
  AbsDiff(x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2), 0)
}

// The set of distinct nonzero twice-area values of pastures (triangles) formed
// by choosing two x-axis trees (at positions a[i] and a[j]) and the tree at (0,1).
// Since any three x-axis trees are collinear (zero area), every nonzero-area
// triangle must include the (0,1) tree, so this covers all valid pastures.
ghost function DistinctPastureAreas(a: seq<int>): set<int>
{
  set i: int, j: int
    | 0 <= i < |a| && 0 <= j < |a| && i != j
      && TwiceTriangleArea(a[i], 0, a[j], 0, 0, 1) > 0
    :: TwiceTriangleArea(a[i], 0, a[j], 0, 0, 1)
}

method BovineDilemma(a: seq<int>) returns (count: int)
  ensures count == |DistinctPastureAreas(a)|
{
  var s: set<int> := {};
  for i := 0 to |a| {
    for j := 0 to |a| {
      if a[i] > a[j] {
        s := s + {a[i] - a[j]};
      }
    }
  }
  count := |s|;
}