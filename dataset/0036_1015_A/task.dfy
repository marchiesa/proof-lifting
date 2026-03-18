ghost predicate PointInSegment(p: int, seg: (int, int))
{
  seg.0 <= p <= seg.1
}

ghost predicate PointCoveredByAny(p: int, segments: seq<(int, int)>)
{
  exists i | 0 <= i < |segments| :: PointInSegment(p, segments[i])
}

ghost predicate StrictlyIncreasing(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] < s[j]
}

method PointsInSegments(segments: seq<(int, int)>, m: int) returns (result: seq<int>)
  requires m >= 0
  requires forall i | 0 <= i < |segments| :: 1 <= segments[i].0 <= segments[i].1 <= m
  // Every output point is a valid point in [1, m] that is not covered by any segment
  ensures forall i | 0 <= i < |result| :: 1 <= result[i] <= m
  ensures forall i | 0 <= i < |result| :: !PointCoveredByAny(result[i], segments)
  // Every uncovered point in [1, m] appears in the result (completeness)
  ensures forall p | 1 <= p <= m :: !PointCoveredByAny(p, segments) ==>
    (exists j | 0 <= j < |result| :: result[j] == p)
  // Output is in strictly increasing order (implies no duplicates)
  ensures StrictlyIncreasing(result)
{
  var A := seq(m, (_: int) => true);
  var i := 0;
  while i < |segments| {
    var a := segments[i].0;
    var b := segments[i].1;
    var j := a - 1;
    while j < b {
      if 0 <= j < |A| {
        A := A[j := false];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := [];
  var k := 0;
  while k < m {
    if A[k] {
      result := result + [k + 1];
    }
    k := k + 1;
  }
}