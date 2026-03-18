// ===== Specification for Teams Forming =====
// Problem: Pair n students into n/2 teams. Students may increase their
// skill (cost 1 each). Paired students must end with equal skills.
// Minimize total cost.
//
// A valid team assignment (d, p) has non-negative increases d[i] and a
// permutation p pairing students so that each team has equal final skills.
// The answer minimizes SumSeq(d) over all valid (d, p).
//
// The minimum equals the sum of consecutive-pair differences after sorting,
// by the rearrangement inequality.

ghost function Abs(x: int): int {
  if x >= 0 then x else -x
}

ghost function SumSeq(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else SumSeq(s[..|s| - 1]) + s[|s| - 1]
}

// A permutation of {0, 1, ..., n-1}
ghost predicate IsPermutation(p: seq<int>, n: int) {
  |p| == n &&
  (forall i | 0 <= i < n :: 0 <= p[i] < n) &&
  (forall i, j | 0 <= i < j < n :: p[i] != p[j])
}

// A valid team assignment: non-negative increases d, permutation p,
// with equal final skills within each team k = (p[2k], p[2k+1])
ghost predicate ValidTeamAssignment(a: seq<int>, d: seq<int>, p: seq<int>)
  requires |a| % 2 == 0
{
  var n := |a|;
  |d| == n && IsPermutation(p, n) &&
  (forall i | 0 <= i < n :: d[i] >= 0) &&
  (forall k | 0 <= k < n / 2 ::
    a[p[2 * k]] + d[p[2 * k]] == a[p[2 * k + 1]] + d[p[2 * k + 1]])
}

// The cost of a team assignment is the total number of skill increases
ghost function AssignmentCost(d: seq<int>): int {
  SumSeq(d)
}

// Functional insertion sort
ghost function InsertSorted(x: int, s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + InsertSorted(x, s[1..])
}

ghost function SortSeq(a: seq<int>): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else InsertSorted(a[|a| - 1], SortSeq(a[..|a| - 1]))
}

// Sum of consecutive-pair absolute differences:
// pairs (s[0],s[1]), (s[2],s[3]), ...
ghost function ConsecutivePairCost(s: seq<int>): int
  decreases |s|
{
  if |s| < 2 then 0
  else Abs(s[|s| - 1] - s[|s| - 2]) + ConsecutivePairCost(s[..|s| - 2])
}

// Minimum team-forming cost: sort then pair consecutively.
// This equals min { AssignmentCost(d) | ValidTeamAssignment(a, d, p) }
// over all valid (d, p), by the rearrangement inequality.
ghost function MinTeamCost(a: seq<int>): int {
  ConsecutivePairCost(SortSeq(a))
}

method TeamsForming(a: seq<int>) returns (ans: int)
  requires |a| % 2 == 0
  ensures ans >= 0
  ensures ans == MinTeamCost(a)
{
  var n := |a|;
  var arr := new int[n];
  var k := 0;
  while k < n {
    arr[k] := a[k];
    k := k + 1;
  }

  // Bubble sort
  var i := 0;
  while i < n {
    var j := 0;
    while j < n - 1 - i {
      if arr[j] > arr[j + 1] {
        var tmp := arr[j];
        arr[j] := arr[j + 1];
        arr[j + 1] := tmp;
      }
      j := j + 1;
    }
    i := i + 1;
  }

  // Sum differences of consecutive pairs
  ans := 0;
  i := 0;
  while i < n {
    ans := ans + arr[i + 1] - arr[i];
    i := i + 2;
  }
}