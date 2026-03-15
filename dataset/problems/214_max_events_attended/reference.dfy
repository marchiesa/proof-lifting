// Maximum Events Attended -- Reference solution with invariants

function Max(a: int, b: int): int { if a >= b then a else b }

method MaxEvents(starts: seq<int>, ends: seq<int>) returns (count: int)
  requires |starts| == |ends|
  requires |starts| > 0
  requires forall i :: 0 <= i < |starts| ==> 1 <= starts[i] <= ends[i]
  ensures count >= 0
  ensures count <= |starts|
{
  var n := |starts|;
  var sortedStarts := starts;
  var sortedEnds := ends;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |sortedStarts| == n && |sortedEnds| == n
    invariant forall k :: 0 <= k < n ==> 1 <= sortedStarts[k] <= sortedEnds[k]
    decreases n - i
  {
    var minIdx := i;
    var j := i + 1;
    while j < n
      invariant i + 1 <= j <= n
      invariant i <= minIdx < n
      decreases n - j
    {
      if sortedEnds[j] < sortedEnds[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    if minIdx != i {
      var tmpS := sortedStarts[i];
      var tmpE := sortedEnds[i];
      sortedStarts := sortedStarts[..i] + [sortedStarts[minIdx]] + sortedStarts[i+1..minIdx] + [tmpS] + sortedStarts[minIdx+1..];
      sortedEnds := sortedEnds[..i] + [sortedEnds[minIdx]] + sortedEnds[i+1..minIdx] + [tmpE] + sortedEnds[minIdx+1..];
    }
    i := i + 1;
  }

  var usedDays: set<int> := {};
  count := 0;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant count >= 0
    invariant count <= i
    invariant count <= n
    decreases n - i
  {
    var day := sortedStarts[i];
    var found := false;
    while day <= sortedEnds[i] && !found
      invariant sortedStarts[i] <= day <= sortedEnds[i] + 1
      decreases sortedEnds[i] - day + 1
    {
      if day !in usedDays {
        usedDays := usedDays + {day};
        count := count + 1;
        found := true;
      }
      day := day + 1;
    }
    i := i + 1;
  }
}
