// Topological Sort (Kahn's Algorithm) -- Reference solution with invariants

method KahnTopSort(graph: seq<seq<bool>>, n: int) returns (order: seq<int>, count: int)
  requires n >= 0
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  ensures |order| == count
  ensures 0 <= count <= n
  ensures forall k :: 0 <= k < count ==> 0 <= order[k] < n
  ensures forall i, j :: 0 <= i < j < count ==> order[i] != order[j]
{
  var indeg := seq(n, _ => 0);
  var j := 0;
  while j < n
    invariant 0 <= j <= n
    invariant |indeg| == n
    invariant forall k :: 0 <= k < n ==> indeg[k] >= 0
    decreases n - j
  {
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant |indeg| == n
      invariant forall k :: 0 <= k < n ==> indeg[k] >= 0
      decreases n - i
    {
      if graph[i][j] {
        indeg := indeg[j := indeg[j] + 1];
      }
      i := i + 1;
    }
    j := j + 1;
  }

  var processed := seq(n, _ => false);
  order := [];
  count := 0;

  var rounds := n;
  while rounds > 0
    invariant 0 <= rounds <= n
    invariant 0 <= count <= n
    invariant |order| == count
    invariant |indeg| == n
    invariant |processed| == n
    invariant forall k :: 0 <= k < count ==> 0 <= order[k] < n
    invariant forall k :: 0 <= k < count ==> processed[order[k]]
    invariant forall i, j :: 0 <= i < j < count ==> order[i] != order[j]
    decreases rounds
  {
    var foundAny := false;
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant 0 <= count <= n
      invariant |order| == count
      invariant |indeg| == n
      invariant |processed| == n
      invariant forall k :: 0 <= k < count ==> 0 <= order[k] < n
      invariant forall k :: 0 <= k < count ==> processed[order[k]]
      invariant forall i, j :: 0 <= i < j < count ==> order[i] != order[j]
      decreases n - i
    {
      if !processed[i] && indeg[i] == 0 && count < n {
        processed := processed[i := true];
        order := order + [i];
        count := count + 1;
        foundAny := true;
        var k := 0;
        while k < n
          invariant 0 <= k <= n
          invariant |indeg| == n
          invariant |processed| == n
          invariant |order| == count
          invariant forall k :: 0 <= k < count ==> 0 <= order[k] < n
          invariant forall k :: 0 <= k < count ==> processed[order[k]]
          invariant forall i, j :: 0 <= i < j < count ==> order[i] != order[j]
          decreases n - k
        {
          if graph[i][k] {
            indeg := indeg[k := indeg[k] - 1];
          }
          k := k + 1;
        }
      }
      i := i + 1;
    }
    if !foundAny { break; }
    rounds := rounds - 1;
  }
}
