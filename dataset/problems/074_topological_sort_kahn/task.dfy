// Topological Sort (Kahn's Algorithm)
// Task: Add loop invariants so that Dafny can verify this program.

method KahnTopSort(graph: seq<seq<bool>>, n: int) returns (order: seq<int>, count: int)
  requires n >= 0
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  ensures |order| == count
  ensures 0 <= count <= n
  ensures forall k :: 0 <= k < count ==> 0 <= order[k] < n
  ensures forall i, j :: 0 <= i < j < count ==> order[i] != order[j]
{
  // Compute in-degrees
  var indeg := seq(n, _ => 0);
  var j := 0;
  while j < n
  {
    var i := 0;
    while i < n
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
  {
    var foundAny := false;
    var i := 0;
    while i < n
    {
      if !processed[i] && indeg[i] == 0 && count < n {
        processed := processed[i := true];
        order := order + [i];
        count := count + 1;
        foundAny := true;
        var k := 0;
        while k < n
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
