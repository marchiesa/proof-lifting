// Strongly Connected Components (via Transitive Closure)
// Task: Add loop invariants so that Dafny can verify this program.

// Compute transitive closure using Floyd-Warshall
method TransitiveClosure(graph: seq<seq<bool>>, n: int) returns (reach: seq<seq<bool>>)
  requires n >= 0
  requires |graph| == n
  requires forall i :: 0 <= i < n ==> |graph[i]| == n
  ensures |reach| == n
  ensures forall i :: 0 <= i < n ==> |reach[i]| == n
  ensures forall i :: 0 <= i < n ==> reach[i][i]  // reflexive
{
  // Initialize: reach[i][j] = graph[i][j] || (i == j)
  reach := [];
  var i := 0;
  while i < n
  {
    var row: seq<bool> := [];
    var j := 0;
    while j < n
    {
      row := row + [graph[i][j] || i == j];
      j := j + 1;
    }
    reach := reach + [row];
    i := i + 1;
  }

  // Floyd-Warshall
  var k := 0;
  while k < n
  {
    i := 0;
    while i < n
    {
      var j := 0;
      while j < n
      {
        if reach[i][k] && reach[k][j] {
          reach := reach[i := reach[i][j := true]];
        }
        j := j + 1;
      }
      i := i + 1;
    }
    k := k + 1;
  }
}
