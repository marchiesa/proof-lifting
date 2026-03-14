// Strongly Connected Components (via Transitive Closure)
// Reference solution with invariants

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
    invariant 0 <= i <= n
    invariant |reach| == i
    invariant forall r :: 0 <= r < i ==> |reach[r]| == n
    invariant forall r :: 0 <= r < i ==> reach[r][r]
    decreases n - i
  {
    var row: seq<bool> := [];
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |row| == j
      invariant j > i ==> row[i]
      invariant j == i ==> true  // haven't added position i yet or at it
      decreases n - j
    {
      row := row + [graph[i][j] || i == j];
      j := j + 1;
    }
    assert row[i];
    reach := reach + [row];
    i := i + 1;
  }

  // Floyd-Warshall
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant |reach| == n
    invariant forall r :: 0 <= r < n ==> |reach[r]| == n
    invariant forall r :: 0 <= r < n ==> reach[r][r]
    decreases n - k
  {
    i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant |reach| == n
      invariant forall r :: 0 <= r < n ==> |reach[r]| == n
      invariant forall r :: 0 <= r < n ==> reach[r][r]
      decreases n - i
    {
      var j := 0;
      while j < n
        invariant 0 <= j <= n
        invariant |reach| == n
        invariant forall r :: 0 <= r < n ==> |reach[r]| == n
        invariant forall r :: 0 <= r < n ==> reach[r][r]
        decreases n - j
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
