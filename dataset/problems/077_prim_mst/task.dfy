// Prim's Minimum Spanning Tree (Array-Based)
// Task: Add loop invariants so that Dafny can verify this program.

predicate ValidGraph(graph: seq<seq<int>>, n: int)
{
  n >= 0 && |graph| == n &&
  (forall i :: 0 <= i < n ==> |graph[i]| == n) &&
  (forall i, j :: 0 <= i < n && 0 <= j < n ==> graph[i][j] >= -1) &&
  (forall i, j :: 0 <= i < n && 0 <= j < n ==> graph[i][j] == graph[j][i])
}

method PrimMST(graph: seq<seq<int>>, n: int) returns (totalWeight: int)
  requires n > 0
  requires ValidGraph(graph, n)
  ensures totalWeight >= -1
{
  var inMST := seq(n, _ => false);
  var key := seq(n, _ => -1);
  key := key[0 := 0];
  totalWeight := 0;
  var count := 0;
  while count < n
  {
    var u := -1;
    var i := 0;
    while i < n
    {
      if !inMST[i] && key[i] != -1 {
        if u == -1 || key[i] < key[u] {
          u := i;
        }
      }
      i := i + 1;
    }
    if u == -1 {
      totalWeight := -1;
      return;
    }
    inMST := inMST[u := true];
    totalWeight := totalWeight + key[u];
    var j := 0;
    while j < n
    {
      if !inMST[j] && graph[u][j] != -1 {
        if key[j] == -1 || graph[u][j] < key[j] {
          key := key[j := graph[u][j]];
        }
      }
      j := j + 1;
    }
    count := count + 1;
  }
}
