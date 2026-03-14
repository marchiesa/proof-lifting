// Connected Components (iterative label propagation)
// Task: Add loop invariants so that Dafny can verify this program.
// Assigns a component ID to each vertex by propagating minimum labels along edges.

method AssignComponents(n: int, adj: seq<seq<int>>) returns (comp: array<int>)
  requires n > 0
  requires |adj| == n
  requires forall i :: 0 <= i < n ==> forall j :: 0 <= j < |adj[i]| ==> 0 <= adj[i][j] < n
  ensures comp.Length == n
  ensures forall i :: 0 <= i < n ==> comp[i] >= 0
{
  comp := new int[n];
  var i := 0;
  while i < n
  {
    comp[i] := -1;
    i := i + 1;
  }

  // Seed each node with its own index as component label
  i := 0;
  while i < n
  {
    comp[i] := i;
    i := i + 1;
  }

  // Propagate: for each edge, take the minimum label
  var fuel := n * n;
  var iter := 0;
  while iter < fuel
  {
    i := 0;
    while i < n
    {
      var j := 0;
      while j < |adj[i]|
      {
        var w := adj[i][j];
        if comp[w] < comp[i] {
          comp[i] := comp[w];
        } else if comp[i] < comp[w] {
          comp[w] := comp[i];
        }
        j := j + 1;
      }
      i := i + 1;
    }
    iter := iter + 1;
  }
}
