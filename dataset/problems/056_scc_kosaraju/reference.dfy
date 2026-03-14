// Connected Components (iterative labeling) -- Reference solution with invariants

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
    invariant 0 <= i <= n
    invariant comp.Length == n
    invariant forall k :: 0 <= k < i ==> comp[k] == -1
    decreases n - i
  {
    comp[i] := -1;
    i := i + 1;
  }

  var compId := 0;
  // Iterative flood fill: repeat passes until no changes
  // Each pass propagates labels one step through edges
  var changed := true;
  var fuel := n * n; // Upper bound on iterations needed

  // First, seed each unlabeled node with its own component
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant comp.Length == n
    invariant forall k :: 0 <= k < i ==> comp[k] >= 0
    invariant forall k :: i <= k < n ==> comp[k] == -1
    decreases n - i
  {
    comp[i] := i;
    i := i + 1;
  }

  // Propagate: for each edge, take the minimum label
  var iter := 0;
  while iter < fuel
    invariant comp.Length == n
    invariant forall k :: 0 <= k < n ==> comp[k] >= 0
    decreases fuel - iter
  {
    i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant comp.Length == n
      invariant forall k :: 0 <= k < n ==> comp[k] >= 0
      decreases n - i
    {
      var j := 0;
      while j < |adj[i]|
        invariant 0 <= j <= |adj[i]|
        invariant comp.Length == n
        invariant forall k :: 0 <= k < n ==> comp[k] >= 0
        decreases |adj[i]| - j
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
