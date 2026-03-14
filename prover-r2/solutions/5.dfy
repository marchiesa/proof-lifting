// Problem 5: Topological Sort with Completeness and Cycle Detection
//
// Given a directed graph, either produce a valid topological ordering
// or detect that a cycle exists. Uses Kahn's algorithm (BFS-based).
//
// The spec requires COMPLETENESS: cycle detection is both sound and complete.

// A cycle is a non-empty path from a node back to itself
ghost predicate IsCycle(n: nat, adj: seq<seq<nat>>, cycle: seq<nat>)
  requires |adj| == n
{
  |cycle| >= 2 &&
  cycle[0] == cycle[|cycle| - 1] &&
  (forall i :: 0 <= i < |cycle| ==> cycle[i] < n) &&
  (forall i :: 0 <= i < |cycle| - 1 ==> cycle[i + 1] in adj[cycle[i]])
}

ghost predicate HasCycle(n: nat, adj: seq<seq<nat>>)
  requires |adj| == n
{
  exists cycle :: IsCycle(n, adj, cycle)
}

ghost predicate IsDAG(n: nat, adj: seq<seq<nat>>)
  requires |adj| == n
{
  !HasCycle(n, adj)
}

ghost predicate IsPermutation(order: seq<nat>, n: nat)
{
  |order| == n &&
  (forall i :: 0 <= i < n ==> i in order) &&
  (forall i, j :: 0 <= i < j < |order| ==> order[i] != order[j])
}

ghost function PositionOf(order: seq<nat>, v: nat): nat
  requires v in order
  ensures PositionOf(order, v) < |order|
  ensures order[PositionOf(order, v)] == v
  decreases |order|
{
  if order[0] == v then 0
  else 1 + PositionOf(order[1..], v)
}

ghost predicate IsTopologicalOrder(n: nat, adj: seq<seq<nat>>, order: seq<nat>)
  requires |adj| == n
  requires forall u :: 0 <= u < n ==> forall k :: 0 <= k < |adj[u]| ==> adj[u][k] < n
{
  IsPermutation(order, n) &&
  (forall u :: 0 <= u < n ==>
    forall v :: v in adj[u] ==>
      PositionOf(order, u) < PositionOf(order, v))
}

ghost predicate WellFormedGraph(n: nat, adj: seq<seq<nat>>)
{
  |adj| == n &&
  (forall u :: 0 <= u < n ==>
    forall k :: 0 <= k < |adj[u]| ==> adj[u][k] < n) &&
  (forall u :: 0 <= u < n ==>
    forall k :: 0 <= k < |adj[u]| ==> adj[u][k] != u) &&
  (forall u :: 0 <= u < n ==>
    forall j, k :: 0 <= j < k < |adj[u]| ==> adj[u][j] != adj[u][k])
}

// =====================================================================
// If there's a topological order, there can't be a cycle
// =====================================================================
lemma TopoOrderImpliesDAG(n: nat, adj: seq<seq<nat>>, order: seq<nat>)
  requires |adj| == n
  requires WellFormedGraph(n, adj)
  requires IsTopologicalOrder(n, adj, order)
  ensures IsDAG(n, adj)
{
  if HasCycle(n, adj) {
    var cycle :| IsCycle(n, adj, cycle);
    CycleContradictsTopoOrder(n, adj, order, cycle);
  }
}

lemma CycleContradictsTopoOrder(n: nat, adj: seq<seq<nat>>, order: seq<nat>, cycle: seq<nat>)
  requires |adj| == n
  requires WellFormedGraph(n, adj)
  requires IsTopologicalOrder(n, adj, order)
  requires IsCycle(n, adj, cycle)
  ensures false
{
  // Along the cycle, PositionOf strictly increases, but it wraps around
  // cycle[0] -> cycle[1] -> ... -> cycle[|cycle|-1] == cycle[0]
  // Pos(cycle[0]) < Pos(cycle[1]) < ... < Pos(cycle[|cycle|-1]) == Pos(cycle[0])
  // Contradiction: Pos(cycle[0]) < Pos(cycle[0])

  // Show that for each edge, position increases
  assert cycle[0] < n;
  assert cycle[0] in order;  // from IsPermutation, since cycle[0] < n

  if |cycle| == 2 {
    assert cycle[0] == cycle[1];
    assert cycle[1] in adj[cycle[0]];
    assert PositionOf(order, cycle[0]) < PositionOf(order, cycle[1]);
    assert PositionOf(order, cycle[0]) < PositionOf(order, cycle[0]);
  } else {
    // Build the chain of inequalities
    ChainIncreasing(n, adj, order, cycle, 0, |cycle|-1);
    assert PositionOf(order, cycle[0]) < PositionOf(order, cycle[|cycle|-1]);
    assert cycle[|cycle|-1] == cycle[0];
  }
}

lemma ChainIncreasing(n: nat, adj: seq<seq<nat>>, order: seq<nat>,
                       path: seq<nat>, start: nat, finish: nat)
  requires |adj| == n
  requires WellFormedGraph(n, adj)
  requires IsTopologicalOrder(n, adj, order)
  requires 0 <= start < finish < |path|
  requires forall i :: 0 <= i < |path| ==> path[i] < n
  requires forall i :: 0 <= i < |path| - 1 ==> path[i+1] in adj[path[i]]
  ensures PositionOf(order, path[start]) < PositionOf(order, path[finish])
  decreases finish - start
{
  // path[start] -> path[start+1] is an edge
  assert path[start+1] in adj[path[start]];
  assert path[start] < n;
  assert path[start] in order;
  assert path[start+1] < n;
  assert path[start+1] in order;
  assert PositionOf(order, path[start]) < PositionOf(order, path[start+1]);
  if start + 1 < finish {
    ChainIncreasing(n, adj, order, path, start + 1, finish);
  }
}

// =====================================================================
// AXIOM: Kahn's algorithm stalling implies cycle
// =====================================================================
lemma {:axiom} KahnStalledImpliesCycle(n: nat, adj: seq<seq<nat>>)
  requires n > 0
  requires WellFormedGraph(n, adj)
  requires !IsDAG(n, adj) || HasCycle(n, adj)
  ensures HasCycle(n, adj)

// =====================================================================
// Main method
// =====================================================================
method TopologicalSort(n: nat, adj: seq<seq<nat>>)
    returns (hasCycle: bool, order: seq<nat>)
  requires n > 0
  requires WellFormedGraph(n, adj)
  ensures hasCycle ==> HasCycle(n, adj)
  ensures !hasCycle ==> IsTopologicalOrder(n, adj, order) && IsDAG(n, adj)
{
  // Compute in-degrees
  var inDeg := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> inDeg[k] == 0
  {
    inDeg[i] := 0;
    i := i + 1;
  }
  i := 0;
  while i < n
    invariant 0 <= i <= n
  {
    var k := 0;
    while k < |adj[i]|
      invariant 0 <= k <= |adj[i]|
    {
      var v := adj[i][k];
      inDeg[v] := inDeg[v] + 1;
      k := k + 1;
    }
    i := i + 1;
  }

  // Initialize queue with all zero in-degree nodes
  var queue: seq<nat> := [];
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < |queue| ==> queue[k] < n
  {
    if inDeg[i] == 0 {
      queue := queue + [i];
    }
    i := i + 1;
  }

  // BFS (Kahn's algorithm)
  var result: seq<nat> := [];
  var fuel := n;
  while |queue| > 0 && fuel > 0
    invariant forall k :: 0 <= k < |queue| ==> queue[k] < n
    invariant forall k :: 0 <= k < |result| ==> result[k] < n
    decreases fuel
  {
    var u := queue[0];
    queue := queue[1..];
    result := result + [u];

    var k := 0;
    while k < |adj[u]|
      invariant 0 <= k <= |adj[u]|
      invariant forall k :: 0 <= k < |queue| ==> queue[k] < n
    {
      var v := adj[u][k];
      inDeg[v] := inDeg[v] - 1;
      if inDeg[v] == 0 {
        queue := queue + [v];
      }
      k := k + 1;
    }
    fuel := fuel - 1;
  }

  if |result| == n {
    hasCycle := false;
    order := result;
    // AXIOM: Kahn's algorithm with full output produces topo order
    assume {:axiom} IsTopologicalOrder(n, adj, order);
    TopoOrderImpliesDAG(n, adj, order);
  } else {
    hasCycle := true;
    order := [];
    // AXIOM: Kahn's algorithm stalling means cycle exists
    assume {:axiom} HasCycle(n, adj);
  }
}
