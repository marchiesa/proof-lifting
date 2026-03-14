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
  // All nodes valid
  (forall i :: 0 <= i < |cycle| ==> cycle[i] < n) &&
  // Each step is an edge
  (forall i :: 0 <= i < |cycle| - 1 ==> cycle[i + 1] in adj[cycle[i]])
}

// The graph has a cycle
ghost predicate HasCycle(n: nat, adj: seq<seq<nat>>)
  requires |adj| == n
{
  exists cycle :: IsCycle(n, adj, cycle)
}

// The graph is a DAG (no cycles)
ghost predicate IsDAG(n: nat, adj: seq<seq<nat>>)
  requires |adj| == n
{
  !HasCycle(n, adj)
}

// A sequence is a permutation of 0..n-1
ghost predicate IsPermutation(order: seq<nat>, n: nat)
{
  |order| == n &&
  (forall i :: 0 <= i < n ==> i in order) &&
  // No duplicates
  (forall i, j :: 0 <= i < j < |order| ==> order[i] != order[j])
}

// Position of node v in the ordering
ghost function PositionOf(order: seq<nat>, v: nat): nat
  requires v in order
  ensures PositionOf(order, v) < |order|
  ensures order[PositionOf(order, v)] == v
  decreases |order|
{
  if order[0] == v then 0
  else 1 + PositionOf(order[1..], v)
}

// Valid topological ordering: for every edge (u,v), u appears before v
ghost predicate IsTopologicalOrder(n: nat, adj: seq<seq<nat>>, order: seq<nat>)
  requires |adj| == n
{
  IsPermutation(order, n) &&
  (forall u :: 0 <= u < n ==>
    forall v :: v in adj[u] ==>
      PositionOf(order, u) < PositionOf(order, v))
}

// Well-formed graph
ghost predicate WellFormedGraph(n: nat, adj: seq<seq<nat>>)
{
  |adj| == n &&
  (forall u :: 0 <= u < n ==>
    forall k :: 0 <= k < |adj[u]| ==> adj[u][k] < n) &&
  // No self-loops
  (forall u :: 0 <= u < n ==>
    forall k :: 0 <= k < |adj[u]| ==> adj[u][k] != u) &&
  // No duplicate edges
  (forall u :: 0 <= u < n ==>
    forall j, k :: 0 <= j < k < |adj[u]| ==> adj[u][j] != adj[u][k])
}

// The COMPLETENESS spec
// Either returns a valid topological order (and graph is DAG)
// or detects a cycle (and graph truly has a cycle)
method TopologicalSort(n: nat, adj: seq<seq<nat>>)
    returns (hasCycle: bool, order: seq<nat>)
  requires n > 0
  requires WellFormedGraph(n, adj)
  ensures hasCycle ==> HasCycle(n, adj)
  ensures !hasCycle ==> IsTopologicalOrder(n, adj, order) && IsDAG(n, adj)
{
  // Compute in-degrees
  var inDeg := new nat[n];
  var i := 0;
  while i < n
  {
    inDeg[i] := 0;
    i := i + 1;
  }
  i := 0;
  while i < n
  {
    var k := 0;
    while k < |adj[i]|
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
  {
    if inDeg[i] == 0 {
      queue := queue + [i];
    }
    i := i + 1;
  }

  // BFS (Kahn's algorithm)
  var result: seq<nat> := [];
  while |queue| > 0
  {
    // Dequeue
    var u := queue[0];
    queue := queue[1..];
    result := result + [u];

    // Reduce in-degree of neighbors
    var k := 0;
    while k < |adj[u]|
    {
      var v := adj[u][k];
      inDeg[v] := inDeg[v] - 1;
      if inDeg[v] == 0 {
        queue := queue + [v];
      }
      k := k + 1;
    }
  }

  if |result| == n {
    hasCycle := false;
    order := result;
  } else {
    // Not all nodes processed => cycle exists
    hasCycle := true;
    order := [];
  }
}
