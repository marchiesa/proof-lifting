// Problem 4: Dijkstra's Shortest Path with Optimality Proof
//
// Given a weighted directed graph (adjacency list) and a source node,
// compute shortest distances from source to all nodes.
//
// The spec requires OPTIMALITY: computed distance = minimum weight path.

// Graph is represented as adjacency list: graph[u] = list of (v, weight) pairs
// We use parallel sequences for simplicity: adj[u] = seq of target nodes,
// weights[u] = seq of corresponding weights.

// A path is a sequence of node indices representing a walk in the graph
ghost predicate IsValidPath(n: nat, adj: seq<seq<nat>>, path: seq<nat>)
  requires |adj| == n
{
  |path| > 0 &&
  // All nodes in path are valid
  (forall i :: 0 <= i < |path| ==> path[i] < n) &&
  // Each consecutive pair is an edge
  (forall i :: 0 <= i < |path| - 1 ==>
    path[i + 1] in adj[path[i]])
}

// A path from src to dst
ghost predicate IsPathFromTo(n: nat, adj: seq<seq<nat>>, path: seq<nat>, src: nat, dst: nat)
  requires |adj| == n
{
  IsValidPath(n, adj, path) &&
  path[0] == src &&
  path[|path| - 1] == dst
}

// Weight of an edge (u, v) in the graph
ghost function EdgeWeight(adj: seq<seq<nat>>, w: seq<seq<nat>>, u: nat, v: nat): nat
  requires u < |adj| && u < |w|
  requires |adj[u]| == |w[u]|
  requires v in adj[u]
{
  var idx := IndexOf(adj[u], v);
  w[u][idx]
}

// Index of first occurrence of v in s
ghost function IndexOf(s: seq<nat>, v: nat): nat
  requires v in s
  ensures IndexOf(s, v) < |s|
  ensures s[IndexOf(s, v)] == v
  decreases |s|
{
  if s[0] == v then 0
  else 1 + IndexOf(s[1..], v)
}

// Total weight of a path
ghost function PathWeight(n: nat, adj: seq<seq<nat>>, w: seq<seq<nat>>, path: seq<nat>): nat
  requires |adj| == n && |w| == n
  requires forall u :: 0 <= u < n ==> |adj[u]| == |w[u]|
  requires IsValidPath(n, adj, path)
  decreases |path|
{
  if |path| <= 1 then 0
  else
    EdgeWeight(adj, w, path[0], path[1]) +
    PathWeight(n, adj, w, path[1..])
}

// A node is reachable if there exists a path from src to it
ghost predicate IsReachable(n: nat, adj: seq<seq<nat>>, src: nat, dst: nat)
  requires |adj| == n && src < n && dst < n
{
  exists path :: IsPathFromTo(n, adj, path, src, dst)
}

// Well-formed graph: all edges point to valid nodes, parallel weight arrays match
ghost predicate WellFormedGraph(n: nat, adj: seq<seq<nat>>, w: seq<seq<nat>>)
{
  |adj| == n && |w| == n &&
  (forall u :: 0 <= u < n ==> |adj[u]| == |w[u]|) &&
  (forall u :: 0 <= u < n ==>
    forall k :: 0 <= k < |adj[u]| ==> adj[u][k] < n)
}

// Sentinel value for unreachable nodes
const INFINITY: nat := 0xFFFF_FFFF

// OPTIMALITY spec: dist[v] is the shortest path distance from src to v
ghost predicate IsShortestDistances(
  n: nat, adj: seq<seq<nat>>, w: seq<seq<nat>>, src: nat, dist: seq<nat>)
  requires WellFormedGraph(n, adj, w)
  requires src < n
  requires |dist| == n
{
  // Source distance is 0
  dist[src] == 0 &&
  // For every reachable node: dist[v] = min path weight
  (forall v :: 0 <= v < n && v != src ==>
    (
      // If reachable: dist[v] is the weight of some path AND no path has less weight
      (IsReachable(n, adj, src, v) ==>
        (exists path :: IsPathFromTo(n, adj, path, src, v) &&
          PathWeight(n, adj, w, path) == dist[v]) &&
        (forall path :: IsPathFromTo(n, adj, path, src, v) ==>
          PathWeight(n, adj, w, path) >= dist[v])) &&
      // If unreachable: dist[v] is INFINITY
      (!IsReachable(n, adj, src, v) ==> dist[v] == INFINITY)
    ))
}

// Main method: Dijkstra's algorithm
method Dijkstra(n: nat, adj: seq<seq<nat>>, w: seq<seq<nat>>, src: nat)
    returns (dist: seq<nat>)
  requires n > 0
  requires WellFormedGraph(n, adj, w)
  requires src < n
  // All weights are positive (non-negative and no zero-weight cycles concern)
  requires forall u :: 0 <= u < n ==>
    forall k :: 0 <= k < |w[u]| ==> w[u][k] > 0
  ensures |dist| == n
  ensures IsShortestDistances(n, adj, w, src, dist)
{
  // Initialize distances
  var d := new nat[n];
  var i := 0;
  while i < n
  {
    d[i] := INFINITY;
    i := i + 1;
  }
  d[src] := 0;

  // Visited set
  var visited := new bool[n];
  i := 0;
  while i < n
  {
    visited[i] := false;
    i := i + 1;
  }

  // Main loop: process each node
  var count := 0;
  while count < n
  {
    // Find unvisited node with minimum distance
    var u := n; // sentinel: no node found
    var minDist := INFINITY;
    i := 0;
    while i < n
    {
      if !visited[i] && (u == n || d[i] < minDist) {
        u := i;
        minDist := d[i];
      }
      i := i + 1;
    }

    if u == n {
      // No unvisited node found
      break;
    }
    if d[u] == INFINITY {
      // All remaining unvisited nodes are unreachable
      break;
    }

    visited[u] := true;

    // Relax neighbors
    var k := 0;
    while k < |adj[u]|
    {
      var v := adj[u][k];
      var edgeW := w[u][k];
      if !visited[v] && d[u] + edgeW < d[v] {
        d[v] := d[u] + edgeW;
      }
      k := k + 1;
    }

    count := count + 1;
  }

  dist := d[..];
}
