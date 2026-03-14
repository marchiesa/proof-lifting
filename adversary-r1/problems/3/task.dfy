/*
 * Problem 3: BFS Reachability on Adjacency List Graph
 *
 * Given a directed graph as an adjacency list (seq<seq<int>>) and a source
 * node, compute the set of all nodes reachable from the source.
 * The postcondition requires that the returned set is exactly the
 * set of nodes reachable via paths in the graph.
 */

// A valid graph: all adjacency references are within bounds
ghost predicate ValidGraph(graph: seq<seq<int>>)
{
  forall i, j :: 0 <= i < |graph| && 0 <= j < |graph[i]| ==>
    0 <= graph[i][j] < |graph|
}

// A path is a sequence of nodes where consecutive nodes are connected by edges
ghost predicate IsPath(graph: seq<seq<int>>, path: seq<int>)
  requires ValidGraph(graph)
{
  |path| >= 1 &&
  (forall i :: 0 <= i < |path| ==> 0 <= path[i] < |graph|) &&
  (forall i :: 0 <= i < |path| - 1 ==> path[i+1] in graph[path[i]])
}

// Node t is reachable from node s if there exists a path from s to t
ghost predicate Reachable(graph: seq<seq<int>>, s: int, t: int)
  requires ValidGraph(graph)
  requires 0 <= s < |graph|
{
  exists path: seq<int> :: IsPath(graph, path) && path[0] == s && path[|path|-1] == t
}

// The spec: the returned set is exactly the reachable set
ghost predicate BFSSpec(graph: seq<seq<int>>, source: int, result: set<int>)
  requires ValidGraph(graph)
  requires 0 <= source < |graph|
{
  // Every node in result is reachable from source
  (forall v :: v in result ==> 0 <= v < |graph| && Reachable(graph, source, v)) &&
  // Every reachable node is in result
  (forall v :: 0 <= v < |graph| && Reachable(graph, source, v) ==> v in result)
}

// BFS implementation
method BFS(graph: seq<seq<int>>, source: int) returns (visited: set<int>)
  requires ValidGraph(graph)
  requires 0 <= source < |graph|
  ensures BFSSpec(graph, source, visited)
{
  visited := {source};
  var queue: seq<int> := [source];
  // ghost var paths: map<int, seq<int>> := map[source := [source]];

  // BFS main loop
  while |queue| > 0
    // INVARIANT NEEDED HERE
  {
    var current := queue[0];
    queue := queue[1..];

    // Explore neighbors
    var i := 0;
    while i < |graph[current]|
      // INVARIANT NEEDED HERE
    {
      var neighbor := graph[current][i];
      if neighbor !in visited {
        visited := visited + {neighbor};
        queue := queue + [neighbor];
        // ghost: record path to neighbor
      }
      i := i + 1;
    }
  }
}
