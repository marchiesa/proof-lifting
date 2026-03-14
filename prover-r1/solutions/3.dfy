/*
 * Problem 3: BFS Reachability on Adjacency List Graph
 */

ghost predicate ValidGraph(graph: seq<seq<int>>)
{
  forall i, j :: 0 <= i < |graph| && 0 <= j < |graph[i]| ==>
    0 <= graph[i][j] < |graph|
}

ghost predicate IsPath(graph: seq<seq<int>>, path: seq<int>)
  requires ValidGraph(graph)
{
  |path| >= 1 &&
  (forall i :: 0 <= i < |path| ==> 0 <= path[i] < |graph|) &&
  (forall i :: 0 <= i < |path| - 1 ==> path[i+1] in graph[path[i]])
}

ghost predicate Reachable(graph: seq<seq<int>>, s: int, t: int)
  requires ValidGraph(graph)
  requires 0 <= s < |graph|
{
  exists path: seq<int> :: IsPath(graph, path) && path[0] == s && path[|path|-1] == t
}

ghost predicate BFSSpec(graph: seq<seq<int>>, source: int, result: set<int>)
  requires ValidGraph(graph)
  requires 0 <= source < |graph|
{
  (forall v :: v in result ==> 0 <= v < |graph| && Reachable(graph, source, v)) &&
  (forall v :: 0 <= v < |graph| && Reachable(graph, source, v) ==> v in result)
}

lemma ReachableExtend(graph: seq<seq<int>>, s: int, u: int, v: int, pathToU: seq<int>)
  requires ValidGraph(graph)
  requires 0 <= s < |graph|
  requires 0 <= u < |graph|
  requires 0 <= v < |graph|
  requires IsPath(graph, pathToU)
  requires pathToU[0] == s
  requires pathToU[|pathToU|-1] == u
  requires v in graph[u]
  ensures IsPath(graph, pathToU + [v])
  ensures Reachable(graph, s, v)
{
  var newPath := pathToU + [v];
  forall i | 0 <= i < |newPath| - 1
    ensures newPath[i+1] in graph[newPath[i]]
  {
    if i < |pathToU| - 1 { } else { }
  }
}

lemma ReachableSelf(graph: seq<seq<int>>, s: int)
  requires ValidGraph(graph)
  requires 0 <= s < |graph|
  ensures Reachable(graph, s, s)
{
  assert IsPath(graph, [s]);
}

ghost function GraphNodes(graph: seq<seq<int>>): set<int>
{
  set i {:trigger i in GraphNodes(graph)} | 0 <= i < |graph|
}

// If a set containing source is closed under edges, it contains all reachable nodes
lemma ClosedContainsReachable(graph: seq<seq<int>>, source: int, s: set<int>, v: int)
  requires ValidGraph(graph)
  requires 0 <= source < |graph|
  requires source in s
  requires forall x :: x in s ==> 0 <= x < |graph|
  // Closed: all neighbors of nodes in s are in s
  requires forall u :: u in s ==> forall j :: 0 <= j < |graph[u]| ==> graph[u][j] in s
  requires Reachable(graph, source, v)
  ensures v in s
{
  var path :| IsPath(graph, path) && path[0] == source && path[|path|-1] == v;
  var idx := 0;
  while idx < |path|
    invariant 0 <= idx <= |path|
    invariant forall p :: 0 <= p < idx ==> path[p] in s
  {
    if idx == 0 {
    } else {
      var node := path[idx-1];
      var next := path[idx];
      assert node in s;
      assert next in graph[node];
      var j :| 0 <= j < |graph[node]| && graph[node][j] == next;
    }
    idx := idx + 1;
  }
}

method BFS(graph: seq<seq<int>>, source: int) returns (visited: set<int>)
  requires ValidGraph(graph)
  requires 0 <= source < |graph|
  ensures BFSSpec(graph, source, visited)
{
  visited := {source};
  var queue: seq<int> := [source];
  ghost var paths: map<int, seq<int>> := map[source := [source]];
  ghost var expanded: set<int> := {};

  ReachableSelf(graph, source);

  while |queue| > 0
    invariant forall v :: v in visited ==> 0 <= v < |graph|
    invariant source in visited
    invariant visited <= GraphNodes(graph)
    invariant forall v :: v in visited ==> v in paths
    invariant forall v :: v in paths ==>
      IsPath(graph, paths[v]) && paths[v][0] == source && paths[v][|paths[v]|-1] == v
    invariant forall v :: v in queue ==> v in visited
    invariant expanded <= visited
    // Expanded nodes: all their neighbors are in visited
    invariant forall u :: u in expanded ==>
      forall j :: 0 <= j < |graph[u]| ==> graph[u][j] in visited
    // Every non-expanded visited node is in the queue
    invariant forall v :: v in visited && v !in expanded ==> v in multiset(queue)
    // Every queue element is a non-expanded visited node
    invariant forall v :: v in multiset(queue) ==> v in visited && v !in expanded
    // No duplicates in queue
    invariant forall i, j :: 0 <= i < j < |queue| ==> queue[i] != queue[j]
    decreases GraphNodes(graph) - expanded
  {
    var current := queue[0];
    queue := queue[1..];
    assert current in visited;
    assert current !in expanded;

    var i := 0;
    while i < |graph[current]|
      invariant 0 <= i <= |graph[current]|
      invariant forall v :: v in visited ==> 0 <= v < |graph|
      invariant source in visited
      invariant visited <= GraphNodes(graph)
      invariant forall v :: v in visited ==> v in paths
      invariant forall v :: v in paths ==>
        IsPath(graph, paths[v]) && paths[v][0] == source && paths[v][|paths[v]|-1] == v
      invariant forall v :: v in queue ==> v in visited
      invariant expanded <= visited
      invariant current in visited && current !in expanded
      invariant forall j :: 0 <= j < i ==> graph[current][j] in visited
      invariant forall u :: u in expanded ==>
        forall j :: 0 <= j < |graph[u]| ==> graph[u][j] in visited
      // For the inner loop, we weaken the queue tracking:
      // non-expanded, non-current visited nodes are in the queue
      invariant forall v :: v in visited && v !in expanded && v != current ==> v in multiset(queue)
      invariant forall v :: v in multiset(queue) ==> v in visited && v !in expanded
      invariant forall i2, j2 :: 0 <= i2 < j2 < |queue| ==> queue[i2] != queue[j2]
      invariant current !in multiset(queue)
    {
      var neighbor := graph[current][i];
      if neighbor !in visited {
        var pathToCurrent := paths[current];
        ReachableExtend(graph, source, current, neighbor, pathToCurrent);

        assert neighbor !in expanded;  // because expanded <= visited and neighbor !in visited
        visited := visited + {neighbor};
        queue := queue + [neighbor];
        paths := paths[neighbor := pathToCurrent + [neighbor]];
      }
      i := i + 1;
    }

    expanded := expanded + {current};
  }

  // Queue is empty, so every visited node must be expanded
  // (since non-expanded visited nodes would be in multiset(queue), which is empty)
  assert forall v :: v in visited ==> v in expanded;
  // So visited is closed under edges
  assert forall u :: u in visited ==>
    forall j :: 0 <= j < |graph[u]| ==> graph[u][j] in visited;

  forall v | 0 <= v < |graph| && Reachable(graph, source, v)
    ensures v in visited
  {
    ClosedContainsReachable(graph, source, visited, v);
  }

  forall v | v in visited
    ensures 0 <= v < |graph| && Reachable(graph, source, v)
  {
    assert v in paths;
  }
}
