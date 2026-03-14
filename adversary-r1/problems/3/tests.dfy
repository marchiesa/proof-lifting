/*
 * Tests for Problem 3: BFS Reachability
 *
 * We test the spec predicates on small graphs with known reachability.
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

// Test 1: Single node, no edges. Only the source is reachable.
// Graph: node 0 -> []
lemma test1()
{
  var graph: seq<seq<int>> := [[]];
  assert ValidGraph(graph);

  var result := {0};

  // 0 is reachable from 0 via path [0]
  var p0: seq<int> := [0];
  assert IsPath(graph, p0);
  assert p0[0] == 0 && p0[|p0|-1] == 0;
  assert Reachable(graph, 0, 0);

  assert BFSSpec(graph, 0, result);
}

// Test 2: Linear chain 0 -> 1 -> 2. Source = 0, all reachable.
// Graph: node 0 -> [1], node 1 -> [2], node 2 -> []
lemma test2()
{
  var graph := [[1], [2], []];
  assert ValidGraph(graph);

  var result := {0, 1, 2};

  // Path to 0: [0]
  var p0 := [0];
  assert IsPath(graph, p0) && p0[0] == 0 && p0[|p0|-1] == 0;
  assert Reachable(graph, 0, 0);

  // Path to 1: [0, 1]
  var p1 := [0, 1];
  assert 1 in graph[0];
  assert IsPath(graph, p1) && p1[0] == 0 && p1[|p1|-1] == 1;
  assert Reachable(graph, 0, 1);

  // Path to 2: [0, 1, 2]
  var p2 := [0, 1, 2];
  assert 2 in graph[1];
  assert IsPath(graph, p2) && p2[0] == 0 && p2[|p2|-1] == 2;
  assert Reachable(graph, 0, 2);

  // Now show completeness: any reachable node must be in {0,1,2}
  // Since |graph| == 3 and result == {0,1,2}, every valid node is in result
  assert forall v :: 0 <= v < |graph| ==> v in result;
  assert BFSSpec(graph, 0, result);
}

// Test 3: Disconnected graph. 0 -> 1, 2 -> 3 (no connection).
// Source = 0, only {0, 1} reachable.
// Graph: 0 -> [1], 1 -> [], 2 -> [3], 3 -> []
lemma test3()
{
  var graph := [[1], [], [3], []];
  assert ValidGraph(graph);

  var result := {0, 1};

  // 0 reachable via [0]
  var p0 := [0];
  assert IsPath(graph, p0);
  assert Reachable(graph, 0, 0);

  // 1 reachable via [0, 1]
  var p1 := [0, 1];
  assert 1 in graph[0];
  assert IsPath(graph, p1);
  assert Reachable(graph, 0, 1);

  // 2 is NOT reachable from 0 — we need to show this
  // 3 is NOT reachable from 0
  // We prove: any path starting from 0 can only visit {0, 1}
  assert forall v :: v in result ==> Reachable(graph, 0, v);

  // For completeness: need to show 2 and 3 are not reachable
  // This requires showing no path from 0 reaches 2 or 3
  NotReachable2(graph);
  NotReachable3(graph);

  assert BFSSpec(graph, 0, result);
}

// Helper: prove node 2 is not reachable from 0 in graph [[1],[],[3],[]]
lemma NotReachable2(graph: seq<seq<int>>)
  requires graph == [[1], [], [3], []]
  requires ValidGraph(graph)
  ensures !Reachable(graph, 0, 2)
{
  forall path: seq<int> | IsPath(graph, path) && path[0] == 0
    ensures path[|path|-1] != 2
  {
    PathStaysInComponent(graph, path);
  }
}

lemma NotReachable3(graph: seq<seq<int>>)
  requires graph == [[1], [], [3], []]
  requires ValidGraph(graph)
  ensures !Reachable(graph, 0, 3)
{
  forall path: seq<int> | IsPath(graph, path) && path[0] == 0
    ensures path[|path|-1] != 3
  {
    PathStaysInComponent(graph, path);
  }
}

// Any path from 0 in this graph stays in {0, 1}
lemma PathStaysInComponent(graph: seq<seq<int>>, path: seq<int>)
  requires graph == [[1], [], [3], []]
  requires ValidGraph(graph)
  requires IsPath(graph, path)
  requires path[0] == 0
  ensures forall i :: 0 <= i < |path| ==> path[i] in {0, 1}
  decreases |path|
{
  if |path| == 1 {
    assert path[0] == 0;
  } else {
    // path[0] == 0, so path[1] in graph[0] = [1], so path[1] == 1
    assert path[1] in graph[0];
    assert path[1] == 1;
    // path[1] == 1, graph[1] = [], so if |path| > 2 we need path[2] in graph[1]
    // but graph[1] is empty, so |path| must be <= 2
    if |path| > 2 {
      assert path[2] in graph[path[1]];
      assert graph[1] == [];
      assert false; // contradiction
    }
  }
}
