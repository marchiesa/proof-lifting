// Dijkstra's Shortest Path -- Runtime spec tests
// The spec is mostly in postconditions. No standalone spec predicates to test.
// We test the graph validity conditions and distance properties.

// Valid adjacency matrix: all weights >= -1, square
predicate ValidGraph(graph: seq<seq<int>>, n: int)
{
  |graph| == n && n > 0 &&
  (forall i | 0 <= i < n :: |graph[i]| == n) &&
  (forall i, j | 0 <= i < n && 0 <= j < n :: graph[i][j] >= -1)
}

// Valid distance array
predicate ValidDist(dist: seq<int>, n: int, src: int)
  requires 0 <= src < n
{
  |dist| == n &&
  dist[src] == 0 &&
  (forall i | 0 <= i < n :: dist[i] >= -1)
}

method Main()
{
  // Test ValidGraph
  var g1 := [[0, 4, -1], [-1, 0, 1], [-1, -1, 0]];
  expect ValidGraph(g1, 3), "3-node graph is valid";

  var g2 := [[0]];
  expect ValidGraph(g2, 1), "single node graph valid";

  var g3 := [[0, -1], [-1, 0]];
  expect ValidGraph(g3, 2), "disconnected 2-node graph valid";

  // Invalid graphs
  expect !ValidGraph([[0, -2], [-1, 0]], 2), "weight -2 is invalid";
  expect !ValidGraph([], 0), "empty graph (n=0) is invalid (requires n>0)";

  // Test ValidDist
  expect ValidDist([0, 4, 5], 3, 0), "dist from source 0 is valid";
  expect ValidDist([-1, 0, -1], 3, 1), "dist from source 1 is valid";
  expect ValidDist([0], 1, 0), "single node dist valid";

  // Invalid distances
  expect !ValidDist([1, 0, 5], 3, 0), "source dist must be 0";
  expect !ValidDist([0, -2, 5], 3, 0), "dist < -1 is invalid";

  // Test specific expected distances for simple graph
  // g1: 0 --4--> 1 --1--> 2
  // From source 0: dist[0]=0, dist[1]=4, dist[2]=5
  var expected := [0, 4, 5];
  expect ValidDist(expected, 3, 0), "expected Dijkstra output is valid";
  expect expected[0] == 0, "source distance is 0";
  expect expected[1] == 4, "distance to node 1 is 4";
  expect expected[2] == 5, "distance to node 2 is 4+1=5";

  print "All spec tests passed\n";
}
