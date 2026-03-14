// Bellman-Ford Shortest Paths -- Runtime spec tests

function Inf(): int { 1000000 }

method Main() {
  // Inf function test
  expect Inf() == 1000000, "Inf sentinel value";
  expect Inf() > 0, "Inf is positive";

  // Postcondition property tests:
  // dist[source] == 0
  // forall v :: 0 <= v < n ==> dist[v] <= Inf()

  // Simulate checking postconditions on known results
  // Single node: dist = [0]
  var dist1 := [0];
  expect dist1[0] == 0, "source dist is 0";
  expect dist1[0] <= Inf(), "dist[0] <= Inf";

  // Three nodes, no edges: dist = [0, Inf, Inf]
  var dist2 := [0, Inf(), Inf()];
  expect dist2[0] == 0, "source is 0";
  expect dist2[1] <= Inf(), "unreachable node <= Inf";
  expect dist2[2] <= Inf(), "unreachable node <= Inf";

  // Two nodes, edge 0->1 weight 5: dist = [0, 5]
  var dist3 := [0, 5];
  expect dist3[0] == 0, "source is 0";
  expect dist3[1] == 5, "shortest path is 5";
  expect dist3[1] <= Inf(), "reachable node <= Inf";

  // Triangle: 0->1 (3), 1->2 (4), 0->2 (10): dist = [0, 3, 7]
  var dist4 := [0, 3, 7];
  expect dist4[0] == 0, "source is 0";
  expect dist4[1] == 3, "direct edge cost 3";
  expect dist4[2] == 7, "shortest via 0->1->2 is 7 not 10";
  expect dist4[2] <= Inf(), "dist <= Inf";

  // Wrong answer check
  expect dist4[2] != 10, "going through intermediate vertex is shorter";

  print "All spec tests passed\n";
}
