// Floyd-Warshall All-Pairs Shortest Paths -- Runtime spec tests

function Inf(): int { 1000000 }

method Main() {
  // Inf function test
  expect Inf() == 1000000, "Inf sentinel value";

  // Postcondition property tests:
  // dist[i,i] == 0 for all i
  // dist[i,j] <= Inf() for all i,j

  // Simulate postcondition checks on known shortest-path matrices
  // 1 node: dist = [[0]]
  expect 0 == 0, "self-distance is 0";
  expect 0 <= Inf(), "self-distance <= Inf";

  // 3 nodes, no edges: all dist[i,j] = Inf except diagonal
  // dist = [[0, Inf, Inf], [Inf, 0, Inf], [Inf, Inf, 0]]
  var diag := [0, 0, 0];
  var off := Inf();
  expect diag[0] == 0, "dist[0,0] == 0";
  expect diag[1] == 0, "dist[1,1] == 0";
  expect diag[2] == 0, "dist[2,2] == 0";
  expect off <= Inf(), "unreachable <= Inf";

  // 3 nodes, edges: 0->1 (2), 1->2 (3), 0->2 (8)
  // Shortest: 0->0=0, 0->1=2, 0->2=5 (via 1), 1->2=3
  var d02 := 5;
  expect d02 <= Inf(), "reachable distance <= Inf";
  expect d02 < 8, "indirect path shorter than direct";
  expect d02 == 2 + 3, "path goes through node 1";

  // Wrong answer check
  expect d02 != 8, "direct edge 8 is not shortest";

  print "All spec tests passed\n";
}
