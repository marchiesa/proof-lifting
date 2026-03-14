// Tests for Problem 4: Dijkstra's Shortest Path
include "task.dfy"

method Main()
{
  // Test 1: Simple triangle graph
  // 0 --2--> 1 --3--> 2
  // 0 --10-> 2
  // Shortest: 0->1->2 = 5, not 0->2 = 10
  var adj1: seq<seq<nat>> := [[1, 2], [2], []];
  var w1: seq<seq<nat>> := [[2, 10], [3], []];
  var d1 := Dijkstra(3, adj1, w1, 0);
  print "Test 1 - Triangle graph from 0:\n";
  print "  dist[0] = ", d1[0], " (expected 0)\n";
  print "  dist[1] = ", d1[1], " (expected 2)\n";
  print "  dist[2] = ", d1[2], " (expected 5)\n";

  // Test 2: Disconnected graph
  // 0 --1--> 1, node 2 unreachable
  var adj2: seq<seq<nat>> := [[1], [], []];
  var w2: seq<seq<nat>> := [[1], [], []];
  var d2 := Dijkstra(3, adj2, w2, 0);
  print "Test 2 - Disconnected graph from 0:\n";
  print "  dist[0] = ", d2[0], " (expected 0)\n";
  print "  dist[1] = ", d2[1], " (expected 1)\n";
  print "  dist[2] = ", d2[2], " (expected INFINITY)\n";

  // Test 3: Single node
  var adj3: seq<seq<nat>> := [[]];
  var w3: seq<seq<nat>> := [[]];
  var d3 := Dijkstra(1, adj3, w3, 0);
  print "Test 3 - Single node: dist[0] = ", d3[0], " (expected 0)\n";

  // Test 4: Diamond graph
  // 0 --1--> 1 --1--> 3
  // 0 --1--> 2 --1--> 3
  var adj4: seq<seq<nat>> := [[1, 2], [3], [3], []];
  var w4: seq<seq<nat>> := [[1, 1], [1], [1], []];
  var d4 := Dijkstra(4, adj4, w4, 0);
  print "Test 4 - Diamond graph from 0:\n";
  print "  dist[3] = ", d4[3], " (expected 2)\n";
}
