// Tests for Problem 5: Topological Sort with Cycle Detection
include "task.dfy"

method Main()
{
  // Test 1: Simple DAG
  // 0 -> 1 -> 2
  var adj1: seq<seq<nat>> := [[1], [2], []];
  var cyc1, ord1 := TopologicalSort(3, adj1);
  print "Test 1 - Linear DAG 0->1->2:\n";
  print "  hasCycle: ", cyc1, " (expected false)\n";
  if !cyc1 {
    print "  order: ", ord1, " (expected [0,1,2])\n";
  }

  // Test 2: Diamond DAG
  // 0 -> 1, 0 -> 2, 1 -> 3, 2 -> 3
  var adj2: seq<seq<nat>> := [[1, 2], [3], [3], []];
  var cyc2, ord2 := TopologicalSort(4, adj2);
  print "Test 2 - Diamond DAG:\n";
  print "  hasCycle: ", cyc2, " (expected false)\n";
  if !cyc2 {
    print "  order: ", ord2, "\n";
  }

  // Test 3: Simple cycle
  // 0 -> 1 -> 2 -> 0
  var adj3: seq<seq<nat>> := [[1], [2], [0]];
  var cyc3, ord3 := TopologicalSort(3, adj3);
  print "Test 3 - Cycle 0->1->2->0:\n";
  print "  hasCycle: ", cyc3, " (expected true)\n";

  // Test 4: Disconnected DAG
  // 0 -> 1, 2 -> 3 (two components)
  var adj4: seq<seq<nat>> := [[1], [], [3], []];
  var cyc4, ord4 := TopologicalSort(4, adj4);
  print "Test 4 - Disconnected DAG:\n";
  print "  hasCycle: ", cyc4, " (expected false)\n";
  if !cyc4 {
    print "  order: ", ord4, "\n";
  }

  // Test 5: Single node
  var adj5: seq<seq<nat>> := [[]];
  var cyc5, ord5 := TopologicalSort(1, adj5);
  print "Test 5 - Single node:\n";
  print "  hasCycle: ", cyc5, " (expected false)\n";
  if !cyc5 {
    print "  order: ", ord5, " (expected [0])\n";
  }

  // Test 6: Cycle in part of graph
  // 0 -> 1, 1 -> 2, 2 -> 1 (cycle), 3 standalone
  var adj6: seq<seq<nat>> := [[1], [2], [1], []];
  var cyc6, ord6 := TopologicalSort(4, adj6);
  print "Test 6 - Partial cycle:\n";
  print "  hasCycle: ", cyc6, " (expected true)\n";
}
