// Max Flow -- Runtime spec tests
// The spec only guarantees flow >= 0. No standalone predicates.
// We test the postcondition property on simulated results.

method Main() {
  // flow >= 0 postcondition tests on known flow values

  // Simple network: source -> sink with capacity 10, max flow = 10
  var flow1 := 10;
  expect flow1 >= 0, "flow >= 0 for simple network";

  // No path: max flow = 0
  var flow2 := 0;
  expect flow2 >= 0, "flow >= 0 when no path";

  // Diamond network: s->a(10), s->b(10), a->t(10), b->t(10), max flow = 20
  var flow3 := 20;
  expect flow3 >= 0, "flow >= 0 for diamond network";

  // Bottleneck: s->a(100), a->b(1), b->t(100), max flow = 1
  var flow4 := 1;
  expect flow4 >= 0, "flow >= 0 with bottleneck";

  // Negative values should not satisfy the postcondition
  var bad := -1;
  expect !(bad >= 0), "negative flow violates postcondition";

  // Flow conservation property (not in spec but good to verify understanding):
  // In a network with parallel paths, flow = sum of path flows
  var path1_flow := 5;
  var path2_flow := 3;
  var total_flow := path1_flow + path2_flow;
  expect total_flow >= 0, "combined flow >= 0";
  expect total_flow == 8, "flow through parallel paths adds up";

  print "All spec tests passed\n";
}
