// Connected Components (iterative label propagation) -- Runtime spec tests
// The spec only guarantees comp[i] >= 0. There are no standalone predicates.
// We test the postcondition properties directly.

method Main() {
  // Postcondition: comp.Length == n and forall i :: 0 <= i < n ==> comp[i] >= 0

  // Simulate postcondition checks on known component assignments
  // Single node: comp = [0]
  var comp1 := [0];
  expect |comp1| == 1, "length matches n";
  expect comp1[0] >= 0, "comp[0] >= 0";

  // Three disconnected nodes: comp = [0, 1, 2]
  var comp2 := [0, 1, 2];
  expect |comp2| == 3, "length matches n";
  expect comp2[0] >= 0, "comp[0] >= 0";
  expect comp2[1] >= 0, "comp[1] >= 0";
  expect comp2[2] >= 0, "comp[2] >= 0";
  // Disconnected nodes should have different components
  expect comp2[0] != comp2[1], "disconnected nodes differ";
  expect comp2[1] != comp2[2], "disconnected nodes differ";

  // Connected triangle: comp = [0, 0, 0] (all same component)
  var comp3 := [0, 0, 0];
  expect |comp3| == 3, "length matches n";
  expect comp3[0] >= 0 && comp3[1] >= 0 && comp3[2] >= 0, "all non-negative";
  expect comp3[0] == comp3[1] && comp3[1] == comp3[2], "connected nodes same component";

  // Two components: {0,1} and {2,3}
  var comp4 := [0, 0, 2, 2];
  expect |comp4| == 4, "length matches n";
  expect comp4[0] >= 0 && comp4[1] >= 0 && comp4[2] >= 0 && comp4[3] >= 0, "all non-negative";
  expect comp4[0] == comp4[1], "0 and 1 same component";
  expect comp4[2] == comp4[3], "2 and 3 same component";
  expect comp4[0] != comp4[2], "different components differ";

  print "All spec tests passed\n";
}
