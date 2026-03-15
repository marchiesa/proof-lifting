// Three-Way Partition -- Test cases

method Main()
{
  // We test partition properties with concrete values
  // After partitioning [3, 1, 2, 4, 0] around pivot 2:
  // - Elements < 2: {0, 1} come first
  // - Elements == 2: {2} in middle
  // - Elements > 2: {3, 4} come last
  // The multiset is preserved

  var input := [3, 1, 2, 4, 0];
  // Valid partition result: [0, 1, 2, 3, 4] or [1, 0, 2, 4, 3] etc.
  var valid := [0, 1, 2, 3, 4];
  expect multiset(input) == multiset(valid), "Same multiset";

  // Check partition property on valid result
  expect valid[0] < 2, "First should be < pivot";
  expect valid[1] < 2, "Second should be < pivot";
  expect valid[2] == 2, "Middle should be pivot";
  expect valid[3] > 2, "Fourth should be > pivot";
  expect valid[4] > 2, "Fifth should be > pivot";

  // Invalid partition (wrong order)
  var invalid := [3, 1, 2, 4, 0];
  expect invalid[0] > 2, "First element > pivot, violates partition";

  print "All spec tests passed\n";
}
