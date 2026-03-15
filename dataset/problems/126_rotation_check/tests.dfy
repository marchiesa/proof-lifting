// Rotation Check -- Test cases

predicate IsRotation(a: seq<int>, b: seq<int>)
{
  |a| == |b| &&
  exists k :: 0 <= k <= |a| && b == a[k..] + a[..k]
}

method Main()
{
  // Test IsRotation - positive
  expect IsRotation([], []), "Empty seqs are rotations";
  expect IsRotation([1], [1]), "Single element";
  expect IsRotation([1, 2, 3], [1, 2, 3]), "Same seq (rotation by 0)";
  expect IsRotation([1, 2, 3], [2, 3, 1]), "Rotation by 1";
  expect IsRotation([1, 2, 3], [3, 1, 2]), "Rotation by 2";

  // Test IsRotation - negative
  expect !IsRotation([1, 2, 3], [1, 3, 2]), "Not a rotation";
  expect !IsRotation([1, 2], [1, 2, 3]), "Different lengths";
  expect !IsRotation([1, 1, 2], [2, 2, 1]), "Not a rotation (similar elements)";

  print "All spec tests passed\n";
}
