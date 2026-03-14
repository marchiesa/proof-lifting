// Array Rotation -- Runtime spec tests

// The spec: ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[(i + k) % a.Length])
// We test the rotation spec by checking expected values after rotation.

method CheckRotation(original: seq<int>, k: nat, result: seq<int>) returns (ok: bool)
  requires |original| > 0
  requires |result| == |original|
{
  var i := 0;
  while i < |original|
  {
    if result[i] != original[(i + k) % |original|] { return false; }
    i := i + 1;
  }
  return true;
}

method Main()
{
  // Test: rotate [1,2,3,4,5] by 2 => [3,4,5,1,2]
  var r := CheckRotation([1, 2, 3, 4, 5], 2, [3, 4, 5, 1, 2]);
  expect r, "Rotate [1,2,3,4,5] by 2 should give [3,4,5,1,2]";

  // Test: rotate by 0 => identity
  r := CheckRotation([1, 2, 3], 0, [1, 2, 3]);
  expect r, "Rotate by 0 should be identity";

  // Test: rotate by length => identity
  r := CheckRotation([1, 2, 3], 3, [1, 2, 3]);
  expect r, "Rotate by length should be identity";

  // Test: rotate by 1
  r := CheckRotation([1, 2, 3, 4], 1, [2, 3, 4, 1]);
  expect r, "Rotate [1,2,3,4] by 1 should give [2,3,4,1]";

  // Test: rotate single element
  r := CheckRotation([42], 5, [42]);
  expect r, "Rotate single element by any k should be identity";

  // Test: rotate by more than length
  r := CheckRotation([1, 2, 3], 5, [3, 1, 2]);
  expect r, "Rotate [1,2,3] by 5 should give [3,1,2] (5 mod 3 = 2)";

  // Negative: wrong rotation result
  r := CheckRotation([1, 2, 3, 4, 5], 2, [1, 2, 3, 4, 5]);
  expect !r, "Rotate by 2 should not be identity for [1,2,3,4,5]";

  r := CheckRotation([1, 2, 3], 1, [3, 1, 2]);
  expect !r, "Rotate [1,2,3] by 1 should not give [3,1,2]";

  print "All spec tests passed\n";
}
