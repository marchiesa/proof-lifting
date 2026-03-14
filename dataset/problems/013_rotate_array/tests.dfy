// Rotate Array -- Runtime spec tests
// The spec is: result[i] == a[(i - k % |a| + |a|) % |a|]
// We test this rotation formula directly.

// Helper: compute expected rotation result
function RotateSpec(a: seq<int>, k: nat): seq<int>
  requires |a| > 0
{
  seq(|a|, i requires 0 <= i < |a| => a[(i - k % |a| + |a|) % |a|])
}

method Main()
{
  // Test basic rotation
  var a1 := [1, 2, 3, 4, 5];
  expect RotateSpec(a1, 2) == [4, 5, 1, 2, 3], "rotate [1,2,3,4,5] by 2 should be [4,5,1,2,3]";

  // Rotate by 0 should be identity
  expect RotateSpec(a1, 0) == [1, 2, 3, 4, 5], "rotate by 0 is identity";

  // Rotate by length should be identity
  expect RotateSpec(a1, 5) == [1, 2, 3, 4, 5], "rotate by length is identity";

  // Rotate by 1
  expect RotateSpec(a1, 1) == [5, 1, 2, 3, 4], "rotate by 1";

  // Rotate by more than length
  expect RotateSpec(a1, 7) == RotateSpec(a1, 2), "rotate by 7 == rotate by 2 (mod 5)";

  // Single element
  var a2 := [42];
  expect RotateSpec(a2, 0) == [42], "single element rotate by 0";
  expect RotateSpec(a2, 7) == [42], "single element rotate by any";

  // Two elements
  var a3 := [10, 20];
  expect RotateSpec(a3, 1) == [20, 10], "rotate [10,20] by 1";
  expect RotateSpec(a3, 2) == [10, 20], "rotate [10,20] by 2 is identity";

  // Length preservation
  expect |RotateSpec(a1, 3)| == 5, "rotation preserves length";

  print "All spec tests passed\n";
}
