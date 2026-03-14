// Serialize/Deserialize Binary Tree -- Runtime spec tests

// ValidSerialization uses bounded quantifier (0 <= i < n) so it should be compilable
// But Dafny predicates with quantifiers won't compile directly. Use bounded version.
function ValidSerializationBounded(a: seq<int>, n: int, i: int): bool
  requires 0 <= i <= n <= |a|
  decreases n - i
{
  if i >= n then true
  else
    var ok := if a[i] == -1 then
                (if 2 * i + 1 < n then a[2*i+1] == -1 else true) &&
                (if 2 * i + 2 < n then a[2*i+2] == -1 else true)
              else true;
    ok && ValidSerializationBounded(a, n, i + 1)
}

function CountNodes(a: seq<int>, n: int): int
  requires 0 <= n <= |a|
{
  if n == 0 then 0
  else (if a[n-1] != -1 then 1 else 0) + CountNodes(a, n - 1)
}

method Main()
{
  // CountNodes: positive cases
  expect CountNodes([1, 2, 3], 3) == 3, "CountNodes([1,2,3]) = 3";
  expect CountNodes([1, -1, 3], 3) == 2, "CountNodes([1,-1,3]) = 2";
  expect CountNodes([-1], 1) == 0, "CountNodes([-1]) = 0";
  expect CountNodes([], 0) == 0, "CountNodes([]) = 0";
  expect CountNodes([1], 1) == 1, "CountNodes([1]) = 1";

  // CountNodes: negative
  expect CountNodes([1, 2, 3], 3) != 2, "CountNodes([1,2,3]) != 2";
  expect CountNodes([1, -1, 3], 3) != 3, "CountNodes([1,-1,3]) != 3";

  // CountNodes: partial count
  expect CountNodes([1, 2, 3], 2) == 2, "CountNodes of first 2 of [1,2,3] = 2";
  expect CountNodes([1, 2, 3], 1) == 1, "CountNodes of first 1 of [1,2,3] = 1";

  // ValidSerializationBounded: valid trees
  expect ValidSerializationBounded([1, 2, 3], 3, 0), "[1,2,3] is valid serialization";
  expect ValidSerializationBounded([1, -1, -1], 3, 0), "[1,-1,-1] is valid (leaf node)";
  expect ValidSerializationBounded([-1], 1, 0), "[-1] is valid (null tree)";
  expect ValidSerializationBounded([], 0, 0), "[] is valid";

  // ValidSerializationBounded: if parent null, children must be null
  expect ValidSerializationBounded([1, -1, 3], 3, 0),
    "[1,-1,3] is valid (null left child has no children in range)";

  // ValidSerializationBounded: invalid (null parent with non-null child)
  expect !ValidSerializationBounded([-1, 2, 3], 3, 0),
    "[-1,2,3] is invalid (null root has non-null children)";
  expect !ValidSerializationBounded([-1, 2, -1], 3, 0),
    "[-1,2,-1] is invalid (null root has non-null left child)";

  // All null
  expect ValidSerializationBounded([-1, -1, -1], 3, 0), "[-1,-1,-1] is valid";
  expect CountNodes([-1, -1, -1], 3) == 0, "All null has 0 nodes";

  print "All spec tests passed\n";
}
