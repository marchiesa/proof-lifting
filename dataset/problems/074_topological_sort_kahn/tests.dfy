// Topological Sort (Kahn's) -- Runtime spec tests

// The spec ensures:
//   |order| == count
//   0 <= count <= n
//   forall k :: 0 <= k < count ==> 0 <= order[k] < n
//   forall i, j :: 0 <= i < j < count ==> order[i] != order[j]

method CheckTopoSpec(order: seq<int>, count: int, n: int) returns (ok: bool)
{
  if |order| != count { return false; }
  if count < 0 || count > n { return false; }
  // All elements in range [0, n)
  var k := 0;
  while k < count
  {
    if order[k] < 0 || order[k] >= n { return false; }
    k := k + 1;
  }
  // All elements distinct
  var i := 0;
  while i < count
  {
    var j := i + 1;
    while j < count
    {
      if order[i] == order[j] { return false; }
      j := j + 1;
    }
    i := i + 1;
  }
  return true;
}

method Main()
{
  // Valid: correct topological order for DAG 0->1->2
  var r := CheckTopoSpec([0, 1, 2], 3, 3);
  expect r, "Valid topo order [0,1,2] for 3-node DAG";

  // Valid: partial order (only 2 of 3 nodes processed, e.g., cycle case)
  r := CheckTopoSpec([0, 2], 2, 3);
  expect r, "Valid partial topo order [0,2]";

  // Valid: empty order (all nodes in cycles)
  r := CheckTopoSpec([], 0, 3);
  expect r, "Empty order is valid (count=0)";

  // Valid: single node
  r := CheckTopoSpec([0], 1, 1);
  expect r, "Single node topo order";

  // Valid: count = n
  r := CheckTopoSpec([2, 0, 1, 3], 4, 4);
  expect r, "All 4 nodes in order";

  // Invalid: duplicate elements
  r := CheckTopoSpec([0, 0, 1], 3, 3);
  expect !r, "Duplicate elements should fail";

  // Invalid: element out of range
  r := CheckTopoSpec([0, 3, 1], 3, 3);
  expect !r, "Element 3 out of range [0,3) should fail";

  // Invalid: negative element
  r := CheckTopoSpec([-1, 0, 1], 3, 3);
  expect !r, "Negative element should fail";

  // Invalid: count != |order|
  r := CheckTopoSpec([0, 1], 3, 3);
  expect !r, "count != |order| should fail";

  // Invalid: count > n
  r := CheckTopoSpec([0, 1, 2, 3], 4, 3);
  expect !r, "count > n should fail";

  print "All spec tests passed\n";
}
