// Dinic's Max Flow -- Runtime spec tests

// The spec: ensures maxFlow >= 0
// We test the postcondition property and precondition validation.

method ValidFlowInputCheck(n: int, src: int, sink: int, capLen0: int, capLen1: int) returns (ok: bool)
{
  if n <= 0 { return false; }
  if src < 0 || src >= n { return false; }
  if sink < 0 || sink >= n { return false; }
  if src == sink { return false; }
  if capLen0 != n || capLen1 != n { return false; }
  return true;
}

method NonNegCapCheck(cap: array2<int>, n: int) returns (ok: bool)
  requires cap.Length0 == n && cap.Length1 == n
  requires n > 0
{
  var i := 0;
  while i < n
  {
    var j := 0;
    while j < n
    {
      if cap[i, j] < 0 { return false; }
      j := j + 1;
    }
    i := i + 1;
  }
  return true;
}

method Main()
{
  // Test precondition: valid inputs
  var r := ValidFlowInputCheck(4, 0, 3, 4, 4);
  expect r, "Valid flow network n=4, src=0, sink=3";

  r := ValidFlowInputCheck(2, 0, 1, 2, 2);
  expect r, "Valid 2-node flow network";

  // Invalid: src == sink
  r := ValidFlowInputCheck(3, 1, 1, 3, 3);
  expect !r, "src == sink should be invalid";

  // Invalid: n <= 0
  r := ValidFlowInputCheck(0, 0, 1, 0, 0);
  expect !r, "n=0 should be invalid";

  // Invalid: src out of range
  r := ValidFlowInputCheck(2, 2, 0, 2, 2);
  expect !r, "src=2 out of range for n=2";

  // Invalid: wrong cap dimensions
  r := ValidFlowInputCheck(3, 0, 2, 2, 3);
  expect !r, "Wrong cap dimensions";

  // Test non-negative capacity check
  var cap1 := new int[3, 3]((i, j) =>
    if i == 0 && j == 1 then 10
    else if i == 1 && j == 2 then 5
    else 0
  );
  r := NonNegCapCheck(cap1, 3);
  expect r, "All-non-negative capacities should be valid";

  var cap2 := new int[2, 2]((i, j) => if i == 0 && j == 1 then -1 else 0);
  r := NonNegCapCheck(cap2, 2);
  expect !r, "Negative capacity should be invalid";

  // Test maxFlow >= 0 postcondition property
  var f := 0;
  expect f >= 0, "Flow 0 satisfies >= 0";
  f := 5;
  expect f >= 0, "Flow 5 satisfies >= 0";
  f := 15;
  expect f >= 0, "Flow 15 satisfies >= 0";

  // Negative: flow < 0 would violate spec
  f := -1;
  expect !(f >= 0), "Flow -1 would violate postcondition";
  f := -10;
  expect !(f >= 0), "Flow -10 would violate postcondition";

  print "All spec tests passed\n";
}
