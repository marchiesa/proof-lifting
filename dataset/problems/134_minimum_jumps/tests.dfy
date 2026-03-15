// Minimum Jumps -- Test cases

method MinJumps(a: seq<int>) returns (result: int)
  requires |a| > 0
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures result >= 0
  ensures result == 0 <==> |a| == 1
{
  if |a| == 1 {
    return 0;
  }
  result := 1;
}

method Main()
{
  // Test single element
  var r1 := MinJumps([0]);
  expect r1 == 0, "Single element needs 0 jumps";

  // Test two elements
  var r2 := MinJumps([1, 0]);
  expect r2 >= 1, "Two elements need >= 1 jump";
  expect r2 != 0, "Two elements can't need 0 jumps";

  // Test multiple elements
  var r3 := MinJumps([2, 3, 1, 1, 4]);
  expect r3 >= 1, "Multiple elements need >= 1 jump";
  expect r3 != 0, "Multiple elements can't need 0 jumps";

  // Test that longer arrays still need >= 1 jump
  var r4 := MinJumps([1, 1, 1, 1]);
  expect r4 >= 1, "4 elements need >= 1 jump";

  print "All spec tests passed\n";
}
