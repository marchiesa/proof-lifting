// Minimum Window Containing All Target Elements -- Runtime spec tests

function CountInRange(a: seq<int>, val: int, lo: int, hi: int): nat
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else (if a[lo] == val then 1 else 0) + CountInRange(a, val, lo + 1, hi)
}

predicate ContainsEnough(a: seq<int>, val: int, lo: int, hi: int, need: nat)
  requires 0 <= lo <= hi <= |a|
{
  CountInRange(a, val, lo, hi) >= need
}

method Main() {
  // CountInRange tests
  var a := [1, 2, 1, 2, 1];
  expect CountInRange(a, 1, 0, 5) == 3, "three 1s in full range";
  expect CountInRange(a, 1, 0, 3) == 2, "two 1s in [0..3)";
  expect CountInRange(a, 1, 0, 1) == 1, "one 1 in [0..1)";
  expect CountInRange(a, 1, 1, 2) == 0, "no 1s in [1..2)";
  expect CountInRange(a, 2, 0, 5) == 2, "two 2s in full range";
  expect CountInRange(a, 3, 0, 5) == 0, "no 3s anywhere";

  // ContainsEnough positive
  expect ContainsEnough(a, 1, 0, 5, 2), "at least 2 ones in full range";
  expect ContainsEnough(a, 1, 0, 5, 3), "at least 3 ones in full range";
  expect ContainsEnough(a, 1, 0, 3, 2), "at least 2 ones in [0..3)";

  // ContainsEnough negative
  expect !ContainsEnough(a, 1, 0, 5, 4), "not 4 ones in range";
  expect !ContainsEnough(a, 1, 0, 1, 2), "not 2 ones in [0..1)";
  expect !ContainsEnough(a, 3, 0, 5, 1), "not 1 three in range";

  // Wrong answer
  expect CountInRange(a, 1, 0, 5) != 2, "count of 1s is not 2";

  print "All spec tests passed\n";
}
