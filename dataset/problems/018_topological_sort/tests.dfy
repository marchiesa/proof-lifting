// Topological Sort Existence (Cycle Detection) -- Runtime spec tests
// The spec is primarily in postconditions (0 <= count <= n).
// We test the helper function CountTrue which is the main spec function.

function CountTrue(s: seq<bool>): int
{
  if |s| == 0 then 0
  else (if s[0] then 1 else 0) + CountTrue(s[1..])
}

method Main()
{
  // Test CountTrue
  expect CountTrue([]) == 0, "empty has 0 trues";
  expect CountTrue([true]) == 1, "single true";
  expect CountTrue([false]) == 0, "single false";
  expect CountTrue([true, true, true]) == 3, "all true";
  expect CountTrue([false, false, false]) == 0, "all false";
  expect CountTrue([true, false, true]) == 2, "mixed: 2 trues";
  expect CountTrue([false, true, false, true, false]) == 2, "alternating: 2 trues";
  expect CountTrue([true, true, false, false, true]) == 3, "3 trues";

  // Test bounds: 0 <= CountTrue(s) <= |s|
  var s := [true, false, true, true, false];
  expect 0 <= CountTrue(s), "CountTrue >= 0";
  expect CountTrue(s) <= |s|, "CountTrue <= |s|";
  expect CountTrue(s) == 3, "CountTrue of mixed is 3";

  // Test that all false gives 0
  expect CountTrue([false, false, false, false]) == 0, "all false gives 0";

  // Test that all true gives length
  expect CountTrue([true, true, true, true]) == 4, "all true gives length";

  print "All spec tests passed\n";
}
