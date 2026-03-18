method DominoOnWindowsill(n: int, k1: int, k2: int, w: int, b: int) returns (result: bool)
{
  var r1 := n - k1;
  var r2 := n - k2;

  var diffK := k1 - k2;
  if diffK < 0 { diffK := -diffK; }

  var diffR := r1 - r2;
  if diffR < 0 { diffR := -diffR; }

  var minK := if k1 < k2 then k1 else k2;
  var minR := if r1 < r2 then r1 else r2;

  var W := minK + diffK / 2;
  var B := minR + diffR / 2;

  result := W >= w && B >= b;
}

method Main()
{
  var r: bool;

  // Test 1 (5 cases)
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "Test 1.1";
  r := DominoOnWindowsill(1, 1, 1, 0, 0);
  expect r == true, "Test 1.2";
  r := DominoOnWindowsill(3, 0, 0, 1, 3);
  expect r == false, "Test 1.3";
  r := DominoOnWindowsill(4, 3, 1, 2, 2);
  expect r == true, "Test 1.4";
  r := DominoOnWindowsill(5, 4, 3, 3, 1);
  expect r == true, "Test 1.5";

  // Test 2 (9 cases, all n=1 k1=0 k2=1 w=1 b=0 → NO)
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "Test 2.1";
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "Test 2.2";
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "Test 2.3";
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "Test 2.4";
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "Test 2.5";
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "Test 2.6";
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "Test 2.7";
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "Test 2.8";
  r := DominoOnWindowsill(1, 0, 1, 1, 0);
  expect r == false, "Test 2.9";

  // Test 3
  r := DominoOnWindowsill(5, 3, 4, 2, 1);
  expect r == true, "Test 3";

  // Test 4
  r := DominoOnWindowsill(10, 10, 10, 5, 5);
  expect r == false, "Test 4";

  // Test 5
  r := DominoOnWindowsill(1, 0, 0, 0, 0);
  expect r == true, "Test 5";

  // Test 6
  r := DominoOnWindowsill(3, 3, 3, 3, 0);
  expect r == true, "Test 6";

  // Test 7
  r := DominoOnWindowsill(6, 0, 0, 0, 6);
  expect r == true, "Test 7";

  // Test 8 (3 cases)
  r := DominoOnWindowsill(4, 2, 3, 1, 2);
  expect r == false, "Test 8.1";
  r := DominoOnWindowsill(5, 5, 5, 5, 0);
  expect r == true, "Test 8.2";
  r := DominoOnWindowsill(3, 1, 1, 0, 2);
  expect r == true, "Test 8.3";

  // Test 9
  r := DominoOnWindowsill(50, 25, 30, 10, 8);
  expect r == true, "Test 9";

  // Test 10
  r := DominoOnWindowsill(7, 7, 0, 3, 3);
  expect r == true, "Test 10";

  // Test 11 (2 cases)
  r := DominoOnWindowsill(10, 5, 5, 5, 5);
  expect r == true, "Test 11.1";
  r := DominoOnWindowsill(8, 4, 6, 2, 3);
  expect r == true, "Test 11.2";

  // Test 12
  r := DominoOnWindowsill(2, 1, 0, 0, 1);
  expect r == true, "Test 12";

  print "All tests passed\n";
}