method AndThenThereWereK(n: int) returns (k: int)
{
  var p := 1;
  while p * 2 <= n
    decreases n - p
  {
    p := p * 2;
  }
  k := p - 1;
}

method Main()
{
  // Test 1 inputs
  var r := AndThenThereWereK(2);
  expect r == 1, "Failed: AndThenThereWereK(2)";

  r := AndThenThereWereK(5);
  expect r == 3, "Failed: AndThenThereWereK(5)";

  r := AndThenThereWereK(17);
  expect r == 15, "Failed: AndThenThereWereK(17)";

  // Test 2
  r := AndThenThereWereK(99888383);
  expect r == 67108863, "Failed: AndThenThereWereK(99888383)";

  // Test 3
  r := AndThenThereWereK(1);
  expect r == 0, "Failed: AndThenThereWereK(1)";

  // Test 4
  r := AndThenThereWereK(2);
  expect r == 1, "Failed: AndThenThereWereK(2) [test4]";

  // Test 5
  r := AndThenThereWereK(3);
  expect r == 1, "Failed: AndThenThereWereK(3)";

  // Test 6
  r := AndThenThereWereK(7);
  expect r == 3, "Failed: AndThenThereWereK(7)";

  // Test 7
  r := AndThenThereWereK(10);
  expect r == 7, "Failed: AndThenThereWereK(10)";

  // Test 8
  r := AndThenThereWereK(16);
  expect r == 15, "Failed: AndThenThereWereK(16)";

  // Test 9
  r := AndThenThereWereK(32);
  expect r == 31, "Failed: AndThenThereWereK(32)";

  // Test 10
  r := AndThenThereWereK(50);
  expect r == 31, "Failed: AndThenThereWereK(50)";

  // Test 11
  r := AndThenThereWereK(48);
  expect r == 31, "Failed: AndThenThereWereK(48)";

  // Test 12 (covers 1, 2, 5, 17, 50 — already tested above, included for completeness)
  r := AndThenThereWereK(1);
  expect r == 0, "Failed: AndThenThereWereK(1) [test12]";

  r := AndThenThereWereK(2);
  expect r == 1, "Failed: AndThenThereWereK(2) [test12]";

  r := AndThenThereWereK(5);
  expect r == 3, "Failed: AndThenThereWereK(5) [test12]";

  r := AndThenThereWereK(17);
  expect r == 15, "Failed: AndThenThereWereK(17) [test12]";

  r := AndThenThereWereK(50);
  expect r == 31, "Failed: AndThenThereWereK(50) [test12]";

  print "All tests passed\n";
}