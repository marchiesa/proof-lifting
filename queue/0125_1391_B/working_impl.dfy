method FixYou(n: int, m: int, grid: seq<seq<char>>) returns (changes: int)
{
  changes := 0;
  var lastRow := grid[n - 1];
  var j := 0;
  while j < m
  {
    if lastRow[j] == 'D' {
      changes := changes + 1;
    }
    j := j + 1;
  }
  var i := 0;
  while i < n
  {
    if grid[i][m - 1] == 'R' {
      changes := changes + 1;
    }
    i := i + 1;
  }
}

method Main()
{
  var changes: int;

  // === Test 1 ===
  changes := FixYou(3, 3, ["RRD", "DDR", "RRC"]);
  expect changes == 1, "Test 1.1 failed";

  changes := FixYou(1, 4, ["DDDC"]);
  expect changes == 3, "Test 1.2 failed";

  changes := FixYou(6, 9, ["RDDDDDRRR", "RRDDRRDDD", "RRDRDRRDR", "DDDDRDDRR", "DRRDRDDDR", "DDRDRRDDC"]);
  expect changes == 9, "Test 1.3 failed";

  changes := FixYou(1, 1, ["C"]);
  expect changes == 0, "Test 1.4 failed";

  // === Test 2 ===
  changes := FixYou(1, 2, ["RC"]);
  expect changes == 0, "Test 2.1 failed";

  changes := FixYou(1, 2, ["DC"]);
  expect changes == 1, "Test 2.2 failed";

  changes := FixYou(2, 1, ["R", "C"]);
  expect changes == 1, "Test 2.3 failed";

  changes := FixYou(2, 1, ["D", "C"]);
  expect changes == 0, "Test 2.4 failed";

  changes := FixYou(7, 6, ["DRDDRR", "RDDDRR", "DRRRDD", "RRDRRR", "DDRRRR", "RRDRDR", "DDRDRC"]);
  expect changes == 8, "Test 2.5 failed";

  changes := FixYou(8, 5, ["DRDRD", "DRRRR", "RDRRD", "DDDRR", "RDDRR", "RRDDD", "DDRRR", "DDDRC"]);
  expect changes == 7, "Test 2.6 failed";

  changes := FixYou(8, 3, ["DDD", "DDR", "DRD", "RRR", "DRR", "DRD", "RRR", "RDC"]);
  expect changes == 5, "Test 2.7 failed";

  changes := FixYou(6, 6, ["DRDDDR", "DDDRDR", "RDDRRD", "DRRRRR", "RRRRRR", "DRDRRC"]);
  expect changes == 6, "Test 2.8 failed";

  changes := FixYou(6, 8, ["RRDDDRRR", "RDRDDRRR", "DRRDRRRD", "DRDRRDRR", "DDDDDDDR", "RRDRRDDC"]);
  expect changes == 7, "Test 2.9 failed";

  changes := FixYou(7, 9, ["RDDDDRDDR", "DRRRRDRDR", "DDRRDDDRR", "DDDDDRDRR", "DDRDRDDRR", "DRRDDDDRD", "DDDDRRRDC"]);
  expect changes == 10, "Test 2.10 failed";

  // === Test 3 ===
  changes := FixYou(4, 4, ["DDDD", "DRDR", "DRDD", "DRRC"]);
  expect changes == 2, "Test 3.1 failed";

  changes := FixYou(4, 4, ["DDRR", "DDRR", "DDRD", "DRRC"]);
  expect changes == 3, "Test 3.2 failed";

  changes := FixYou(4, 4, ["RRDR", "DRRR", "RRRR", "DDRC"]);
  expect changes == 5, "Test 3.3 failed";

  changes := FixYou(4, 4, ["DRRR", "RDDD", "DDDR", "RDRC"]);
  expect changes == 3, "Test 3.4 failed";

  changes := FixYou(4, 4, ["RDDD", "RRDR", "DDRD", "DRRC"]);
  expect changes == 2, "Test 3.5 failed";

  changes := FixYou(4, 4, ["RDRR", "RDRR", "RDDR", "RDDC"]);
  expect changes == 5, "Test 3.6 failed";

  changes := FixYou(4, 4, ["DRDD", "DRRR", "DDDD", "DDRC"]);
  expect changes == 3, "Test 3.7 failed";

  changes := FixYou(4, 4, ["RDDR", "RRRD", "RRRR", "RRRC"]);
  expect changes == 2, "Test 3.8 failed";

  changes := FixYou(4, 4, ["DRRR", "RDRR", "RDDD", "RDRC"]);
  expect changes == 3, "Test 3.9 failed";

  changes := FixYou(4, 4, ["RRDR", "DRRD", "RRDR", "DDDC"]);
  expect changes == 5, "Test 3.10 failed";

  // === Test 4 ===
  changes := FixYou(1, 1, ["C"]);
  expect changes == 0, "Test 4.1 failed";

  changes := FixYou(1, 1, ["C"]);
  expect changes == 0, "Test 4.2 failed";

  changes := FixYou(1, 1, ["C"]);
  expect changes == 0, "Test 4.3 failed";

  changes := FixYou(1, 1, ["C"]);
  expect changes == 0, "Test 4.4 failed";

  changes := FixYou(1, 1, ["C"]);
  expect changes == 0, "Test 4.5 failed";

  changes := FixYou(1, 1, ["C"]);
  expect changes == 0, "Test 4.6 failed";

  changes := FixYou(1, 1, ["C"]);
  expect changes == 0, "Test 4.7 failed";

  changes := FixYou(1, 1, ["C"]);
  expect changes == 0, "Test 4.8 failed";

  changes := FixYou(1, 1, ["C"]);
  expect changes == 0, "Test 4.9 failed";

  changes := FixYou(1, 1, ["C"]);
  expect changes == 0, "Test 4.10 failed";

  // === Test 5 ===
  changes := FixYou(6, 4, ["RRRR", "RRRR", "RRRR", "RRRR", "RRRR", "RRRC"]);
  expect changes == 5, "Test 5.1 failed";

  print "All tests passed\n";
}