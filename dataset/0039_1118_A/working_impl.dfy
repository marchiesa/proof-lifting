method WaterBuying(queries: seq<(int, int, int)>) returns (results: seq<int>)
{
  results := [];
  var i := 0;
  while i < |queries|
  {
    var (n, a, b) := queries[i];
    var two := 2 * a;
    var m := if two < b then two else b;
    var ans := (n / 2) * m + (n % 2) * a;
    results := results + [ans];
    i := i + 1;
  }
}

method Main()
{
  // Test 1: 4 queries
  var r1 := WaterBuying([(10, 1, 3), (7, 3, 2), (1, 1000, 1), (1000000000000, 42, 88)]);
  expect |r1| == 4;
  expect r1[0] == 10, "Test 1a failed";
  expect r1[1] == 9, "Test 1b failed";
  expect r1[2] == 1000, "Test 1c failed";
  expect r1[3] == 42000000000000, "Test 1d failed";

  // Test 2
  var r2 := WaterBuying([(25, 4, 8)]);
  expect |r2| == 1;
  expect r2[0] == 100, "Test 2 failed";

  // Test 3
  var r3 := WaterBuying([(26, 5, 9)]);
  expect |r3| == 1;
  expect r3[0] == 117, "Test 3 failed";

  // Test 4
  var r4 := WaterBuying([(27, 4, 9)]);
  expect |r4| == 1;
  expect r4[0] == 108, "Test 4 failed";

  // Test 5
  var r5 := WaterBuying([(28, 23, 53)]);
  expect |r5| == 1;
  expect r5[0] == 644, "Test 5 failed";

  // Test 6
  var r6 := WaterBuying([(29, 5, 8)]);
  expect |r6| == 1;
  expect r6[0] == 117, "Test 6 failed";

  // Test 7
  var r7 := WaterBuying([(30, 1, 3)]);
  expect |r7| == 1;
  expect r7[0] == 30, "Test 7 failed";

  // Test 8
  var r8 := WaterBuying([(31, 1, 6)]);
  expect |r8| == 1;
  expect r8[0] == 31, "Test 8 failed";

  // Test 9
  var r9 := WaterBuying([(32, 4, 7)]);
  expect |r9| == 1;
  expect r9[0] == 112, "Test 9 failed";

  // Test 10
  var r10 := WaterBuying([(33, 1, 56)]);
  expect |r10| == 1;
  expect r10[0] == 33, "Test 10 failed";

  // Test 11
  var r11 := WaterBuying([(34, 1, 2)]);
  expect |r11| == 1;
  expect r11[0] == 34, "Test 11 failed";

  // Test 12
  var r12 := WaterBuying([(36, 1, 2)]);
  expect |r12| == 1;
  expect r12[0] == 36, "Test 12 failed";

  // Test 13
  var r13 := WaterBuying([(35, 1, 2)]);
  expect |r13| == 1;
  expect r13[0] == 35, "Test 13 failed";

  // Test 14
  var r14 := WaterBuying([(39, 1, 2)]);
  expect |r14| == 1;
  expect r14[0] == 39, "Test 14 failed";

  // Test 15
  var r15 := WaterBuying([(40, 2, 4)]);
  expect |r15| == 1;
  expect r15[0] == 80, "Test 15 failed";

  // Test 16
  var r16 := WaterBuying([(45, 6, 7)]);
  expect |r16| == 1;
  expect r16[0] == 160, "Test 16 failed";

  // Test 17
  var r17 := WaterBuying([(86, 7, 90)]);
  expect |r17| == 1;
  expect r17[0] == 602, "Test 17 failed";

  print "All tests passed\n";
}