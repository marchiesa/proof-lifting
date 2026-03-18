method VasyaAndChocolate(t: int, cases: seq<(int, int, int, int)>) returns (results: seq<int>)
{
  results := [];
  var i := 0;
  while i < t
  {
    var (s, a, b, c) := cases[i];
    var n := s / c;
    var x := n / a;
    var ans := n + x * b;
    results := results + [ans];
    i := i + 1;
  }
}

method Main()
{
  // Test 1
  var r1 := VasyaAndChocolate(2, [(10, 3, 1, 1), (1000000000, 1, 1000000000, 1)]);
  expect |r1| == 2;
  expect r1[0] == 13;
  expect r1[1] == 1000000001000000000;

  // Test 2
  var r2 := VasyaAndChocolate(1, [(19260817, 1, 1, 1)]);
  expect |r2| == 1;
  expect r2[0] == 38521634;

  // Test 3
  var r3 := VasyaAndChocolate(16, [
    (1, 1, 1, 1),
    (1, 1, 1, 1000000000),
    (1, 1, 1000000000, 1),
    (1, 1, 1000000000, 1000000000),
    (1, 1000000000, 1, 1),
    (1, 1000000000, 1, 1000000000),
    (1, 1000000000, 1000000000, 1),
    (1, 1000000000, 1000000000, 1000000000),
    (1000000000, 1, 1, 1),
    (1000000000, 1, 1, 1000000000),
    (1000000000, 1, 1000000000, 1),
    (1000000000, 1, 1000000000, 1000000000),
    (1000000000, 1000000000, 1, 1),
    (1000000000, 1000000000, 1, 1000000000),
    (1000000000, 1000000000, 1000000000, 1),
    (1000000000, 1000000000, 1000000000, 1000000000)
  ]);
  expect |r3| == 16;
  expect r3[0] == 2;
  expect r3[1] == 0;
  expect r3[2] == 1000000001;
  expect r3[3] == 0;
  expect r3[4] == 1;
  expect r3[5] == 0;
  expect r3[6] == 1;
  expect r3[7] == 0;
  expect r3[8] == 2000000000;
  expect r3[9] == 2;
  expect r3[10] == 1000000001000000000;
  expect r3[11] == 1000000001;
  expect r3[12] == 1000000001;
  expect r3[13] == 1;
  expect r3[14] == 2000000000;
  expect r3[15] == 1;

  // Test 4
  var r4 := VasyaAndChocolate(1, [(19260818, 1, 1, 1)]);
  expect |r4| == 1;
  expect r4[0] == 38521636;

  // Test 5
  var r5 := VasyaAndChocolate(1, [(1, 19260817, 1, 1)]);
  expect |r5| == 1;
  expect r5[0] == 1;

  print "All tests passed\n";
}