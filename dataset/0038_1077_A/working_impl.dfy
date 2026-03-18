method FrogJumping(queries: seq<(int, int, int)>) returns (results: seq<real>)
{
  results := [];
  var i := 0;
  while i < |queries|
  {
    var (a, b, k) := queries[i];
    var f: real := k as real / 2.0;
    var ans: real := a as real * f - b as real * f;
    if k % 2 == 1 {
      ans := ans + a as real;
    }
    results := results + [ans];
    i := i + 1;
  }
}

method Main()
{
  // Test 1: 6 queries
  var results1 := FrogJumping([(5, 2, 3), (100, 1, 4), (1, 10, 5), (1000000000, 1, 6), (1, 1, 1000000000), (1, 1, 999999999)]);
  expect |results1| == 6;
  expect results1[0] == 9.5;
  expect results1[1] == 198.0;
  expect results1[2] == -21.5;
  expect results1[3] == 2999999997.0;
  expect results1[4] == 0.0;
  expect results1[5] == 1.0;

  // Test 2
  var results2 := FrogJumping([(19280817, 1, 1)]);
  expect |results2| == 1;
  expect results2[0] == 28921225.0;

  // Test 3
  var results3 := FrogJumping([(598, 56, 799)]);
  expect |results3| == 1;
  expect results3[0] == 217127.0;

  // Test 4
  var results4 := FrogJumping([(599, 56, 799)]);
  expect |results4| == 1;
  expect results4[0] == 217527.5;

  print "All tests passed\n";
}