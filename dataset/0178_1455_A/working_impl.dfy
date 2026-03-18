method StrangeFunctions(n: seq<int>) returns (result: int)
{
  result := |n|;
}

method Repeat(d: int, count: int) returns (s: seq<int>)
{
  s := [];
  var i := 0;
  while i < count {
    s := s + [d];
    i := i + 1;
  }
}

method StringToDigits(str: string) returns (s: seq<int>)
{
  s := [];
  var i := 0;
  while i < |str| {
    s := s + [str[i] as int - '0' as int];
    i := i + 1;
  }
}

method Main()
{
  var r: int;
  var n: seq<int>;

  // Test 1
  r := StrangeFunctions([4]);
  expect r == 1, "Test 1.1";
  r := StrangeFunctions([3, 7]);
  expect r == 2, "Test 1.2";
  r := StrangeFunctions([9, 9, 8, 2, 4, 4, 3, 5, 3]);
  expect r == 9, "Test 1.3";
  r := StrangeFunctions([1, 0, 0, 0, 0, 0, 0, 0, 0, 7]);
  expect r == 10, "Test 1.4";
  r := StrangeFunctions([1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 3, 3, 7, 4, 2, 6, 9, 6, 6, 6, 3, 1, 4, 1, 5]);
  expect r == 26, "Test 1.5";

  // Test 2
  r := StrangeFunctions([1, 0]);
  expect r == 2, "Test 2";

  // Test 3: 59 nines
  n := Repeat(9, 59);
  r := StrangeFunctions(n);
  expect r == 59, "Test 3";

  // Test 4
  r := StrangeFunctions([1, 0, 0, 0]);
  expect r == 4, "Test 4";

  // Test 5
  r := StrangeFunctions([5, 4, 3, 2]);
  expect r == 4, "Test 5.1";
  r := StrangeFunctions([5, 3, 4, 2]);
  expect r == 4, "Test 5.2";
  r := StrangeFunctions([2, 4, 3]);
  expect r == 3, "Test 5.3";

  // Test 6
  r := StrangeFunctions([1]);
  expect r == 1, "Test 6";

  // Test 7
  r := StrangeFunctions([1, 0]);
  expect r == 2, "Test 7.1";
  r := StrangeFunctions([1, 0, 0]);
  expect r == 3, "Test 7.2";

  // Test 8: 94 nines
  n := Repeat(9, 94);
  r := StrangeFunctions(n);
  expect r == 94, "Test 8";

  // Test 9
  r := StrangeFunctions([1, 2]);
  expect r == 2, "Test 9.1";
  r := StrangeFunctions([1, 2]);
  expect r == 2, "Test 9.2";
  r := StrangeFunctions([1, 3]);
  expect r == 2, "Test 9.3";
  r := StrangeFunctions([1, 4]);
  expect r == 2, "Test 9.4";
  r := StrangeFunctions([1, 5]);
  expect r == 2, "Test 9.5";
  r := StrangeFunctions([1, 6]);
  expect r == 2, "Test 9.6";
  r := StrangeFunctions([1, 7]);
  expect r == 2, "Test 9.7";
  r := StrangeFunctions([1, 8]);
  expect r == 2, "Test 9.8";
  r := StrangeFunctions([1, 9]);
  expect r == 2, "Test 9.9";

  // Test 10
  r := StrangeFunctions([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
  expect r == 10, "Test 10";

  // Test 11: 99 cases of [1] -> 1
  var i := 0;
  while i < 99 {
    r := StrangeFunctions([1]);
    expect r == 1, "Test 11";
    i := i + 1;
  }

  // Test 12
  r := StrangeFunctions([1, 1]);
  expect r == 2, "Test 12";

  // Test 13: 10^99 (100 digits)
  n := Repeat(0, 99);
  n := [1] + n;
  r := StrangeFunctions(n);
  expect r == 100, "Test 13";

  // Test 14: 100 nines
  n := Repeat(9, 100);
  r := StrangeFunctions(n);
  expect r == 100, "Test 14";

  // Test 15
  r := StrangeFunctions([1, 0, 0]);
  expect r == 3, "Test 15";

  // Test 16
  n := Repeat(0, 99);
  n := [1] + n;
  r := StrangeFunctions(n);
  expect r == 100, "Test 16.1";
  n := Repeat(9, 99);
  r := StrangeFunctions(n);
  expect r == 99, "Test 16.2";

  // Test 17
  n := Repeat(9, 94);
  r := StrangeFunctions(n);
  expect r == 94, "Test 17.1";

  n := StringToDigits("18888888888888888888888888800000000000000000000000000009999999990000000000000000094494990400000");
  r := StrangeFunctions(n);
  expect r == 95, "Test 17.2";

  n := Repeat(0, 98);
  n := [1] + n;
  r := StrangeFunctions(n);
  expect r == 99, "Test 17.3";

  n := Repeat(9, 99);
  r := StrangeFunctions(n);
  expect r == 99, "Test 17.4";

  n := StringToDigits("1234567899876543210");
  var t := Repeat(0, 54);
  n := n + t;
  r := StrangeFunctions(n);
  expect r == 73, "Test 17.5";

  // Test 18
  r := StrangeFunctions([1, 1]);
  expect r == 2, "Test 18.1";
  r := StrangeFunctions([1, 1, 1]);
  expect r == 3, "Test 18.2";

  // Test 19
  r := StrangeFunctions([8, 6, 2, 7]);
  expect r == 4, "Test 19";

  // Test 20: 99 nines
  n := Repeat(9, 99);
  r := StrangeFunctions(n);
  expect r == 99, "Test 20";

  print "All tests passed\n";
}