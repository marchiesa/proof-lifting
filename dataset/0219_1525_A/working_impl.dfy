method Gcd(a: int, b: int) returns (r: int)
  requires a > 0 && b > 0
{
  var x := a;
  var y := b;
  while y != 0
  {
    var tmp := y;
    y := x % y;
    x := tmp;
  }
  r := x;
}

method PotionMaking(k: int) returns (steps: int)
{
  var g := Gcd(k, 100);
  steps := 100 / g;
}

method Main()
{
  var r: int;

  // Test 1
  r := PotionMaking(3);
  expect r == 100, "Test 1: k=3";
  r := PotionMaking(100);
  expect r == 1, "Test 1: k=100";
  r := PotionMaking(25);
  expect r == 4, "Test 1: k=25";

  // Test 2 (100 cases)
  var t2inputs: seq<int> := [
    2, 36, 43, 19, 99, 100, 98, 9, 79, 57,
    1, 78, 56, 14, 66, 93, 62, 50, 76, 33,
    25, 41, 15, 61, 97, 68, 51, 91, 95, 96,
    83, 53, 12, 77, 75, 85, 37, 72, 82, 70,
    44, 69, 58, 52, 48, 73, 21, 24, 20, 8,
    31, 32, 45, 55, 29, 13, 28, 49, 60, 54,
    90, 86, 94, 10, 71, 47, 40, 74, 80, 23,
    26, 84, 38, 89, 4, 39, 6, 22, 92, 46,
    88, 67, 35, 18, 34, 5, 59, 81, 64, 17,
    3, 42, 65, 87, 11, 27, 7, 30, 16, 63
  ];
  var t2expected: seq<int> := [
    50, 25, 100, 100, 100, 1, 50, 100, 100, 100,
    100, 50, 25, 50, 50, 100, 50, 2, 25, 100,
    4, 100, 20, 100, 100, 25, 100, 100, 20, 25,
    100, 100, 25, 100, 4, 20, 100, 25, 50, 10,
    25, 100, 50, 25, 25, 100, 100, 25, 5, 25,
    100, 25, 20, 20, 100, 100, 25, 100, 5, 50,
    10, 50, 50, 10, 100, 100, 5, 50, 5, 100,
    50, 25, 50, 100, 25, 100, 50, 50, 25, 50,
    25, 100, 20, 50, 50, 20, 100, 100, 25, 100,
    100, 50, 20, 100, 100, 100, 100, 10, 25, 100
  ];
  var i := 0;
  while i < |t2inputs| {
    r := PotionMaking(t2inputs[i]);
    expect r == t2expected[i], "Test 2 failed";
    i := i + 1;
  }

  // Test 3 (100 cases: alternating k=7 and k=3, all expect 100)
  i := 0;
  while i < 50 {
    r := PotionMaking(7);
    expect r == 100, "Test 3: k=7";
    r := PotionMaking(3);
    expect r == 100, "Test 3: k=3";
    i := i + 1;
  }

  // Test 4
  r := PotionMaking(1);
  expect r == 100, "Test 4: k=1";

  // Test 5
  r := PotionMaking(50);
  expect r == 2, "Test 5: k=50";

  // Test 6
  r := PotionMaking(100);
  expect r == 1, "Test 6: k=100";

  // Test 7
  r := PotionMaking(1);
  expect r == 100, "Test 7: k=1";
  r := PotionMaking(2);
  expect r == 50, "Test 7: k=2";
  r := PotionMaking(3);
  expect r == 100, "Test 7: k=3";
  r := PotionMaking(4);
  expect r == 25, "Test 7: k=4";
  r := PotionMaking(5);
  expect r == 20, "Test 7: k=5";

  // Test 8
  r := PotionMaking(10);
  expect r == 10, "Test 8: k=10";
  r := PotionMaking(20);
  expect r == 5, "Test 8: k=20";
  r := PotionMaking(30);
  expect r == 10, "Test 8: k=30";

  // Test 9
  r := PotionMaking(25);
  expect r == 4, "Test 9: k=25";
  r := PotionMaking(50);
  expect r == 2, "Test 9: k=50";
  r := PotionMaking(75);
  expect r == 4, "Test 9: k=75";
  r := PotionMaking(100);
  expect r == 1, "Test 9: k=100";

  // Test 10
  r := PotionMaking(1);
  expect r == 100, "Test 10: k=1";
  r := PotionMaking(33);
  expect r == 100, "Test 10: k=33";
  r := PotionMaking(50);
  expect r == 2, "Test 10: k=50";
  r := PotionMaking(67);
  expect r == 100, "Test 10: k=67";
  r := PotionMaking(99);
  expect r == 100, "Test 10: k=99";
  r := PotionMaking(100);
  expect r == 1, "Test 10: k=100";

  // Test 11
  r := PotionMaking(7);
  expect r == 100, "Test 11: k=7";
  r := PotionMaking(13);
  expect r == 100, "Test 11: k=13";

  // Test 12
  r := PotionMaking(1);
  expect r == 100, "Test 12: k=1";
  r := PotionMaking(10);
  expect r == 10, "Test 12: k=10";
  r := PotionMaking(20);
  expect r == 5, "Test 12: k=20";
  r := PotionMaking(25);
  expect r == 4, "Test 12: k=25";
  r := PotionMaking(33);
  expect r == 100, "Test 12: k=33";
  r := PotionMaking(50);
  expect r == 2, "Test 12: k=50";
  r := PotionMaking(67);
  expect r == 100, "Test 12: k=67";
  r := PotionMaking(75);
  expect r == 4, "Test 12: k=75";
  r := PotionMaking(90);
  expect r == 10, "Test 12: k=90";
  r := PotionMaking(100);
  expect r == 1, "Test 12: k=100";

  // Test 13
  r := PotionMaking(44);
  expect r == 25, "Test 13: k=44";
  r := PotionMaking(55);
  expect r == 20, "Test 13: k=55";
  r := PotionMaking(66);
  expect r == 50, "Test 13: k=66";

  print "All tests passed\n";
}