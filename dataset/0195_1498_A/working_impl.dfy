method Gcd(a: int, b: int) returns (g: int)
  decreases *
{
  var x := a;
  var y := b;
  if x < 0 { x := -x; }
  if y < 0 { y := -y; }
  while y != 0
    decreases *
  {
    var temp := y;
    y := x % y;
    x := temp;
  }
  g := x;
}

method GcdSum(n: int) returns (x: int)
  decreases *
{
  x := n;
  while true
    decreases *
  {
    var digitSum := 0;
    var temp := x;
    if temp < 0 { temp := -temp; }
    while temp > 0
      decreases *
    {
      digitSum := digitSum + (temp % 10);
      temp := temp / 10;
    }
    var g := Gcd(digitSum, x);
    if g > 1 {
      return;
    }
    x := x + 1;
  }
}

method Main()
  decreases *
{
  // Test 1
  var r1 := GcdSum(11);
  expect r1 == 12, "GcdSum(11) failed";
  var r2 := GcdSum(31);
  expect r2 == 33, "GcdSum(31) failed";
  var r3 := GcdSum(75);
  expect r3 == 75, "GcdSum(75) failed";

  // Test 2
  var r4 := GcdSum(1);
  expect r4 == 2, "GcdSum(1) failed";

  // Test 3
  var r5 := GcdSum(50);
  expect r5 == 50, "GcdSum(50) failed";

  // Test 4
  var r6 := GcdSum(2);
  expect r6 == 2, "GcdSum(2) failed";
  var r7 := GcdSum(10);
  expect r7 == 12, "GcdSum(10) failed";
  var r8 := GcdSum(15);
  expect r8 == 15, "GcdSum(15) failed";
  var r9 := GcdSum(33);
  expect r9 == 33, "GcdSum(33) failed";
  var r10 := GcdSum(49);
  expect r10 == 50, "GcdSum(49) failed";

  // Test 5
  var r11 := GcdSum(7);
  expect r11 == 7, "GcdSum(7) failed";

  // Test 6
  var r12 := GcdSum(1);
  expect r12 == 2, "GcdSum(1) failed [test6]";
  var r13 := GcdSum(2);
  expect r13 == 2, "GcdSum(2) failed [test6]";

  // Test 7
  var r14 := GcdSum(12);
  expect r14 == 12, "GcdSum(12) failed";
  var r15 := GcdSum(24);
  expect r15 == 24, "GcdSum(24) failed";
  var r16 := GcdSum(36);
  expect r16 == 36, "GcdSum(36) failed";
  var r17 := GcdSum(48);
  expect r17 == 48, "GcdSum(48) failed";

  // Test 8
  var r18 := GcdSum(9);
  expect r18 == 9, "GcdSum(9) failed";
  var r19 := GcdSum(18);
  expect r19 == 18, "GcdSum(18) failed";
  var r20 := GcdSum(27);
  expect r20 == 27, "GcdSum(27) failed";

  // Test 9
  var r21 := GcdSum(3);
  expect r21 == 3, "GcdSum(3) failed";
  var r22 := GcdSum(5);
  expect r22 == 5, "GcdSum(5) failed";
  var r23 := GcdSum(13);
  expect r23 == 15, "GcdSum(13) failed";
  var r24 := GcdSum(20);
  expect r24 == 20, "GcdSum(20) failed";
  var r25 := GcdSum(37);
  expect r25 == 39, "GcdSum(37) failed";
  var r26 := GcdSum(45);
  expect r26 == 45, "GcdSum(45) failed";

  // Test 10
  var r27 := GcdSum(41);
  expect r27 == 42, "GcdSum(41) failed";
  var r28 := GcdSum(50);
  expect r28 == 50, "GcdSum(50) failed [test10]";

  print "All tests passed\n";
}