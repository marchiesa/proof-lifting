method XORwice(a: int, b: int) returns (result: int)
{
  var x := a;
  var y := b;
  if x < y {
    x := b;
    y := a;
  }
  // Compute z = x AND y (bitwise)
  var z := 0;
  var tX := x;
  var tY := y;
  var bit := 1;
  while tX > 0 || tY > 0
    decreases tX + tY
  {
    if tX % 2 == 1 && tY % 2 == 1 {
      z := z + bit;
    }
    tX := tX / 2;
    tY := tY / 2;
    bit := bit * 2;
  }
  // Compute (x ^ z) + (y ^ z)
  var axz := 0;
  tX := x;
  var tZ := z;
  bit := 1;
  while tX > 0 || tZ > 0
    decreases tX + tZ
  {
    if tX % 2 != tZ % 2 {
      axz := axz + bit;
    }
    tX := tX / 2;
    tZ := tZ / 2;
    bit := bit * 2;
  }
  var bxz := 0;
  tY := y;
  tZ := z;
  bit := 1;
  while tY > 0 || tZ > 0
    decreases tY + tZ
  {
    if tY % 2 != tZ % 2 {
      bxz := bxz + bit;
    }
    tY := tY / 2;
    tZ := tZ / 2;
    bit := bit * 2;
  }
  result := axz + bxz;
}

method Main()
{
  var r: int;

  // Test 1
  r := XORwice(6, 12);
  expect r == 10, "Failed: XORwice(6, 12)";
  r := XORwice(4, 9);
  expect r == 13, "Failed: XORwice(4, 9)";
  r := XORwice(59, 832);
  expect r == 891, "Failed: XORwice(59, 832)";
  r := XORwice(28, 14);
  expect r == 18, "Failed: XORwice(28, 14)";
  r := XORwice(4925, 2912);
  expect r == 6237, "Failed: XORwice(4925, 2912)";
  r := XORwice(1, 1);
  expect r == 0, "Failed: XORwice(1, 1)";

  // Test 2
  r := XORwice(1, 1);
  expect r == 0, "Failed: XORwice(1, 1) [test2]";

  // Test 3
  r := XORwice(2, 3);
  expect r == 1, "Failed: XORwice(2, 3)";

  // Test 4
  r := XORwice(7, 7);
  expect r == 0, "Failed: XORwice(7, 7)";

  // Test 5
  r := XORwice(10, 20);
  expect r == 30, "Failed: XORwice(10, 20)";

  // Test 6
  r := XORwice(15, 8);
  expect r == 7, "Failed: XORwice(15, 8)";

  // Test 7
  r := XORwice(3, 50);
  expect r == 49, "Failed: XORwice(3, 50)";

  // Test 8
  r := XORwice(48, 49);
  expect r == 1, "Failed: XORwice(48, 49)";

  // Test 9
  r := XORwice(25, 30);
  expect r == 7, "Failed: XORwice(25, 30)";

  // Test 10
  r := XORwice(1, 2);
  expect r == 3, "Failed: XORwice(1, 2)";
  r := XORwice(5, 5);
  expect r == 0, "Failed: XORwice(5, 5)";
  r := XORwice(12, 7);
  expect r == 11, "Failed: XORwice(12, 7)";

  // Test 11
  r := XORwice(33, 44);
  expect r == 13, "Failed: XORwice(33, 44)";
  r := XORwice(50, 50);
  expect r == 0, "Failed: XORwice(50, 50)";

  print "All tests passed\n";
}