method GotAnyGrapes(x: int, y: int, z: int, a: int, b: int, c: int) returns (result: bool)
{
  var a' := a;
  var b' := b;
  var c' := c;

  c' := c' - z;
  if c' < 0 {
    b' := b' + c';
  }
  b' := b' - y;
  if b' < 0 {
    a' := a' + b';
  }
  a' := a' - x;

  result := a' >= 0;
}

method Main()
{
  var r: bool;

  // Test 1
  r := GotAnyGrapes(1, 6, 2, 4, 3, 3);
  expect r == true, "Test 1 failed";

  // Test 2
  r := GotAnyGrapes(5, 1, 1, 4, 3, 2);
  expect r == false, "Test 2 failed";

  // Test 3
  r := GotAnyGrapes(1, 1, 100000, 4, 2, 99995);
  expect r == false, "Test 3 failed";

  // Test 4
  r := GotAnyGrapes(1, 2, 3, 3, 2, 1);
  expect r == true, "Test 4 failed";

  // Test 5
  r := GotAnyGrapes(1, 8, 4, 3, 1, 9);
  expect r == false, "Test 5 failed";

  // Test 6
  r := GotAnyGrapes(6, 1, 2, 4, 9, 6);
  expect r == false, "Test 6 failed";

  // Test 7
  r := GotAnyGrapes(100000, 100000, 100000, 100000, 100000, 100000);
  expect r == true, "Test 7 failed";

  // Test 8
  r := GotAnyGrapes(3, 2, 1, 1, 2, 3);
  expect r == false, "Test 8 failed";

  // Test 9
  r := GotAnyGrapes(99999, 99998, 99997, 99997, 99998, 99999);
  expect r == false, "Test 9 failed";

  // Test 10
  r := GotAnyGrapes(1, 7, 9, 4, 5, 7);
  expect r == false, "Test 10 failed";

  // Test 11
  r := GotAnyGrapes(99999, 100000, 100000, 100000, 100000, 100000);
  expect r == true, "Test 11 failed";

  // Test 12
  r := GotAnyGrapes(100000, 99999, 100000, 100000, 100000, 100000);
  expect r == true, "Test 12 failed";

  // Test 13
  r := GotAnyGrapes(100000, 100000, 99999, 100000, 100000, 100000);
  expect r == true, "Test 13 failed";

  // Test 14
  r := GotAnyGrapes(100000, 100000, 100000, 99999, 100000, 100000);
  expect r == false, "Test 14 failed";

  // Test 15
  r := GotAnyGrapes(100000, 100000, 100000, 100000, 99999, 100000);
  expect r == false, "Test 15 failed";

  // Test 16
  r := GotAnyGrapes(100000, 100000, 100000, 100000, 100000, 99999);
  expect r == false, "Test 16 failed";

  // Test 17
  r := GotAnyGrapes(4, 6, 4, 4, 5, 6);
  expect r == false, "Test 17 failed";

  // Test 18
  r := GotAnyGrapes(6, 1, 9, 1, 7, 8);
  expect r == false, "Test 18 failed";

  // Test 19
  r := GotAnyGrapes(4, 10, 5, 4, 10, 5);
  expect r == true, "Test 19 failed";

  // Test 20
  r := GotAnyGrapes(10, 1, 7, 1, 9, 10);
  expect r == false, "Test 20 failed";

  print "All tests passed\n";
}