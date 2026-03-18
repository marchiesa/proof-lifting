method Ropewalkers(a: int, b: int, c: int, d: int) returns (result: int)
{
  var x := a;
  var y := b;
  var z := c;

  if x > y {
    var tmp := x;
    x := y;
    y := tmp;
  }
  if y > z {
    var tmp := y;
    y := z;
    z := tmp;
  }
  if x > y {
    var tmp := x;
    x := y;
    y := tmp;
  }

  var val1 := d - (y - x);
  var val2 := d - (z - y);
  if val1 < 0 { val1 := 0; }
  if val2 < 0 { val2 := 0; }

  result := val1 + val2;
}

method Main()
{
  var r: int;

  r := Ropewalkers(5, 2, 6, 3);
  expect r == 2, "Test 1 failed";

  r := Ropewalkers(3, 1, 5, 6);
  expect r == 8, "Test 2 failed";

  r := Ropewalkers(8, 3, 3, 2);
  expect r == 2, "Test 3 failed";

  r := Ropewalkers(2, 3, 10, 4);
  expect r == 3, "Test 4 failed";

  r := Ropewalkers(1000000000, 1000000000, 1000000000, 1000000000);
  expect r == 2000000000, "Test 5 failed";

  r := Ropewalkers(500000000, 250000000, 750000000, 1000000000);
  expect r == 1500000000, "Test 6 failed";

  r := Ropewalkers(1, 3, 2, 5);
  expect r == 8, "Test 7 failed";

  r := Ropewalkers(2, 3, 1, 6);
  expect r == 10, "Test 8 failed";

  r := Ropewalkers(9, 6, 2, 5);
  expect r == 3, "Test 9 failed";

  r := Ropewalkers(1, 1, 1, 1);
  expect r == 2, "Test 10 failed";

  r := Ropewalkers(1, 1, 500, 10);
  expect r == 10, "Test 11 failed";

  r := Ropewalkers(500, 1, 500, 1000);
  expect r == 1501, "Test 12 failed";

  r := Ropewalkers(1, 2, 1, 1);
  expect r == 1, "Test 13 failed";

  r := Ropewalkers(89, 983, 751, 1000);
  expect r == 1106, "Test 14 failed";

  r := Ropewalkers(716270982, 22102638, 553198855, 1000000000);
  expect r == 1305831656, "Test 15 failed";

  r := Ropewalkers(1000000000, 1, 1000000000, 999999999);
  expect r == 999999999, "Test 16 failed";

  r := Ropewalkers(999999999, 1, 1, 1000000000);
  expect r == 1000000002, "Test 17 failed";

  r := Ropewalkers(1, 2, 3, 4);
  expect r == 6, "Test 18 failed";

  r := Ropewalkers(1, 3, 4, 5);
  expect r == 7, "Test 19 failed";

  r := Ropewalkers(1, 3, 2, 6);
  expect r == 10, "Test 20 failed";

  print "All tests passed\n";
}