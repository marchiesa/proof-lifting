method Min2(x: int, y: int) returns (m: int)
{
  if x < y { m := x; } else { m := y; }
}

method Min3(x: int, y: int, z: int) returns (m: int)
{
  m := x;
  if y < m { m := y; }
  if z < m { m := z; }
}

method Suits(a: int, b: int, c: int, d: int, e: int, f: int) returns (maxCost: int)
{
  if e > f {
    var x := Min2(a, d);
    var newD := d - x;
    var m := Min3(b, c, newD);
    maxCost := x * e + m * f;
  } else {
    var x := Min3(b, c, d);
    var newD := d - x;
    var m := Min2(a, newD);
    maxCost := x * f + m * e;
  }
}

method Main()
{
  var result: int;

  result := Suits(4, 5, 6, 3, 1, 2);
  expect result == 6, "Test 1 failed";

  result := Suits(12, 11, 13, 20, 4, 6);
  expect result == 102, "Test 2 failed";

  result := Suits(17, 14, 5, 21, 15, 17);
  expect result == 325, "Test 3 failed";

  result := Suits(43475, 48103, 50473, 97918, 991, 974);
  expect result == 89936047, "Test 4 failed";

  result := Suits(35361, 35182, 68078, 30077, 870, 907);
  expect result == 27279839, "Test 5 failed";

  result := Suits(84205, 15736, 30259, 79331, 647, 378);
  expect result == 51327157, "Test 6 failed";

  result := Suits(220, 623, 94, 463, 28, 656);
  expect result == 67824, "Test 7 failed";

  result := Suits(100000, 100000, 100000, 100000, 1000, 1);
  expect result == 100000000, "Test 8 failed";

  result := Suits(22606, 4759, 37264, 19105, 787, 237);
  expect result == 15035635, "Test 9 failed";

  result := Suits(630, 312, 279, 823, 316, 915);
  expect result == 427189, "Test 10 failed";

  result := Suits(86516, 30436, 14408, 80824, 605, 220);
  expect result == 48898520, "Test 11 failed";

  result := Suits(1, 1, 1, 2, 100, 200);
  expect result == 300, "Test 12 failed";

  result := Suits(406, 847, 512, 65, 86, 990);
  expect result == 64350, "Test 13 failed";

  result := Suits(250, 400, 766, 246, 863, 166);
  expect result == 212298, "Test 14 failed";

  result := Suits(724, 20, 391, 850, 639, 149);
  expect result == 465616, "Test 15 failed";

  result := Suits(30233, 27784, 36393, 81065, 782, 953);
  expect result == 50120358, "Test 16 failed";

  result := Suits(61455, 43924, 94322, 83903, 855, 232);
  expect result == 57751961, "Test 17 failed";

  result := Suits(68576, 46084, 31772, 10708, 632, 408);
  expect result == 6767456, "Test 18 failed";

  result := Suits(19969, 99297, 44283, 67490, 71, 20);
  expect result == 2303459, "Test 19 failed";

  result := Suits(68814, 96071, 14437, 59848, 848, 195);
  expect result == 50751104, "Test 20 failed";

  print "All tests passed\n";
}