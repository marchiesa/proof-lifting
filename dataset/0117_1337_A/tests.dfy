predicate IsTriangle(x: int, y: int, z: int)
{
  x + y > z && x + z > y && y + z > x
}

predicate InRange(x: int, y: int, z: int, a: int, b: int, c: int, d: int)
{
  a <= x <= b && b <= y <= c && c <= z <= d
}

predicate IsValidSolution(x: int, y: int, z: int, a: int, b: int, c: int, d: int)
{
  InRange(x, y, z, a, b, c, d) && IsTriangle(x, y, z)
}

method IchihimeAndTriangle(a: int, b: int, c: int, d: int) returns (x: int, y: int, z: int)
  requires 1 <= a <= b <= c <= d
  ensures IsValidSolution(x, y, z, a, b, c, d)
{
  x := b;
  y := c;
  z := c;
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // IsValidSolution(correct_x, correct_y, correct_z, a, b, c, d) should hold
  expect IsValidSolution(3, 5, 5, 1, 3, 5, 7), "spec positive 1a";
  expect IsValidSolution(5, 5, 5, 1, 5, 5, 7), "spec positive 1b";
  expect IsValidSolution(200000, 300000, 300000, 100000, 200000, 300000, 400000), "spec positive 1c";
  expect IsValidSolution(1, 977539810, 977539810, 1, 1, 977539810, 977539810), "spec positive 1d";
  expect IsValidSolution(1, 1, 1, 1, 1, 1, 1), "spec positive 2";
  expect IsValidSolution(38166, 39580, 39580, 31796, 38166, 39580, 43622), "spec positive 3a";
  expect IsValidSolution(27223, 58836, 58836, 3002, 27223, 58836, 70214), "spec positive 3b";
  expect IsValidSolution(74454, 78650, 78650, 13832, 74454, 78650, 89847), "spec positive 3c";
  expect IsValidSolution(2374454, 8591131, 8591131, 2374453, 2374454, 8591131, 23094546), "spec positive 4a";
  expect IsValidSolution(5813292, 9709163, 9709163, 5813291, 5813292, 9709163, 35032815), "spec positive 4b";
  expect IsValidSolution(23049698, 23049701, 23049701, 4280399, 23049698, 23049701, 34728360), "spec positive 4c";
  expect IsValidSolution(18688462, 22400847, 22400847, 15184184, 18688462, 22400847, 22400849), "spec positive 4d";
  expect IsValidSolution(31462070, 33936330, 33936330, 24397371, 31462070, 33936330, 33936331), "spec positive 4e";
  expect IsValidSolution(28241116, 38909200, 38909200, 21376685, 28241116, 38909200, 38909202), "spec positive 4f";
  expect IsValidSolution(31628480, 31628482, 31628482, 29491847, 31628480, 31628482, 45225214), "spec positive 4g";
  expect IsValidSolution(15414479, 36902879, 36902879, 15144763, 15414479, 36902879, 36902881), "spec positive 4h";
  expect IsValidSolution(38889986, 47732180, 47732180, 36023581, 38889986, 47732180, 47732180), "spec positive 4i";
  expect IsValidSolution(34770550, 48893932, 48893932, 31679295, 34770550, 48893932, 48893932), "spec positive 4j";
  expect IsValidSolution(5191258, 35923383, 35923383, 5191255, 5191258, 35923383, 42585840), "spec positive 4k";
  expect IsValidSolution(28569071, 40043177, 40043177, 12751172, 28569071, 40043177, 40043177), "spec positive 4l";
  expect IsValidSolution(7647580, 40143919, 40143919, 7647578, 7647580, 40143919, 41874647), "spec positive 4m";
  expect IsValidSolution(11404618, 25570153, 25570153, 11404615, 11404618, 25570153, 47200967), "spec positive 4n";
  expect IsValidSolution(9, 10, 10, 8, 9, 10, 11), "spec positive 5";
  expect IsValidSolution(1, 3, 3, 1, 1, 3, 100), "spec positive 6";
  expect IsValidSolution(1, 2, 2, 1, 1, 2, 3), "spec positive 7";
  expect IsValidSolution(211341211, 211341211, 211341211, 933009, 211341211, 211341211, 211341211), "spec positive 8";
  expect IsValidSolution(2, 3, 3, 1, 2, 3, 5), "spec positive 9";
  expect IsValidSolution(2, 4, 4, 1, 2, 4, 5), "spec positive 10";

  // ===== SPEC NEGATIVE TESTS =====
  // IsValidSolution(wrong_x, wrong_y, wrong_z, a, b, c, d) should NOT hold
  expect !IsValidSolution(4, 5, 5, 1, 3, 5, 7), "spec negative 1";
  expect !IsValidSolution(2, 1, 1, 1, 1, 1, 1), "spec negative 2";
  expect !IsValidSolution(38167, 39580, 39580, 31796, 38166, 39580, 43622), "spec negative 3";
  expect !IsValidSolution(2374455, 8591131, 8591131, 2374453, 2374454, 8591131, 23094546), "spec negative 4";
  expect !IsValidSolution(10, 10, 10, 8, 9, 10, 11), "spec negative 5";
  expect !IsValidSolution(2, 3, 3, 1, 1, 3, 100), "spec negative 6";
  expect !IsValidSolution(2, 2, 2, 1, 1, 2, 3), "spec negative 7";
  expect !IsValidSolution(211341212, 211341211, 211341211, 933009, 211341211, 211341211, 211341211), "spec negative 8";
  expect !IsValidSolution(3, 3, 3, 1, 2, 3, 5), "spec negative 9";
  expect !IsValidSolution(3, 4, 4, 1, 2, 4, 5), "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====
  var x, y, z: int;

  // Test 1
  x, y, z := IchihimeAndTriangle(1, 3, 5, 7);
  expect x == 3 && y == 5 && z == 5, "impl test 1a failed";
  x, y, z := IchihimeAndTriangle(1, 5, 5, 7);
  expect x == 5 && y == 5 && z == 5, "impl test 1b failed";
  x, y, z := IchihimeAndTriangle(100000, 200000, 300000, 400000);
  expect x == 200000 && y == 300000 && z == 300000, "impl test 1c failed";
  x, y, z := IchihimeAndTriangle(1, 1, 977539810, 977539810);
  expect x == 1 && y == 977539810 && z == 977539810, "impl test 1d failed";

  // Test 2
  x, y, z := IchihimeAndTriangle(1, 1, 1, 1);
  expect x == 1 && y == 1 && z == 1, "impl test 2 failed";

  // Test 3
  x, y, z := IchihimeAndTriangle(31796, 38166, 39580, 43622);
  expect x == 38166 && y == 39580 && z == 39580, "impl test 3a failed";
  x, y, z := IchihimeAndTriangle(3002, 27223, 58836, 70214);
  expect x == 27223 && y == 58836 && z == 58836, "impl test 3b failed";
  x, y, z := IchihimeAndTriangle(13832, 74454, 78650, 89847);
  expect x == 74454 && y == 78650 && z == 78650, "impl test 3c failed";

  // Test 4
  x, y, z := IchihimeAndTriangle(2374453, 2374454, 8591131, 23094546);
  expect x == 2374454 && y == 8591131 && z == 8591131, "impl test 4a failed";
  x, y, z := IchihimeAndTriangle(5813291, 5813292, 9709163, 35032815);
  expect x == 5813292 && y == 9709163 && z == 9709163, "impl test 4b failed";
  x, y, z := IchihimeAndTriangle(4280399, 23049698, 23049701, 34728360);
  expect x == 23049698 && y == 23049701 && z == 23049701, "impl test 4c failed";
  x, y, z := IchihimeAndTriangle(15184184, 18688462, 22400847, 22400849);
  expect x == 18688462 && y == 22400847 && z == 22400847, "impl test 4d failed";
  x, y, z := IchihimeAndTriangle(24397371, 31462070, 33936330, 33936331);
  expect x == 31462070 && y == 33936330 && z == 33936330, "impl test 4e failed";
  x, y, z := IchihimeAndTriangle(21376685, 28241116, 38909200, 38909202);
  expect x == 28241116 && y == 38909200 && z == 38909200, "impl test 4f failed";
  x, y, z := IchihimeAndTriangle(29491847, 31628480, 31628482, 45225214);
  expect x == 31628480 && y == 31628482 && z == 31628482, "impl test 4g failed";
  x, y, z := IchihimeAndTriangle(15144763, 15414479, 36902879, 36902881);
  expect x == 15414479 && y == 36902879 && z == 36902879, "impl test 4h failed";
  x, y, z := IchihimeAndTriangle(36023581, 38889986, 47732180, 47732180);
  expect x == 38889986 && y == 47732180 && z == 47732180, "impl test 4i failed";
  x, y, z := IchihimeAndTriangle(31679295, 34770550, 48893932, 48893932);
  expect x == 34770550 && y == 48893932 && z == 48893932, "impl test 4j failed";
  x, y, z := IchihimeAndTriangle(5191255, 5191258, 35923383, 42585840);
  expect x == 5191258 && y == 35923383 && z == 35923383, "impl test 4k failed";
  x, y, z := IchihimeAndTriangle(12751172, 28569071, 40043177, 40043177);
  expect x == 28569071 && y == 40043177 && z == 40043177, "impl test 4l failed";
  x, y, z := IchihimeAndTriangle(7647578, 7647580, 40143919, 41874647);
  expect x == 7647580 && y == 40143919 && z == 40143919, "impl test 4m failed";
  x, y, z := IchihimeAndTriangle(11404615, 11404618, 25570153, 47200967);
  expect x == 11404618 && y == 25570153 && z == 25570153, "impl test 4n failed";

  // Test 5
  x, y, z := IchihimeAndTriangle(8, 9, 10, 11);
  expect x == 9 && y == 10 && z == 10, "impl test 5 failed";

  // Test 6
  x, y, z := IchihimeAndTriangle(1, 1, 3, 100);
  expect x == 1 && y == 3 && z == 3, "impl test 6 failed";

  // Test 7
  x, y, z := IchihimeAndTriangle(1, 1, 2, 3);
  expect x == 1 && y == 2 && z == 2, "impl test 7 failed";

  // Test 8
  x, y, z := IchihimeAndTriangle(933009, 211341211, 211341211, 211341211);
  expect x == 211341211 && y == 211341211 && z == 211341211, "impl test 8 failed";

  // Test 9
  x, y, z := IchihimeAndTriangle(1, 2, 3, 5);
  expect x == 2 && y == 3 && z == 3, "impl test 9 failed";

  // Test 10
  x, y, z := IchihimeAndTriangle(1, 2, 4, 5);
  expect x == 2 && y == 4 && z == 4, "impl test 10 failed";

  print "All tests passed\n";
}