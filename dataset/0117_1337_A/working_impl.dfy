method IchihimeAndTriangle(a: int, b: int, c: int, d: int) returns (x: int, y: int, z: int)
{
  x := b;
  y := c;
  z := c;
}

method Main()
{
  // Test 1
  var x, y, z := IchihimeAndTriangle(1, 3, 5, 7);
  expect x == 3 && y == 5 && z == 5, "Test 1a failed";
  x, y, z := IchihimeAndTriangle(1, 5, 5, 7);
  expect x == 5 && y == 5 && z == 5, "Test 1b failed";
  x, y, z := IchihimeAndTriangle(100000, 200000, 300000, 400000);
  expect x == 200000 && y == 300000 && z == 300000, "Test 1c failed";
  x, y, z := IchihimeAndTriangle(1, 1, 977539810, 977539810);
  expect x == 1 && y == 977539810 && z == 977539810, "Test 1d failed";

  // Test 2
  x, y, z := IchihimeAndTriangle(1, 1, 1, 1);
  expect x == 1 && y == 1 && z == 1, "Test 2 failed";

  // Test 3
  x, y, z := IchihimeAndTriangle(31796, 38166, 39580, 43622);
  expect x == 38166 && y == 39580 && z == 39580, "Test 3a failed";
  x, y, z := IchihimeAndTriangle(3002, 27223, 58836, 70214);
  expect x == 27223 && y == 58836 && z == 58836, "Test 3b failed";
  x, y, z := IchihimeAndTriangle(13832, 74454, 78650, 89847);
  expect x == 74454 && y == 78650 && z == 78650, "Test 3c failed";

  // Test 4
  x, y, z := IchihimeAndTriangle(2374453, 2374454, 8591131, 23094546);
  expect x == 2374454 && y == 8591131 && z == 8591131, "Test 4a failed";
  x, y, z := IchihimeAndTriangle(5813291, 5813292, 9709163, 35032815);
  expect x == 5813292 && y == 9709163 && z == 9709163, "Test 4b failed";
  x, y, z := IchihimeAndTriangle(4280399, 23049698, 23049701, 34728360);
  expect x == 23049698 && y == 23049701 && z == 23049701, "Test 4c failed";
  x, y, z := IchihimeAndTriangle(15184184, 18688462, 22400847, 22400849);
  expect x == 18688462 && y == 22400847 && z == 22400847, "Test 4d failed";
  x, y, z := IchihimeAndTriangle(24397371, 31462070, 33936330, 33936331);
  expect x == 31462070 && y == 33936330 && z == 33936330, "Test 4e failed";
  x, y, z := IchihimeAndTriangle(21376685, 28241116, 38909200, 38909202);
  expect x == 28241116 && y == 38909200 && z == 38909200, "Test 4f failed";
  x, y, z := IchihimeAndTriangle(29491847, 31628480, 31628482, 45225214);
  expect x == 31628480 && y == 31628482 && z == 31628482, "Test 4g failed";
  x, y, z := IchihimeAndTriangle(15144763, 15414479, 36902879, 36902881);
  expect x == 15414479 && y == 36902879 && z == 36902879, "Test 4h failed";
  x, y, z := IchihimeAndTriangle(36023581, 38889986, 47732180, 47732180);
  expect x == 38889986 && y == 47732180 && z == 47732180, "Test 4i failed";
  x, y, z := IchihimeAndTriangle(31679295, 34770550, 48893932, 48893932);
  expect x == 34770550 && y == 48893932 && z == 48893932, "Test 4j failed";
  x, y, z := IchihimeAndTriangle(5191255, 5191258, 35923383, 42585840);
  expect x == 5191258 && y == 35923383 && z == 35923383, "Test 4k failed";
  x, y, z := IchihimeAndTriangle(12751172, 28569071, 40043177, 40043177);
  expect x == 28569071 && y == 40043177 && z == 40043177, "Test 4l failed";
  x, y, z := IchihimeAndTriangle(7647578, 7647580, 40143919, 41874647);
  expect x == 7647580 && y == 40143919 && z == 40143919, "Test 4m failed";
  x, y, z := IchihimeAndTriangle(11404615, 11404618, 25570153, 47200967);
  expect x == 11404618 && y == 25570153 && z == 25570153, "Test 4n failed";

  // Test 5
  x, y, z := IchihimeAndTriangle(8, 9, 10, 11);
  expect x == 9 && y == 10 && z == 10, "Test 5 failed";

  // Test 6
  x, y, z := IchihimeAndTriangle(1, 1, 3, 100);
  expect x == 1 && y == 3 && z == 3, "Test 6 failed";

  // Test 7
  x, y, z := IchihimeAndTriangle(1, 1, 2, 3);
  expect x == 1 && y == 2 && z == 2, "Test 7 failed";

  // Test 8
  x, y, z := IchihimeAndTriangle(933009, 211341211, 211341211, 211341211);
  expect x == 211341211 && y == 211341211 && z == 211341211, "Test 8 failed";

  // Test 9
  x, y, z := IchihimeAndTriangle(1, 2, 3, 5);
  expect x == 2 && y == 3 && z == 3, "Test 9 failed";

  // Test 10
  x, y, z := IchihimeAndTriangle(1, 2, 4, 5);
  expect x == 2 && y == 4 && z == 4, "Test 10 failed";

  // Test 11
  x, y, z := IchihimeAndTriangle(4, 5, 5, 7);
  expect x == 5 && y == 5 && z == 5, "Test 11 failed";

  // Test 12
  x, y, z := IchihimeAndTriangle(5, 6, 7, 8);
  expect x == 6 && y == 7 && z == 7, "Test 12 failed";

  // Test 13
  x, y, z := IchihimeAndTriangle(6, 7, 8, 9);
  expect x == 7 && y == 8 && z == 8, "Test 13 failed";

  // Test 14
  x, y, z := IchihimeAndTriangle(7, 8, 9, 10);
  expect x == 8 && y == 9 && z == 9, "Test 14 failed";

  // Test 15
  x, y, z := IchihimeAndTriangle(1, 3, 4, 7);
  expect x == 3 && y == 4 && z == 4, "Test 15 failed";

  // Test 16
  x, y, z := IchihimeAndTriangle(9, 9, 9, 9);
  expect x == 9 && y == 9 && z == 9, "Test 16a failed";
  x, y, z := IchihimeAndTriangle(1, 2, 3, 4);
  expect x == 2 && y == 3 && z == 3, "Test 16b failed";

  // Test 18 (all 1s, already covered by Test 2)
  x, y, z := IchihimeAndTriangle(1, 1, 1, 1);
  expect x == 1 && y == 1 && z == 1, "Test 18 failed";

  // Test 19
  x, y, z := IchihimeAndTriangle(1, 4, 6, 6);
  expect x == 4 && y == 6 && z == 6, "Test 19 failed";

  // Test 20
  x, y, z := IchihimeAndTriangle(1, 1, 2, 2);
  expect x == 1 && y == 2 && z == 2, "Test 20 failed";

  print "All tests passed\n";
}