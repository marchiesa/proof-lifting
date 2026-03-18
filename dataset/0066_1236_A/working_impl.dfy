method Stones(a: int, b: int, c: int) returns (maxStones: int)
{
  var c2 := if c / 2 < b then c / 2 else b;
  var rem := if (b - c2) / 2 < a then (b - c2) / 2 else a;
  maxStones := (c2 + rem) * 3;
}

method Main()
{
  var r: int;

  // Test 1
  r := Stones(3, 4, 5); expect r == 9, "Stones(3,4,5)";
  r := Stones(1, 0, 5); expect r == 0, "Stones(1,0,5)";
  r := Stones(5, 3, 2); expect r == 6, "Stones(5,3,2)";

  // Test 2 (exhaustive 0..3)
  r := Stones(0, 0, 0); expect r == 0, "Stones(0,0,0)";
  r := Stones(0, 0, 1); expect r == 0, "Stones(0,0,1)";
  r := Stones(0, 0, 2); expect r == 0, "Stones(0,0,2)";
  r := Stones(0, 0, 3); expect r == 0, "Stones(0,0,3)";
  r := Stones(0, 1, 0); expect r == 0, "Stones(0,1,0)";
  r := Stones(0, 1, 1); expect r == 0, "Stones(0,1,1)";
  r := Stones(0, 1, 2); expect r == 3, "Stones(0,1,2)";
  r := Stones(0, 1, 3); expect r == 3, "Stones(0,1,3)";
  r := Stones(0, 2, 0); expect r == 0, "Stones(0,2,0)";
  r := Stones(0, 2, 1); expect r == 0, "Stones(0,2,1)";
  r := Stones(0, 2, 2); expect r == 3, "Stones(0,2,2)";
  r := Stones(0, 2, 3); expect r == 3, "Stones(0,2,3)";
  r := Stones(0, 3, 0); expect r == 0, "Stones(0,3,0)";
  r := Stones(0, 3, 1); expect r == 0, "Stones(0,3,1)";
  r := Stones(0, 3, 2); expect r == 3, "Stones(0,3,2)";
  r := Stones(0, 3, 3); expect r == 3, "Stones(0,3,3)";
  r := Stones(1, 0, 0); expect r == 0, "Stones(1,0,0)";
  r := Stones(1, 0, 1); expect r == 0, "Stones(1,0,1)";
  r := Stones(1, 0, 2); expect r == 0, "Stones(1,0,2)";
  r := Stones(1, 0, 3); expect r == 0, "Stones(1,0,3)";
  r := Stones(1, 1, 0); expect r == 0, "Stones(1,1,0)";
  r := Stones(1, 1, 1); expect r == 0, "Stones(1,1,1)";
  r := Stones(1, 1, 2); expect r == 3, "Stones(1,1,2)";
  r := Stones(1, 1, 3); expect r == 3, "Stones(1,1,3)";
  r := Stones(1, 2, 0); expect r == 3, "Stones(1,2,0)";
  r := Stones(1, 2, 1); expect r == 3, "Stones(1,2,1)";
  r := Stones(1, 2, 2); expect r == 3, "Stones(1,2,2)";
  r := Stones(1, 2, 3); expect r == 3, "Stones(1,2,3)";
  r := Stones(1, 3, 0); expect r == 3, "Stones(1,3,0)";
  r := Stones(1, 3, 1); expect r == 3, "Stones(1,3,1)";
  r := Stones(1, 3, 2); expect r == 6, "Stones(1,3,2)";
  r := Stones(1, 3, 3); expect r == 6, "Stones(1,3,3)";
  r := Stones(2, 0, 0); expect r == 0, "Stones(2,0,0)";
  r := Stones(2, 0, 1); expect r == 0, "Stones(2,0,1)";
  r := Stones(2, 0, 2); expect r == 0, "Stones(2,0,2)";
  r := Stones(2, 0, 3); expect r == 0, "Stones(2,0,3)";
  r := Stones(2, 1, 0); expect r == 0, "Stones(2,1,0)";
  r := Stones(2, 1, 1); expect r == 0, "Stones(2,1,1)";
  r := Stones(2, 1, 2); expect r == 3, "Stones(2,1,2)";
  r := Stones(2, 1, 3); expect r == 3, "Stones(2,1,3)";
  r := Stones(2, 2, 0); expect r == 3, "Stones(2,2,0)";
  r := Stones(2, 2, 1); expect r == 3, "Stones(2,2,1)";
  r := Stones(2, 2, 2); expect r == 3, "Stones(2,2,2)";
  r := Stones(2, 2, 3); expect r == 3, "Stones(2,2,3)";
  r := Stones(2, 3, 0); expect r == 3, "Stones(2,3,0)";
  r := Stones(2, 3, 1); expect r == 3, "Stones(2,3,1)";
  r := Stones(2, 3, 2); expect r == 6, "Stones(2,3,2)";
  r := Stones(2, 3, 3); expect r == 6, "Stones(2,3,3)";
  r := Stones(3, 0, 0); expect r == 0, "Stones(3,0,0)";
  r := Stones(3, 0, 1); expect r == 0, "Stones(3,0,1)";
  r := Stones(3, 0, 2); expect r == 0, "Stones(3,0,2)";
  r := Stones(3, 0, 3); expect r == 0, "Stones(3,0,3)";
  r := Stones(3, 1, 0); expect r == 0, "Stones(3,1,0)";
  r := Stones(3, 1, 1); expect r == 0, "Stones(3,1,1)";
  r := Stones(3, 1, 2); expect r == 3, "Stones(3,1,2)";
  r := Stones(3, 1, 3); expect r == 3, "Stones(3,1,3)";
  r := Stones(3, 2, 0); expect r == 3, "Stones(3,2,0)";
  r := Stones(3, 2, 1); expect r == 3, "Stones(3,2,1)";
  r := Stones(3, 2, 2); expect r == 3, "Stones(3,2,2)";
  r := Stones(3, 2, 3); expect r == 3, "Stones(3,2,3)";
  r := Stones(3, 3, 0); expect r == 3, "Stones(3,3,0)";
  r := Stones(3, 3, 1); expect r == 3, "Stones(3,3,1)";
  r := Stones(3, 3, 2); expect r == 6, "Stones(3,3,2)";
  r := Stones(3, 3, 3); expect r == 6, "Stones(3,3,3)";

  // Test 3
  r := Stones(100, 100, 100); expect r == 225, "Stones(100,100,100)";
  r := Stones(0, 0, 0); expect r == 0, "Stones(0,0,0) t3";
  r := Stones(0, 50, 100); expect r == 150, "Stones(0,50,100)";
  r := Stones(100, 50, 0); expect r == 75, "Stones(100,50,0)";
  r := Stones(100, 30, 100); expect r == 90, "Stones(100,30,100)";

  // Test 4
  r := Stones(9, 4, 8); expect r == 12, "Stones(9,4,8)";
  r := Stones(10, 6, 7); expect r == 12, "Stones(10,6,7)";
  r := Stones(4, 6, 0); expect r == 9, "Stones(4,6,0)";
  r := Stones(7, 7, 6); expect r == 15, "Stones(7,7,6)";
  r := Stones(3, 3, 10); expect r == 9, "Stones(3,3,10)";
  r := Stones(4, 2, 1); expect r == 3, "Stones(4,2,1)";
  r := Stones(4, 4, 0); expect r == 6, "Stones(4,4,0)";
  r := Stones(2, 0, 0); expect r == 0, "Stones(2,0,0) t4";
  r := Stones(8, 8, 7); expect r == 15, "Stones(8,8,7)";
  r := Stones(3, 1, 7); expect r == 3, "Stones(3,1,7)";
  r := Stones(3, 10, 7); expect r == 18, "Stones(3,10,7)";
  r := Stones(1, 7, 3); expect r == 6, "Stones(1,7,3)";
  r := Stones(7, 9, 1); expect r == 12, "Stones(7,9,1)";
  r := Stones(1, 6, 9); expect r == 15, "Stones(1,6,9)";
  r := Stones(0, 9, 5); expect r == 6, "Stones(0,9,5)";
  r := Stones(4, 0, 0); expect r == 0, "Stones(4,0,0)";
  r := Stones(2, 10, 0); expect r == 6, "Stones(2,10,0)";
  r := Stones(4, 8, 5); expect r == 15, "Stones(4,8,5)";
  r := Stones(10, 0, 1); expect r == 0, "Stones(10,0,1)";
  r := Stones(8, 1, 1); expect r == 0, "Stones(8,1,1)";

  // Test 5
  r := Stones(4, 4, 8); expect r == 12, "Stones(4,4,8)";
  r := Stones(5, 3, 7); expect r == 9, "Stones(5,3,7)";
  r := Stones(0, 0, 1); expect r == 0, "Stones(0,0,1) t5";
  r := Stones(2, 3, 8); expect r == 9, "Stones(2,3,8)";
  r := Stones(9, 4, 10); expect r == 12, "Stones(9,4,10)";
  r := Stones(4, 8, 10); expect r == 18, "Stones(4,8,10)";
  r := Stones(6, 3, 4); expect r == 6, "Stones(6,3,4)";
  r := Stones(10, 10, 0); expect r == 15, "Stones(10,10,0)";
  r := Stones(0, 7, 4); expect r == 6, "Stones(0,7,4)";
  r := Stones(6, 2, 2); expect r == 3, "Stones(6,2,2)";
  r := Stones(3, 10, 2); expect r == 12, "Stones(3,10,2)";
  r := Stones(2, 7, 6); expect r == 15, "Stones(2,7,6)";
  r := Stones(1, 2, 6); expect r == 6, "Stones(1,2,6)";
  r := Stones(2, 3, 0); expect r == 3, "Stones(2,3,0)";
  r := Stones(1, 3, 4); expect r == 6, "Stones(1,3,4)";
  r := Stones(5, 0, 10); expect r == 0, "Stones(5,0,10)";
  r := Stones(4, 1, 2); expect r == 3, "Stones(4,1,2)";
  r := Stones(3, 7, 7); expect r == 15, "Stones(3,7,7)";
  r := Stones(7, 10, 5); expect r == 18, "Stones(7,10,5)";
  r := Stones(0, 9, 0); expect r == 0, "Stones(0,9,0)";

  // Test 6
  r := Stones(0, 2, 9); expect r == 6, "Stones(0,2,9)";
  r := Stones(2, 9, 7); expect r == 15, "Stones(2,9,7)";
  r := Stones(7, 3, 3); expect r == 6, "Stones(7,3,3)";
  r := Stones(9, 0, 10); expect r == 0, "Stones(9,0,10)";
  r := Stones(4, 8, 0); expect r == 12, "Stones(4,8,0)";
  r := Stones(2, 3, 9); expect r == 9, "Stones(2,3,9)";
  r := Stones(7, 0, 8); expect r == 0, "Stones(7,0,8)";
  r := Stones(5, 8, 10); expect r == 18, "Stones(5,8,10)";
  r := Stones(1, 4, 2); expect r == 6, "Stones(1,4,2)";
  r := Stones(6, 4, 7); expect r == 9, "Stones(6,4,7)";
  r := Stones(3, 9, 6); expect r == 18, "Stones(3,9,6)";
  r := Stones(3, 5, 7); expect r == 12, "Stones(3,5,7)";
  r := Stones(5, 6, 1); expect r == 9, "Stones(5,6,1)";
  r := Stones(2, 9, 1); expect r == 6, "Stones(2,9,1)";
  r := Stones(0, 6, 4); expect r == 6, "Stones(0,6,4)";
  r := Stones(5, 9, 1); expect r == 12, "Stones(5,9,1)";
  r := Stones(6, 1, 7); expect r == 3, "Stones(6,1,7)";
  r := Stones(0, 6, 10); expect r == 15, "Stones(0,6,10)";
  r := Stones(2, 10, 7); expect r == 15, "Stones(2,10,7)";
  r := Stones(4, 5, 10); expect r == 15, "Stones(4,5,10)";

  // Test 7
  r := Stones(6, 0, 8); expect r == 0, "Stones(6,0,8)";
  r := Stones(0, 6, 5); expect r == 6, "Stones(0,6,5)";
  r := Stones(1, 7, 3); expect r == 6, "Stones(1,7,3) t7";
  r := Stones(6, 5, 2); expect r == 9, "Stones(6,5,2)";
  r := Stones(9, 10, 0); expect r == 15, "Stones(9,10,0)";
  r := Stones(2, 8, 8); expect r == 18, "Stones(2,8,8)";
  r := Stones(9, 8, 1); expect r == 12, "Stones(9,8,1)";
  r := Stones(1, 9, 8); expect r == 15, "Stones(1,9,8)";
  r := Stones(2, 4, 10); expect r == 12, "Stones(2,4,10)";
  r := Stones(9, 5, 0); expect r == 6, "Stones(9,5,0)";
  r := Stones(2, 9, 1); expect r == 6, "Stones(2,9,1) t7";
  r := Stones(5, 5, 10); expect r == 15, "Stones(5,5,10)";
  r := Stones(10, 8, 6); expect r == 15, "Stones(10,8,6)";
  r := Stones(3, 6, 0); expect r == 9, "Stones(3,6,0)";
  r := Stones(10, 9, 2); expect r == 15, "Stones(10,9,2)";
  r := Stones(6, 9, 1); expect r == 12, "Stones(6,9,1)";
  r := Stones(8, 4, 10); expect r == 12, "Stones(8,4,10)";
  r := Stones(10, 3, 4); expect r == 6, "Stones(10,3,4)";
  r := Stones(10, 0, 10); expect r == 0, "Stones(10,0,10)";
  r := Stones(6, 1, 9); expect r == 3, "Stones(6,1,9)";

  // Test 8
  r := Stones(2, 0, 8); expect r == 0, "Stones(2,0,8)";
  r := Stones(8, 3, 5); expect r == 6, "Stones(8,3,5)";
  r := Stones(8, 10, 3); expect r == 15, "Stones(8,10,3)";
  r := Stones(3, 2, 4); expect r == 6, "Stones(3,2,4)";
  r := Stones(4, 2, 1); expect r == 3, "Stones(4,2,1) t8";
  r := Stones(0, 3, 7); expect r == 9, "Stones(0,3,7)";
  r := Stones(0, 7, 5); expect r == 6, "Stones(0,7,5)";
  r := Stones(7, 7, 8); expect r == 15, "Stones(7,7,8)";
  r := Stones(3, 3, 9); expect r == 9, "Stones(3,3,9)";
  r := Stones(1, 7, 5); expect r == 9, "Stones(1,7,5)";
  r := Stones(2, 8, 4); expect r == 12, "Stones(2,8,4)";
  r := Stones(6, 3, 0); expect r == 3, "Stones(6,3,0)";
  r := Stones(4, 1, 10); expect r == 3, "Stones(4,1,10)";
  r := Stones(3, 3, 2); expect r == 6, "Stones(3,3,2)";
  r := Stones(0, 0, 0); expect r == 0, "Stones(0,0,0) t8";
  r := Stones(7, 9, 2); expect r == 15, "Stones(7,9,2)";
  r := Stones(10, 6, 1); expect r == 9, "Stones(10,6,1)";
  r := Stones(10, 2, 6); expect r == 6, "Stones(10,2,6)";
  r := Stones(8, 9, 1); expect r == 12, "Stones(8,9,1)";
  r := Stones(8, 8, 0); expect r == 12, "Stones(8,8,0)";

  print "All tests passed\n";
}