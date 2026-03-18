method CardsForFriends(w: int, h: int, n: int) returns (result: bool)
{
  var cnt := 1;
  var ww := w;
  var hh := h;
  while ww > 0 && ww % 2 == 0
  {
    cnt := cnt * 2;
    ww := ww / 2;
  }
  while hh > 0 && hh % 2 == 0
  {
    cnt := cnt * 2;
    hh := hh / 2;
  }
  result := cnt >= n;
}

method Main()
{
  var r: bool;

  // Test 1
  r := CardsForFriends(2, 2, 3);
  expect r == true, "Test 1.1: (2,2,3) expected true";
  r := CardsForFriends(3, 3, 2);
  expect r == false, "Test 1.2: (3,3,2) expected false";
  r := CardsForFriends(5, 10, 2);
  expect r == true, "Test 1.3: (5,10,2) expected true";
  r := CardsForFriends(11, 13, 1);
  expect r == true, "Test 1.4: (11,13,1) expected true";
  r := CardsForFriends(1, 4, 4);
  expect r == true, "Test 1.5: (1,4,4) expected true";

  // Test 2
  r := CardsForFriends(8192, 8192, 67108864);
  expect r == true, "Test 2.1: (8192,8192,67108864) expected true";

  // Test 3
  r := CardsForFriends(1024, 1024, 22212);
  expect r == true, "Test 3.1: (1024,1024,22212) expected true";

  // Test 4
  r := CardsForFriends(6144, 8192, 16777216);
  expect r == true, "Test 4.1: (6144,8192,16777216) expected true";
  r := CardsForFriends(8192, 6144, 16777216);
  expect r == true, "Test 4.2: (8192,6144,16777216) expected true";
  r := CardsForFriends(8192, 8192, 67108864);
  expect r == true, "Test 4.3: (8192,8192,67108864) expected true";
  r := CardsForFriends(8192, 8192, 67108865);
  expect r == false, "Test 4.4: (8192,8192,67108865) expected false";
  r := CardsForFriends(6144, 8192, 67108864);
  expect r == false, "Test 4.5: (6144,8192,67108864) expected false";
  r := CardsForFriends(8192, 6044, 67108864);
  expect r == false, "Test 4.6: (8192,6044,67108864) expected false";
  r := CardsForFriends(6144, 8192, 16777217);
  expect r == false, "Test 4.7: (6144,8192,16777217) expected false";
  r := CardsForFriends(8192, 6044, 16777217);
  expect r == false, "Test 4.8: (8192,6044,16777217) expected false";

  // Test 5
  r := CardsForFriends(8192, 8192, 1000000);
  expect r == true, "Test 5.1: (8192,8192,1000000) expected true";

  // Test 6
  r := CardsForFriends(8192, 8192, 67108864);
  expect r == true, "Test 6.1: (8192,8192,67108864) expected true";
  r := CardsForFriends(8192, 8192, 67108865);
  expect r == false, "Test 6.2: (8192,8192,67108865) expected false";
  r := CardsForFriends(8192, 8192, 70000000);
  expect r == false, "Test 6.3: (8192,8192,70000000) expected false";
  r := CardsForFriends(8192, 8192, 67108863);
  expect r == true, "Test 6.4: (8192,8192,67108863) expected true";
  r := CardsForFriends(1, 1, 1);
  expect r == true, "Test 6.5: (1,1,1) expected true";
  r := CardsForFriends(13, 13, 1);
  expect r == true, "Test 6.6: (13,13,1) expected true";
  r := CardsForFriends(1000, 1000, 100);
  expect r == false, "Test 6.7: (1000,1000,100) expected false";
  r := CardsForFriends(100, 15, 16);
  expect r == false, "Test 6.8: (100,15,16) expected false";
  r := CardsForFriends(157, 185, 95);
  expect r == false, "Test 6.9: (157,185,95) expected false";
  r := CardsForFriends(1257, 1895, 12);
  expect r == false, "Test 6.10: (1257,1895,12) expected false";
  r := CardsForFriends(1574, 4984, 164);
  expect r == false, "Test 6.11: (1574,4984,164) expected false";
  r := CardsForFriends(1564, 8917, 15);
  expect r == false, "Test 6.12: (1564,8917,15) expected false";
  r := CardsForFriends(150, 15, 2);
  expect r == true, "Test 6.13: (150,15,2) expected true";
  r := CardsForFriends(1500, 10, 40);
  expect r == false, "Test 6.14: (1500,10,40) expected false";
  r := CardsForFriends(1, 10000, 1000);
  expect r == false, "Test 6.15: (1,10000,1000) expected false";
  r := CardsForFriends(1, 10000, 10000);
  expect r == false, "Test 6.16: (1,10000,10000) expected false";

  // Test 7
  r := CardsForFriends(8192, 8192, 67108865);
  expect r == false, "Test 7.1: (8192,8192,67108865) expected false";

  print "All tests passed\n";
}