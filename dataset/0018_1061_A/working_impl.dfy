method Coins(n: int, S: int) returns (minCoins: int)
{
  minCoins := (S - 1) / n + 1;
}

method Main()
{
  var r: int;

  r := Coins(5, 11);
  expect r == 3, "Test 1 failed";

  r := Coins(6, 16);
  expect r == 3, "Test 2 failed";

  r := Coins(14, 28);
  expect r == 2, "Test 3 failed";

  r := Coins(5, 29);
  expect r == 6, "Test 4 failed";

  r := Coins(10, 24);
  expect r == 3, "Test 5 failed";

  r := Coins(1, 30);
  expect r == 30, "Test 6 failed";

  r := Coins(14969, 66991573);
  expect r == 4476, "Test 7 failed";

  r := Coins(1, 1000000000);
  expect r == 1000000000, "Test 8 failed";

  r := Coins(100000, 1);
  expect r == 1, "Test 9 failed";

  r := Coins(10, 46);
  expect r == 5, "Test 10 failed";

  r := Coins(11, 35);
  expect r == 4, "Test 11 failed";

  r := Coins(12, 45);
  expect r == 4, "Test 12 failed";

  r := Coins(15, 34);
  expect r == 3, "Test 13 failed";

  r := Coins(31859, 629091638);
  expect r == 19747, "Test 14 failed";

  r := Coins(15666, 689919612);
  expect r == 44040, "Test 15 failed";

  r := Coins(90681, 254480989);
  expect r == 2807, "Test 16 failed";

  r := Coins(69018, 523197828);
  expect r == 7581, "Test 17 failed";

  r := Coins(1352, 434805201);
  expect r == 321602, "Test 18 failed";

  r := Coins(73439, 384841883);
  expect r == 5241, "Test 19 failed";

  r := Coins(42482, 352232377);
  expect r == 8292, "Test 20 failed";

  print "All tests passed\n";
}