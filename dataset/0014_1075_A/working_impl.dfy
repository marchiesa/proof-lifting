method KingsRace(n: int, x: int, y: int) returns (winner: string)
{
  var dx1 := if x - 1 >= 0 then x - 1 else 1 - x;
  var dy1 := if y - 1 >= 0 then y - 1 else 1 - y;
  var dist1 := if dx1 >= dy1 then dx1 else dy1;

  var dx2 := if x - n >= 0 then x - n else n - x;
  var dy2 := if y - n >= 0 then y - n else n - y;
  var dist2 := if dx2 >= dy2 then dx2 else dy2;

  if dist1 <= dist2 {
    winner := "White";
  } else {
    winner := "Black";
  }
}

method Main()
{
  var result: string;

  result := KingsRace(4, 2, 3);
  expect result == "White", "Test 1 failed";

  result := KingsRace(5, 3, 5);
  expect result == "Black", "Test 2 failed";

  result := KingsRace(2, 2, 2);
  expect result == "Black", "Test 3 failed";

  result := KingsRace(1000000000000000000, 1000000000000000000, 1000000000000000000);
  expect result == "Black", "Test 4 failed";

  result := KingsRace(1000000000000000000, 1, 1);
  expect result == "White", "Test 5 failed";

  result := KingsRace(2, 1, 1);
  expect result == "White", "Test 6 failed";

  result := KingsRace(1234567890123456, 1234567889969697, 153760);
  expect result == "White", "Test 7 failed";

  result := KingsRace(12000000000000, 123056, 11999999876946);
  expect result == "Black", "Test 8 failed";

  result := KingsRace(839105509657869903, 591153401407154876, 258754952987011519);
  expect result == "Black", "Test 9 failed";

  result := KingsRace(778753534913338583, 547836868672081726, 265708022656451521);
  expect result == "Black", "Test 10 failed";

  result := KingsRace(521427324217141769, 375108452493312817, 366738689404083861);
  expect result == "Black", "Test 11 failed";

  result := KingsRace(1000000000000000, 208171971446456, 791828028553545);
  expect result == "White", "Test 12 failed";

  result := KingsRace(719386363530333627, 620916440917452264, 265151985453132665);
  expect result == "Black", "Test 13 failed";

  result := KingsRace(57719663734394834, 53160177030140966, 26258927428764347);
  expect result == "Black", "Test 14 failed";

  result := KingsRace(835610886713350713, 31708329050069500, 231857821534629883);
  expect result == "White", "Test 15 failed";

  result := KingsRace(17289468142098094, 4438423217327361, 4850647042283952);
  expect result == "White", "Test 16 failed";

  result := KingsRace(562949953421312, 259798251531825, 508175017145903);
  expect result == "Black", "Test 17 failed";

  result := KingsRace(9007199254740992, 7977679390099527, 3015199451140672);
  expect result == "Black", "Test 18 failed";

  result := KingsRace(982837494536444311, 471939396014493192, 262488194864680421);
  expect result == "White", "Test 19 failed";

  result := KingsRace(878602530892252875, 583753601575252768, 851813862933314387);
  expect result == "Black", "Test 20 failed";

  print "All tests passed\n";
}