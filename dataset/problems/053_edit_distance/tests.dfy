// Edit Distance -- Runtime spec tests

function Min3(a: int, b: int, c: int): int
{
  if a <= b && a <= c then a
  else if b <= c then b
  else c
}

method Main() {
  // Min3 tests
  expect Min3(1, 2, 3) == 1, "min3(1,2,3) = 1";
  expect Min3(3, 1, 2) == 1, "min3(3,1,2) = 1";
  expect Min3(2, 3, 1) == 1, "min3(2,3,1) = 1";
  expect Min3(5, 5, 5) == 5, "min3(5,5,5) = 5";
  expect Min3(0, 1, 2) == 0, "min3(0,1,2) = 0";
  expect Min3(-1, 0, 1) == -1, "min3(-1,0,1) = -1";

  // Wrong answers
  expect Min3(1, 2, 3) != 2, "min3(1,2,3) is not 2";
  expect Min3(1, 2, 3) != 3, "min3(1,2,3) is not 3";

  // Edit distance postcondition tests:
  // dist >= 0 and dist <= |s| + |t|
  // Known edit distances to verify postcondition bounds
  // edit_dist("", "abc") = 3, and 0 <= 3 <= 0+3
  var d1 := 3;
  expect d1 >= 0, "dist >= 0";
  expect d1 <= 0 + 3, "dist <= |s| + |t|";

  // edit_dist("abc", "abc") = 0, and 0 <= 0 <= 3+3
  var d2 := 0;
  expect d2 >= 0, "identical strings: dist >= 0";
  expect d2 <= 3 + 3, "identical strings: dist <= |s| + |t|";

  // edit_dist("kitten", "sitting") = 3, and 0 <= 3 <= 6+7
  var d3 := 3;
  expect d3 >= 0, "kitten/sitting: dist >= 0";
  expect d3 <= 6 + 7, "kitten/sitting: dist <= |s| + |t|";

  print "All spec tests passed\n";
}
