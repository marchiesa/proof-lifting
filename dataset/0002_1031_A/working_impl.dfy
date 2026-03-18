method GoldenPlate(w: int, h: int, k: int) returns (gilded: int)
{
  gilded := 0;
  var ww := w;
  var hh := h;
  var i := 0;
  while i < k
  {
    var minWH := if ww < hh then ww else hh;
    var maxWH := if ww > hh then ww else hh;
    if minWH == 1 {
      gilded := gilded + maxWH;
    } else {
      gilded := gilded + 2 * (ww + hh) - 4;
    }
    ww := ww - 4;
    hh := hh - 4;
    i := i + 1;
  }
}

method Main()
{
  var result: int;

  result := GoldenPlate(3, 3, 1);
  expect result == 8, "Test 1 failed";

  result := GoldenPlate(7, 9, 1);
  expect result == 28, "Test 2 failed";

  result := GoldenPlate(7, 9, 2);
  expect result == 40, "Test 3 failed";

  result := GoldenPlate(18, 26, 3);
  expect result == 204, "Test 4 failed";

  result := GoldenPlate(63, 34, 8);
  expect result == 1072, "Test 5 failed";

  result := GoldenPlate(100, 100, 25);
  expect result == 5100, "Test 6 failed";

  result := GoldenPlate(4, 3, 1);
  expect result == 10, "Test 7 failed";

  result := GoldenPlate(3, 4, 1);
  expect result == 10, "Test 8 failed";

  result := GoldenPlate(3, 10, 1);
  expect result == 22, "Test 9 failed";

  result := GoldenPlate(12, 3, 1);
  expect result == 26, "Test 10 failed";

  result := GoldenPlate(4, 4, 1);
  expect result == 12, "Test 11 failed";

  result := GoldenPlate(10, 4, 1);
  expect result == 24, "Test 12 failed";

  result := GoldenPlate(4, 12, 1);
  expect result == 28, "Test 13 failed";

  result := GoldenPlate(10, 10, 1);
  expect result == 36, "Test 14 failed";

  result := GoldenPlate(10, 10, 2);
  expect result == 56, "Test 15 failed";

  result := GoldenPlate(12, 10, 1);
  expect result == 40, "Test 16 failed";

  result := GoldenPlate(10, 12, 2);
  expect result == 64, "Test 17 failed";

  result := GoldenPlate(12, 11, 1);
  expect result == 42, "Test 18 failed";

  result := GoldenPlate(11, 12, 2);
  expect result == 68, "Test 19 failed";

  result := GoldenPlate(12, 11, 3);
  expect result == 78, "Test 20 failed";

  print "All tests passed\n";
}