method FavoriteSequence(b: seq<int>) returns (a: seq<int>)
{
  var x := 1;
  var y := 0;
  a := [];
  var i := 0;
  while i < |b|
  {
    if y == 0 {
      a := a + [b[x - 1]];
      y := 1;
    } else {
      a := a + [b[|b| - x]];
      x := x + 1;
      y := 0;
    }
    i := i + 1;
  }
}

method Main()
{
  var result: seq<int>;

  // Test 1, case 1
  result := FavoriteSequence([3, 4, 5, 2, 9, 1, 1]);
  expect result == [3, 1, 4, 1, 5, 9, 2], "Test 1.1 failed";

  // Test 1, case 2
  result := FavoriteSequence([9, 2, 7, 1]);
  expect result == [9, 1, 2, 7], "Test 1.2 failed";

  // Test 1, case 3
  result := FavoriteSequence([8, 4, 3, 1, 2, 7, 8, 7, 9, 4, 2]);
  expect result == [8, 2, 4, 4, 3, 9, 1, 7, 2, 8, 7], "Test 1.3 failed";

  // Test 1, case 4
  result := FavoriteSequence([42]);
  expect result == [42], "Test 1.4 failed";

  // Test 1, case 5
  result := FavoriteSequence([11, 7]);
  expect result == [11, 7], "Test 1.5 failed";

  // Test 1, case 6
  result := FavoriteSequence([1, 1, 1, 1, 1, 1, 1, 1]);
  expect result == [1, 1, 1, 1, 1, 1, 1, 1], "Test 1.6 failed";

  // Test 2, case 1
  result := FavoriteSequence([1324, 4, 5, 2, 9, 1, 1]);
  expect result == [1324, 1, 4, 1, 5, 9, 2], "Test 2.1 failed";

  // Test 2, case 2
  result := FavoriteSequence([9, 2, 7, 1]);
  expect result == [9, 1, 2, 7], "Test 2.2 failed";

  // Test 2, case 3
  result := FavoriteSequence([8, 4, 3, 1, 2, 7, 8, 7, 9, 4, 2]);
  expect result == [8, 2, 4, 4, 3, 9, 1, 7, 2, 8, 7], "Test 2.3 failed";

  // Test 2, case 4
  result := FavoriteSequence([42]);
  expect result == [42], "Test 2.4 failed";

  // Test 2, case 5
  result := FavoriteSequence([11, 7]);
  expect result == [11, 7], "Test 2.5 failed";

  // Test 2, case 6
  result := FavoriteSequence([1, 1, 1, 1, 1, 1, 1, 1]);
  expect result == [1, 1, 1, 1, 1, 1, 1, 1], "Test 2.6 failed";

  // Test 3
  result := FavoriteSequence([1453324, 2, 1453324, 1]);
  expect result == [1453324, 1, 2, 1453324], "Test 3 failed";

  // Test 4
  result := FavoriteSequence([3]);
  expect result == [3], "Test 4 failed";

  // Test 5
  result := FavoriteSequence([6]);
  expect result == [6], "Test 5 failed";

  // Test 6
  result := FavoriteSequence([9]);
  expect result == [9], "Test 6 failed";

  // Test 7
  result := FavoriteSequence([10]);
  expect result == [10], "Test 7 failed";

  // Test 8
  result := FavoriteSequence([20]);
  expect result == [20], "Test 8 failed";

  // Test 9
  result := FavoriteSequence([21]);
  expect result == [21], "Test 9 failed";

  // Test 10
  result := FavoriteSequence([22]);
  expect result == [22], "Test 10 failed";

  // Test 11
  result := FavoriteSequence([23]);
  expect result == [23], "Test 11 failed";

  // Test 12
  result := FavoriteSequence([24]);
  expect result == [24], "Test 12 failed";

  // Test 13
  result := FavoriteSequence([25]);
  expect result == [25], "Test 13 failed";

  // Test 14
  result := FavoriteSequence([45]);
  expect result == [45], "Test 14 failed";

  // Test 15
  result := FavoriteSequence([46]);
  expect result == [46], "Test 15 failed";

  // Test 16
  result := FavoriteSequence([47]);
  expect result == [47], "Test 16 failed";

  // Test 17
  result := FavoriteSequence([97]);
  expect result == [97], "Test 17 failed";

  // Test 18
  result := FavoriteSequence([98]);
  expect result == [98], "Test 18 failed";

  // Test 19
  result := FavoriteSequence([99]);
  expect result == [99], "Test 19 failed";

  print "All tests passed\n";
}