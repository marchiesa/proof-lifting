// --- Specification ---

function Evens(a: seq<int>): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else if |a| == 1 then [a[0]]
  else [a[0]] + Evens(a[2..])
}

function Odds(a: seq<int>): seq<int>
{
  if |a| <= 1 then []
  else Evens(a[1..])
}

function Reverse(a: seq<int>): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else Reverse(a[1..]) + [a[0]]
}

function WriteOnWhiteboard(favorite: seq<int>): seq<int>
{
  Evens(favorite) + Reverse(Odds(favorite))
}

predicate IsValidFavoriteSequence(favorite: seq<int>, whiteboard: seq<int>)
{
  |favorite| == |whiteboard| && WriteOnWhiteboard(favorite) == whiteboard
}

// --- Implementation ---

method {:verify false} FavoriteSequence(b: seq<int>) returns (a: seq<int>)
  ensures IsValidFavoriteSequence(a, b)
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

  // ========== SPEC POSITIVE TESTS ==========
  // IsValidFavoriteSequence(favorite, whiteboard) with correct pairs

  // From test 4: whiteboard [3], favorite [3]
  expect IsValidFavoriteSequence([3], [3]), "spec positive 1";

  // From test 5: whiteboard [6], favorite [6]
  expect IsValidFavoriteSequence([6], [6]), "spec positive 2";

  // From test 6: whiteboard [9], favorite [9]
  expect IsValidFavoriteSequence([9], [9]), "spec positive 3";

  // Scaled from test 1.5 ([11,7]->[11,7]): length 2
  // WriteOnWhiteboard([1,2]) = Evens([1,2]) + Reverse(Odds([1,2])) = [1] + [2] = [1,2]
  expect IsValidFavoriteSequence([1, 2], [1, 2]), "spec positive 4";

  // Scaled from test 1.1: length 3
  // WriteOnWhiteboard([1,3,2]) = Evens([1,3,2]) + Reverse(Odds([1,3,2])) = [1,2] + [3] = [1,2,3]
  expect IsValidFavoriteSequence([1, 3, 2], [1, 2, 3]), "spec positive 5";

  // Scaled from test 1.5: another length 2
  // WriteOnWhiteboard([3,2]) = [3] + [2] = [3,2]
  expect IsValidFavoriteSequence([3, 2], [3, 2]), "spec positive 6";

  // Another length 3 case
  // WriteOnWhiteboard([2,3,1]) = Evens([2,3,1]) + Reverse(Odds([2,3,1])) = [2,1] + [3] = [2,1,3]
  expect IsValidFavoriteSequence([2, 3, 1], [2, 1, 3]), "spec positive 7";

  // From test 7: whiteboard [10], favorite [10]
  expect IsValidFavoriteSequence([10], [10]), "spec positive 8";

  // ========== SPEC NEGATIVE TESTS ==========
  // IsValidFavoriteSequence(wrong_favorite, whiteboard) should be false

  // From negative 4: whiteboard [3], wrong favorite [4]
  expect !IsValidFavoriteSequence([4], [3]), "spec negative 1";

  // From negative 5: whiteboard [6], wrong favorite [7]
  expect !IsValidFavoriteSequence([7], [6]), "spec negative 2";

  // From negative 6: whiteboard [9], wrong favorite [10]
  expect !IsValidFavoriteSequence([10], [9]), "spec negative 3";

  // From negative 7: whiteboard [10], wrong favorite [11]
  expect !IsValidFavoriteSequence([11], [10]), "spec negative 4";

  // Scaled from negative 8: whiteboard [0], wrong favorite [1]
  expect !IsValidFavoriteSequence([1], [0]), "spec negative 5";

  // Scaled from negative 1: length 3, first element wrong
  // correct favorite for whiteboard [1,2,3] is [1,3,2]; wrong: [2,3,2]
  expect !IsValidFavoriteSequence([2, 3, 2], [1, 2, 3]), "spec negative 6";

  // Scaled from negative 2: length 2, first element wrong
  // correct favorite for whiteboard [1,2] is [1,2]; wrong: [2,2]
  expect !IsValidFavoriteSequence([2, 2], [1, 2]), "spec negative 7";

  // Scaled from negative 9: whiteboard [1], wrong favorite [2]
  expect !IsValidFavoriteSequence([2], [1]), "spec negative 8";

  // Scaled from negative 3: length 3, first element wrong
  // correct favorite for whiteboard [5,3,4] is [5,4,3]; wrong: [0,4,3]
  expect !IsValidFavoriteSequence([0, 4, 3], [5, 3, 4]), "spec negative 9";

  // Length mismatch negative test (scaled from negative 10)
  expect !IsValidFavoriteSequence([5, 5], [5]), "spec negative 10";

  // ========== IMPLEMENTATION TESTS ==========

  // Test 1, case 1
  result := FavoriteSequence([3, 4, 5, 2, 9, 1, 1]);
  expect result == [3, 1, 4, 1, 5, 9, 2], "impl test 1.1 failed";

  // Test 1, case 2
  result := FavoriteSequence([9, 2, 7, 1]);
  expect result == [9, 1, 2, 7], "impl test 1.2 failed";

  // Test 1, case 3
  result := FavoriteSequence([8, 4, 3, 1, 2, 7, 8, 7, 9, 4, 2]);
  expect result == [8, 2, 4, 4, 3, 9, 1, 7, 2, 8, 7], "impl test 1.3 failed";

  // Test 1, case 4
  result := FavoriteSequence([42]);
  expect result == [42], "impl test 1.4 failed";

  // Test 1, case 5
  result := FavoriteSequence([11, 7]);
  expect result == [11, 7], "impl test 1.5 failed";

  // Test 1, case 6
  result := FavoriteSequence([1, 1, 1, 1, 1, 1, 1, 1]);
  expect result == [1, 1, 1, 1, 1, 1, 1, 1], "impl test 1.6 failed";

  // Test 2, case 1
  result := FavoriteSequence([1324, 4, 5, 2, 9, 1, 1]);
  expect result == [1324, 1, 4, 1, 5, 9, 2], "impl test 2.1 failed";

  // Test 2, case 2
  result := FavoriteSequence([9, 2, 7, 1]);
  expect result == [9, 1, 2, 7], "impl test 2.2 failed";

  // Test 2, case 3
  result := FavoriteSequence([8, 4, 3, 1, 2, 7, 8, 7, 9, 4, 2]);
  expect result == [8, 2, 4, 4, 3, 9, 1, 7, 2, 8, 7], "impl test 2.3 failed";

  // Test 2, case 4
  result := FavoriteSequence([42]);
  expect result == [42], "impl test 2.4 failed";

  // Test 2, case 5
  result := FavoriteSequence([11, 7]);
  expect result == [11, 7], "impl test 2.5 failed";

  // Test 2, case 6
  result := FavoriteSequence([1, 1, 1, 1, 1, 1, 1, 1]);
  expect result == [1, 1, 1, 1, 1, 1, 1, 1], "impl test 2.6 failed";

  // Test 3
  result := FavoriteSequence([1453324, 2, 1453324, 1]);
  expect result == [1453324, 1, 2, 1453324], "impl test 3 failed";

  // Test 4
  result := FavoriteSequence([3]);
  expect result == [3], "impl test 4 failed";

  // Test 5
  result := FavoriteSequence([6]);
  expect result == [6], "impl test 5 failed";

  // Test 6
  result := FavoriteSequence([9]);
  expect result == [9], "impl test 6 failed";

  // Test 7
  result := FavoriteSequence([10]);
  expect result == [10], "impl test 7 failed";

  // Test 8
  result := FavoriteSequence([20]);
  expect result == [20], "impl test 8 failed";

  // Test 9
  result := FavoriteSequence([21]);
  expect result == [21], "impl test 9 failed";

  // Test 10
  result := FavoriteSequence([22]);
  expect result == [22], "impl test 10 failed";

  // Test 11
  result := FavoriteSequence([23]);
  expect result == [23], "impl test 11 failed";

  // Test 12
  result := FavoriteSequence([24]);
  expect result == [24], "impl test 12 failed";

  // Test 13
  result := FavoriteSequence([25]);
  expect result == [25], "impl test 13 failed";

  // Test 14
  result := FavoriteSequence([45]);
  expect result == [45], "impl test 14 failed";

  // Test 15
  result := FavoriteSequence([46]);
  expect result == [46], "impl test 15 failed";

  // Test 16
  result := FavoriteSequence([47]);
  expect result == [47], "impl test 16 failed";

  // Test 17
  result := FavoriteSequence([97]);
  expect result == [97], "impl test 17 failed";

  // Test 18
  result := FavoriteSequence([98]);
  expect result == [98], "impl test 18 failed";

  // Test 19
  result := FavoriteSequence([99]);
  expect result == [99], "impl test 19 failed";

  print "All tests passed\n";
}