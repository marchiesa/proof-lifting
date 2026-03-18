method UniqueBidAuction(a: seq<int>) returns (winner: int)
{
  winner := -1;
  var minVal := 0;
  var found := false;

  var i := 0;
  while i < |a|
  {
    var count := 0;
    var j := 0;
    while j < |a|
    {
      if a[j] == a[i] {
        count := count + 1;
      }
      j := j + 1;
    }
    if count == 1 && (!found || a[i] < minVal) {
      minVal := a[i];
      winner := i + 1;
      found := true;
    }
    i := i + 1;
  }
  return;
}

method Main()
{
  var r: int;

  // Test 1
  r := UniqueBidAuction([1, 1]);
  expect r == -1, "Test 1.1 failed";

  r := UniqueBidAuction([2, 1, 3]);
  expect r == 2, "Test 1.2 failed";

  r := UniqueBidAuction([2, 2, 2, 3]);
  expect r == 4, "Test 1.3 failed";

  r := UniqueBidAuction([1]);
  expect r == 1, "Test 1.4 failed";

  r := UniqueBidAuction([2, 3, 2, 4, 2]);
  expect r == 2, "Test 1.5 failed";

  r := UniqueBidAuction([1, 1, 5, 5, 4, 4]);
  expect r == -1, "Test 1.6 failed";

  // Test 2
  r := UniqueBidAuction([1, 1, 1, 3, 3, 3]);
  expect r == -1, "Test 2.1 failed";

  r := UniqueBidAuction([1, 1, 1, 3]);
  expect r == 4, "Test 2.2 failed";

  // Test 3
  r := UniqueBidAuction([16, 3, 11, 9, 3, 13, 11, 9, 14, 10, 10, 19, 19, 15, 11, 8, 8, 7, 3]);
  expect r == 18, "Test 3.1 failed";

  r := UniqueBidAuction([8, 6, 1, 4, 1, 4, 2, 9, 7, 10]);
  expect r == 7, "Test 3.2 failed";

  r := UniqueBidAuction([7, 1, 1, 4, 4, 1, 2]);
  expect r == 7, "Test 3.3 failed";

  r := UniqueBidAuction([1]);
  expect r == 1, "Test 3.4 failed";

  // Test 4
  r := UniqueBidAuction([10, 1, 3, 2, 11, 5, 12, 11, 12, 12, 9, 4]);
  expect r == 2, "Test 4.1 failed";

  r := UniqueBidAuction([10, 9, 7, 6, 6, 3, 8, 10, 1, 7, 9]);
  expect r == 9, "Test 4.2 failed";

  r := UniqueBidAuction([3, 11, 8, 9, 5, 9, 6, 5, 11, 12, 8, 7]);
  expect r == 1, "Test 4.3 failed";

  r := UniqueBidAuction([6, 6, 13, 12, 7, 6, 6, 7, 14, 7, 14, 13, 11, 3, 11]);
  expect r == 14, "Test 4.4 failed";

  r := UniqueBidAuction([31, 32, 2, 37, 19, 39, 21, 19, 24, 14, 17, 11, 33, 7, 17, 30, 33, 27, 16, 26, 37, 29, 19, 32, 20, 32, 24, 20, 20, 24, 32, 2, 7, 33, 30, 25, 23, 11, 35, 39]);
  expect r == 10, "Test 4.5 failed";

  r := UniqueBidAuction([11, 9, 16, 2, 10, 5, 10, 4, 13, 11, 8, 1, 13, 7, 4, 12]);
  expect r == 12, "Test 4.6 failed";

  r := UniqueBidAuction([7, 3, 24, 2, 18, 14, 41, 10, 43, 43, 12, 7, 11, 15, 4, 6, 22, 39, 11, 26, 14, 22, 4, 20, 39, 6, 22, 19, 37, 7, 6, 38, 10, 23, 39, 27, 37, 33, 30, 27, 24, 41, 33, 34, 3, 30]);
  expect r == 4, "Test 4.7 failed";

  r := UniqueBidAuction([1, 1, 2]);
  expect r == 3, "Test 4.8 failed";

  // Test 5
  r := UniqueBidAuction([1, 1]);
  expect r == -1, "Test 5.1 failed";

  r := UniqueBidAuction([1]);
  expect r == 1, "Test 5.2 failed";

  print "All tests passed\n";
}