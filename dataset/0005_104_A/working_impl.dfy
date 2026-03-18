method Blackjack(n: int) returns (ways: int)
{
  var vals: seq<seq<int>> := [[10], [2], [3], [4], [5], [6], [7], [8], [9], [10], [10], [10], [1, 11]];

  ways := 0;
  var i := 0;
  while i < |vals|
  {
    var x := vals[i];
    var j := 0;
    while j < |x|
    {
      var y := x[j];
      if y + 10 == n {
        ways := ways + 3;
        if i != 0 {
          ways := ways + 1;
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return;
}

method Main()
{
  var result: int;

  result := Blackjack(12);
  expect result == 4, "Test 1 failed";

  result := Blackjack(20);
  expect result == 15, "Test 2 failed";

  result := Blackjack(10);
  expect result == 0, "Test 3 failed";

  result := Blackjack(11);
  expect result == 4, "Test 4 failed";

  result := Blackjack(15);
  expect result == 4, "Test 5 failed";

  result := Blackjack(18);
  expect result == 4, "Test 6 failed";

  result := Blackjack(25);
  expect result == 0, "Test 7 failed";

  result := Blackjack(22);
  expect result == 0, "Test 8 failed";

  result := Blackjack(1);
  expect result == 0, "Test 9 failed";

  result := Blackjack(2);
  expect result == 0, "Test 10 failed";

  result := Blackjack(3);
  expect result == 0, "Test 11 failed";

  result := Blackjack(4);
  expect result == 0, "Test 12 failed";

  result := Blackjack(5);
  expect result == 0, "Test 13 failed";

  result := Blackjack(6);
  expect result == 0, "Test 14 failed";

  result := Blackjack(7);
  expect result == 0, "Test 15 failed";

  result := Blackjack(8);
  expect result == 0, "Test 16 failed";

  result := Blackjack(9);
  expect result == 0, "Test 17 failed";

  result := Blackjack(13);
  expect result == 4, "Test 18 failed";

  result := Blackjack(14);
  expect result == 4, "Test 19 failed";

  result := Blackjack(16);
  expect result == 4, "Test 20 failed";

  print "All tests passed\n";
}