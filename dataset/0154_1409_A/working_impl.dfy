method MinMoves(a: int, b: int) returns (moves: int)
{
  var lo := a;
  var hi := b;
  if lo > hi {
    lo := b;
    hi := a;
  }
  var diff := hi - lo;
  moves := diff / 10;
  if diff % 10 != 0 {
    moves := moves + 1;
  }
}

method Main()
{
  var result: int;

  // (5, 5) -> 0
  result := MinMoves(5, 5);
  expect result == 0, "MinMoves(5, 5) failed";

  // (13, 42) -> 3
  result := MinMoves(13, 42);
  expect result == 3, "MinMoves(13, 42) failed";

  // (18, 4) -> 2
  result := MinMoves(18, 4);
  expect result == 2, "MinMoves(18, 4) failed";

  // (1337, 420) -> 92
  result := MinMoves(1337, 420);
  expect result == 92, "MinMoves(1337, 420) failed";

  // (123456789, 1000000000) -> 87654322
  result := MinMoves(123456789, 1000000000);
  expect result == 87654322, "MinMoves(123456789, 1000000000) failed";

  // (100500, 9000) -> 9150
  result := MinMoves(100500, 9000);
  expect result == 9150, "MinMoves(100500, 9000) failed";

  // (2, 2) -> 0
  result := MinMoves(2, 2);
  expect result == 0, "MinMoves(2, 2) failed";

  // (7, 7) -> 0
  result := MinMoves(7, 7);
  expect result == 0, "MinMoves(7, 7) failed";

  // (3, 3) -> 0
  result := MinMoves(3, 3);
  expect result == 0, "MinMoves(3, 3) failed";

  print "All tests passed\n";
}