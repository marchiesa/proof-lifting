predicate Reachable(a: int, b: int, n: int)
  decreases if n < 0 then 0 else n
{
  if n <= 0 then
    n == 0 && a == b
  else
    exists k | 1 <= k <= 10 ::
      Reachable(a + k, b, n - 1) || Reachable(a - k, b, n - 1)
}

predicate IsMinMoves(a: int, b: int, moves: int) {
  moves >= 0
  && Reachable(a, b, moves)
  && forall n | 0 <= n < moves :: !Reachable(a, b, n)
}

method MinMoves(a: int, b: int) returns (moves: int)
  ensures IsMinMoves(a, b, moves)
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

  // === Spec positive tests ===
  // Small cases used directly from test pairs
  expect IsMinMoves(5, 5, 0), "spec positive 1";     // from (5,5)->0
  expect IsMinMoves(2, 2, 0), "spec positive 2";     // from (2,2)->0
  expect IsMinMoves(7, 7, 0), "spec positive 3";     // from (7,7)->0
  expect IsMinMoves(3, 3, 0), "spec positive 4";     // from (3,3)->0
  expect IsMinMoves(18, 4, 2), "spec positive 5";    // from (18,4)->2
  expect IsMinMoves(13, 42, 3), "spec positive 6";   // from (13,42)->3
  // Scaled-down versions of large test pairs
  expect IsMinMoves(0, 2, 1), "spec positive 7";     // scaled from (1337,420)->92
  expect IsMinMoves(0, 5, 1), "spec positive 8";     // scaled from (123456789,1000000000)->87654322
  expect IsMinMoves(0, 10, 1), "spec positive 9";    // scaled from (100500,9000)->9150

  // === Spec negative tests ===
  // Each negative pair changed first output from 0 to 1
  expect !IsMinMoves(5, 5, 1), "spec negative 1";    // Neg 1: (5,5) wrong=1
  expect !IsMinMoves(5, 5, 1), "spec negative 2";    // Neg 2: (5,5) wrong=1
  expect !IsMinMoves(5, 5, 1), "spec negative 3";    // Neg 3: (5,5) wrong=1
  expect !IsMinMoves(5, 5, 1), "spec negative 4";    // Neg 4: (5,5) wrong=1
  expect !IsMinMoves(5, 5, 1), "spec negative 5";    // Neg 5: (5,5) wrong=1
  expect !IsMinMoves(2, 2, 1), "spec negative 6";    // Neg 6: (2,2) wrong=1
  expect !IsMinMoves(7, 7, 1), "spec negative 7";    // Neg 7: (7,7) wrong=1

  // === Implementation tests ===
  result := MinMoves(5, 5);
  expect result == 0, "impl test 1 failed";

  result := MinMoves(13, 42);
  expect result == 3, "impl test 2 failed";

  result := MinMoves(18, 4);
  expect result == 2, "impl test 3 failed";

  result := MinMoves(1337, 420);
  expect result == 92, "impl test 4 failed";

  result := MinMoves(123456789, 1000000000);
  expect result == 87654322, "impl test 5 failed";

  result := MinMoves(100500, 9000);
  expect result == 9150, "impl test 6 failed";

  result := MinMoves(2, 2);
  expect result == 0, "impl test 7 failed";

  result := MinMoves(7, 7);
  expect result == 0, "impl test 8 failed";

  result := MinMoves(3, 3);
  expect result == 0, "impl test 9 failed";

  print "All tests passed\n";
}