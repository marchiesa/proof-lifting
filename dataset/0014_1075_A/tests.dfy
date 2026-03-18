// ── Helper functions ──

function Abs(x: int): int
{ if x >= 0 then x else -x }

function Max(a: int, b: int): int
{ if a >= b then a else b }

// ── Problem formalization ──

function ChebyshevDist(r1: int, c1: int, r2: int, c2: int): int
{ Max(Abs(r1 - r2), Abs(c1 - c2)) }

predicate ValidKingStep(r1: int, c1: int, r2: int, c2: int, n: int)
{
  1 <= r1 <= n && 1 <= c1 <= n &&
  1 <= r2 <= n && 1 <= c2 <= n &&
  Abs(r1 - r2) <= 1 && Abs(c1 - c2) <= 1 &&
  (r1 != r2 || c1 != c2)
}

function StepToward(r: int, c: int, tr: int, tc: int): (int, int)
{
  (r + (if tr > r then 1 else if tr < r then -1 else 0),
   c + (if tc > c then 1 else if tc < c then -1 else 0))
}

predicate GreedyStepValid(r: int, c: int, tr: int, tc: int, n: int)
{
  1 <= r <= n && 1 <= c <= n && 1 <= tr <= n && 1 <= tc <= n &&
  ((r == tr && c == tc)
   ||
   (var p := StepToward(r, c, tr, tc);
    ValidKingStep(r, c, p.0, p.1, n) &&
    ChebyshevDist(p.0, p.1, tr, tc) == ChebyshevDist(r, c, tr, tc) - 1))
}

predicate NoStepReducesByMoreThanOne(r: int, c: int, tr: int, tc: int)
{
  forall dr | -1 <= dr <= 1 ::
    forall dc | -1 <= dc <= 1 ::
      ChebyshevDist(r + dr, c + dc, tr, tc) >= ChebyshevDist(r, c, tr, tc) - 1
}

function ArrivalTurn(dist: int, movesFirst: bool): int
{
  if dist == 0 then 0
  else if movesFirst then 2 * dist - 1
  else 2 * dist
}

predicate CorrectWinner(winner: string, n: int, x: int, y: int)
  requires n >= 2 && 1 <= x <= n && 1 <= y <= n
{
  var whiteDist := ChebyshevDist(1, 1, x, y);
  var blackDist := ChebyshevDist(n, n, x, y);
  var whiteTurn := ArrivalTurn(whiteDist, true);
  var blackTurn := ArrivalTurn(blackDist, false);
  (winner == "White" <==> whiteTurn <= blackTurn) &&
  (winner == "Black" <==> whiteTurn > blackTurn)
}

// ── Method with specification ──

method KingsRace(n: int, x: int, y: int) returns (winner: string)
  requires n >= 2 && 1 <= x <= n && 1 <= y <= n
  ensures CorrectWinner(winner, n, x, y)
  ensures GreedyStepValid(1, 1, x, y, n)
  ensures GreedyStepValid(n, n, x, y, n)
  ensures NoStepReducesByMoreThanOne(1, 1, x, y)
  ensures NoStepReducesByMoreThanOne(n, n, x, y)
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
  // ============================================================
  // (a) SPEC POSITIVE tests — ensures predicates with correct output
  // ============================================================

  // Test 1: n=4, x=2, y=3, winner="White"
  expect CorrectWinner("White", 4, 2, 3), "spec pos 1a";
  expect GreedyStepValid(1, 1, 2, 3, 4), "spec pos 1b";
  expect GreedyStepValid(4, 4, 2, 3, 4), "spec pos 1c";
  expect NoStepReducesByMoreThanOne(1, 1, 2, 3), "spec pos 1d";
  expect NoStepReducesByMoreThanOne(4, 4, 2, 3), "spec pos 1e";

  // Test 2: n=5, x=3, y=5, winner="Black"
  expect CorrectWinner("Black", 5, 3, 5), "spec pos 2a";
  expect GreedyStepValid(1, 1, 3, 5, 5), "spec pos 2b";
  expect GreedyStepValid(5, 5, 3, 5, 5), "spec pos 2c";
  expect NoStepReducesByMoreThanOne(1, 1, 3, 5), "spec pos 2d";
  expect NoStepReducesByMoreThanOne(5, 5, 3, 5), "spec pos 2e";

  // Test 3: n=2, x=2, y=2, winner="Black"
  expect CorrectWinner("Black", 2, 2, 2), "spec pos 3a";
  expect GreedyStepValid(1, 1, 2, 2, 2), "spec pos 3b";
  expect GreedyStepValid(2, 2, 2, 2, 2), "spec pos 3c";
  expect NoStepReducesByMoreThanOne(1, 1, 2, 2), "spec pos 3d";
  expect NoStepReducesByMoreThanOne(2, 2, 2, 2), "spec pos 3e";

  // Test 4: n=10^18, x=10^18, y=10^18, winner="Black"
  expect CorrectWinner("Black", 1000000000000000000, 1000000000000000000, 1000000000000000000), "spec pos 4a";
  expect GreedyStepValid(1, 1, 1000000000000000000, 1000000000000000000, 1000000000000000000), "spec pos 4b";
  expect GreedyStepValid(1000000000000000000, 1000000000000000000, 1000000000000000000, 1000000000000000000, 1000000000000000000), "spec pos 4c";
  expect NoStepReducesByMoreThanOne(1, 1, 1000000000000000000, 1000000000000000000), "spec pos 4d";
  expect NoStepReducesByMoreThanOne(1000000000000000000, 1000000000000000000, 1000000000000000000, 1000000000000000000), "spec pos 4e";

  // Test 5: n=10^18, x=1, y=1, winner="White"
  expect CorrectWinner("White", 1000000000000000000, 1, 1), "spec pos 5a";
  expect GreedyStepValid(1, 1, 1, 1, 1000000000000000000), "spec pos 5b";
  expect GreedyStepValid(1000000000000000000, 1000000000000000000, 1, 1, 1000000000000000000), "spec pos 5c";
  expect NoStepReducesByMoreThanOne(1, 1, 1, 1), "spec pos 5d";
  expect NoStepReducesByMoreThanOne(1000000000000000000, 1000000000000000000, 1, 1), "spec pos 5e";

  // Test 6: n=2, x=1, y=1, winner="White"
  expect CorrectWinner("White", 2, 1, 1), "spec pos 6a";
  expect GreedyStepValid(1, 1, 1, 1, 2), "spec pos 6b";
  expect GreedyStepValid(2, 2, 1, 1, 2), "spec pos 6c";
  expect NoStepReducesByMoreThanOne(1, 1, 1, 1), "spec pos 6d";
  expect NoStepReducesByMoreThanOne(2, 2, 1, 1), "spec pos 6e";

  // Test 7: n=1234567890123456, x=1234567889969697, y=153760, winner="White"
  expect CorrectWinner("White", 1234567890123456, 1234567889969697, 153760), "spec pos 7a";
  expect GreedyStepValid(1, 1, 1234567889969697, 153760, 1234567890123456), "spec pos 7b";
  expect GreedyStepValid(1234567890123456, 1234567890123456, 1234567889969697, 153760, 1234567890123456), "spec pos 7c";
  expect NoStepReducesByMoreThanOne(1, 1, 1234567889969697, 153760), "spec pos 7d";
  expect NoStepReducesByMoreThanOne(1234567890123456, 1234567890123456, 1234567889969697, 153760), "spec pos 7e";

  // Test 8: n=12000000000000, x=123056, y=11999999876946, winner="Black"
  expect CorrectWinner("Black", 12000000000000, 123056, 11999999876946), "spec pos 8a";
  expect GreedyStepValid(1, 1, 123056, 11999999876946, 12000000000000), "spec pos 8b";
  expect GreedyStepValid(12000000000000, 12000000000000, 123056, 11999999876946, 12000000000000), "spec pos 8c";
  expect NoStepReducesByMoreThanOne(1, 1, 123056, 11999999876946), "spec pos 8d";
  expect NoStepReducesByMoreThanOne(12000000000000, 12000000000000, 123056, 11999999876946), "spec pos 8e";

  // Test 9: n=839105509657869903, x=591153401407154876, y=258754952987011519, winner="Black"
  expect CorrectWinner("Black", 839105509657869903, 591153401407154876, 258754952987011519), "spec pos 9a";
  expect GreedyStepValid(1, 1, 591153401407154876, 258754952987011519, 839105509657869903), "spec pos 9b";
  expect GreedyStepValid(839105509657869903, 839105509657869903, 591153401407154876, 258754952987011519, 839105509657869903), "spec pos 9c";
  expect NoStepReducesByMoreThanOne(1, 1, 591153401407154876, 258754952987011519), "spec pos 9d";
  expect NoStepReducesByMoreThanOne(839105509657869903, 839105509657869903, 591153401407154876, 258754952987011519), "spec pos 9e";

  // Test 10: n=778753534913338583, x=547836868672081726, y=265708022656451521, winner="Black"
  expect CorrectWinner("Black", 778753534913338583, 547836868672081726, 265708022656451521), "spec pos 10a";
  expect GreedyStepValid(1, 1, 547836868672081726, 265708022656451521, 778753534913338583), "spec pos 10b";
  expect GreedyStepValid(778753534913338583, 778753534913338583, 547836868672081726, 265708022656451521, 778753534913338583), "spec pos 10c";
  expect NoStepReducesByMoreThanOne(1, 1, 547836868672081726, 265708022656451521), "spec pos 10d";
  expect NoStepReducesByMoreThanOne(778753534913338583, 778753534913338583, 547836868672081726, 265708022656451521), "spec pos 10e";

  // ============================================================
  // (b) SPEC NEGATIVE tests — CorrectWinner must reject wrong outputs
  // ============================================================

  expect !CorrectWinner("White WRONG", 4, 2, 3), "spec neg 1";
  expect !CorrectWinner("Black WRONG", 5, 3, 5), "spec neg 2";
  expect !CorrectWinner("Black WRONG", 2, 2, 2), "spec neg 3";
  expect !CorrectWinner("Black WRONG", 1000000000000000000, 1000000000000000000, 1000000000000000000), "spec neg 4";
  expect !CorrectWinner("White WRONG", 1000000000000000000, 1, 1), "spec neg 5";
  expect !CorrectWinner("White WRONG", 2, 1, 1), "spec neg 6";
  expect !CorrectWinner("White WRONG", 1234567890123456, 1234567889969697, 153760), "spec neg 7";
  expect !CorrectWinner("Black WRONG", 12000000000000, 123056, 11999999876946), "spec neg 8";
  expect !CorrectWinner("Black WRONG", 839105509657869903, 591153401407154876, 258754952987011519), "spec neg 9";
  expect !CorrectWinner("Black WRONG", 778753534913338583, 547836868672081726, 265708022656451521), "spec neg 10";

  // ============================================================
  // (c) IMPLEMENTATION tests — call KingsRace and check output
  // ============================================================

  var result: string;

  result := KingsRace(4, 2, 3);
  expect result == "White", "impl test 1 failed";

  result := KingsRace(5, 3, 5);
  expect result == "Black", "impl test 2 failed";

  result := KingsRace(2, 2, 2);
  expect result == "Black", "impl test 3 failed";

  result := KingsRace(1000000000000000000, 1000000000000000000, 1000000000000000000);
  expect result == "Black", "impl test 4 failed";

  result := KingsRace(1000000000000000000, 1, 1);
  expect result == "White", "impl test 5 failed";

  result := KingsRace(2, 1, 1);
  expect result == "White", "impl test 6 failed";

  result := KingsRace(1234567890123456, 1234567889969697, 153760);
  expect result == "White", "impl test 7 failed";

  result := KingsRace(12000000000000, 123056, 11999999876946);
  expect result == "Black", "impl test 8 failed";

  result := KingsRace(839105509657869903, 591153401407154876, 258754952987011519);
  expect result == "Black", "impl test 9 failed";

  result := KingsRace(778753534913338583, 547836868672081726, 265708022656451521);
  expect result == "Black", "impl test 10 failed";

  result := KingsRace(521427324217141769, 375108452493312817, 366738689404083861);
  expect result == "Black", "impl test 11 failed";

  result := KingsRace(1000000000000000, 208171971446456, 791828028553545);
  expect result == "White", "impl test 12 failed";

  result := KingsRace(719386363530333627, 620916440917452264, 265151985453132665);
  expect result == "Black", "impl test 13 failed";

  result := KingsRace(57719663734394834, 53160177030140966, 26258927428764347);
  expect result == "Black", "impl test 14 failed";

  result := KingsRace(835610886713350713, 31708329050069500, 231857821534629883);
  expect result == "White", "impl test 15 failed";

  result := KingsRace(17289468142098094, 4438423217327361, 4850647042283952);
  expect result == "White", "impl test 16 failed";

  result := KingsRace(562949953421312, 259798251531825, 508175017145903);
  expect result == "Black", "impl test 17 failed";

  result := KingsRace(9007199254740992, 7977679390099527, 3015199451140672);
  expect result == "Black", "impl test 18 failed";

  result := KingsRace(982837494536444311, 471939396014493192, 262488194864680421);
  expect result == "White", "impl test 19 failed";

  result := KingsRace(878602530892252875, 583753601575252768, 851813862933314387);
  expect result == "Black", "impl test 20 failed";

  // ============================================================
  // (d) Done
  // ============================================================
  print "All tests passed\n";
}