// ── Spec (functions / predicates) ──────────────────────────────────────

function MatchWinner(a: int, b: int): int {
  if a > b then a else b
}

function CountGreater(v: int, s1: int, s2: int, s3: int, s4: int): int {
  (if s1 > v then 1 else 0) + (if s2 > v then 1 else 0) +
  (if s3 > v then 1 else 0) + (if s4 > v then 1 else 0)
}

predicate IsTopTwo(v: int, s1: int, s2: int, s3: int, s4: int) {
  CountGreater(v, s1, s2, s3, s4) <= 1
}

predicate FairTournament(s1: int, s2: int, s3: int, s4: int) {
  IsTopTwo(MatchWinner(s1, s2), s1, s2, s3, s4) &&
  IsTopTwo(MatchWinner(s3, s4), s1, s2, s3, s4)
}

// ── Implementation ─────────────────────────────────────────────────────

method FairPlayoff(s1: int, s2: int, s3: int, s4: int) returns (fair: bool)
  requires s1 != s2 && s1 != s3 && s1 != s4 && s2 != s3 && s2 != s4 && s3 != s4
  ensures fair == FairTournament(s1, s2, s3, s4)
{
  var min12 := if s1 < s2 then s1 else s2;
  var max12 := if s1 > s2 then s1 else s2;
  var min34 := if s3 < s4 then s3 else s4;
  var max34 := if s3 > s4 then s3 else s4;

  if min34 > max12 || min12 > max34 {
    fair := false;
  } else {
    fair := true;
  }
}

// ── Tests ──────────────────────────────────────────────────────────────

method Main()
{
  // ====== (a) SPEC POSITIVE tests ======
  // FairTournament(s1,s2,s3,s4) == expected
  expect FairTournament(3, 7, 9, 5) == true,   "spec positive 1a";
  expect FairTournament(4, 5, 6, 9) == false,  "spec positive 1b";
  expect FairTournament(5, 3, 8, 1) == true,   "spec positive 1c";
  expect FairTournament(6, 5, 3, 2) == false,  "spec positive 1d";
  expect FairTournament(8, 6, 2, 7) == true,   "spec positive 2";
  expect FairTournament(3, 7, 9, 5) == true,   "spec positive 3";
  expect FairTournament(4, 5, 6, 9) == false,  "spec positive 4";
  expect FairTournament(5, 3, 8, 1) == true,   "spec positive 5";
  expect FairTournament(6, 5, 3, 2) == false,  "spec positive 6";
  expect FairTournament(1, 2, 3, 4) == false,  "spec positive 7";
  expect FairTournament(10, 20, 30, 40) == false, "spec positive 8";
  expect FairTournament(7, 3, 2, 8) == true,   "spec positive 9";
  expect FairTournament(50, 40, 30, 20) == false, "spec positive 10";

  // ====== (b) SPEC NEGATIVE tests ======
  // wrong output must NOT match FairTournament
  // Neg 2: (8,6,2,7) wrong=false, correct=true
  expect !(false == FairTournament(8, 6, 2, 7)),  "spec negative 2";
  // Neg 3: (3,7,9,5) wrong=false, correct=true
  expect !(false == FairTournament(3, 7, 9, 5)),   "spec negative 3";
  // Neg 4: (4,5,6,9) wrong=true, correct=false
  expect !(true == FairTournament(4, 5, 6, 9)),    "spec negative 4";
  // Neg 5: (5,3,8,1) wrong=false, correct=true
  expect !(false == FairTournament(5, 3, 8, 1)),   "spec negative 5";
  // Neg 6: (6,5,3,2) wrong=true, correct=false
  expect !(true == FairTournament(6, 5, 3, 2)),    "spec negative 6";
  // Neg 7: (1,2,3,4) wrong=true, correct=false
  expect !(true == FairTournament(1, 2, 3, 4)),    "spec negative 7";
  // Neg 8: (10,20,30,40) wrong=true, correct=false
  expect !(true == FairTournament(10, 20, 30, 40)), "spec negative 8";
  // Neg 9: (7,3,2,8) wrong=false, correct=true
  expect !(false == FairTournament(7, 3, 2, 8)),   "spec negative 9";
  // Neg 10: (50,40,30,20) wrong=true, correct=false
  expect !(true == FairTournament(50, 40, 30, 20)), "spec negative 10";

  // ====== (c) IMPLEMENTATION tests ======
  var r: bool;

  r := FairPlayoff(3, 7, 9, 5);
  expect r == true, "impl test 1a";

  r := FairPlayoff(4, 5, 6, 9);
  expect r == false, "impl test 1b";

  r := FairPlayoff(5, 3, 8, 1);
  expect r == true, "impl test 1c";

  r := FairPlayoff(6, 5, 3, 2);
  expect r == false, "impl test 1d";

  r := FairPlayoff(8, 6, 2, 7);
  expect r == true, "impl test 2";

  r := FairPlayoff(1, 2, 3, 4);
  expect r == false, "impl test 7";

  r := FairPlayoff(10, 20, 30, 40);
  expect r == false, "impl test 8";

  r := FairPlayoff(7, 3, 2, 8);
  expect r == true, "impl test 9";

  r := FairPlayoff(50, 40, 30, 20);
  expect r == false, "impl test 10";

  r := FairPlayoff(1, 3, 2, 4);
  expect r == true, "impl test 11a";

  r := FairPlayoff(5, 10, 15, 20);
  expect r == false, "impl test 11b";

  r := FairPlayoff(8, 2, 6, 4);
  expect r == true, "impl test 11c";

  r := FairPlayoff(1, 4, 2, 3);
  expect r == true, "impl test 12a";

  r := FairPlayoff(9, 7, 5, 3);
  expect r == false, "impl test 12b";

  r := FairPlayoff(2, 8, 6, 4);
  expect r == true, "impl test 12c";

  r := FairPlayoff(10, 1, 5, 3);
  expect r == true, "impl test 12d";

  r := FairPlayoff(7, 3, 9, 1);
  expect r == true, "impl test 12e";

  print "All tests passed\n";
}