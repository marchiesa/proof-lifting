function CategoryRank(hp: int): int
  requires hp >= 1
{
  var r := hp % 4;
  if r == 1 then 3
  else if r == 3 then 2
  else if r == 2 then 1
  else 0
}

function CategoryChar(hp: int): char
  requires hp >= 1
{
  var r := hp % 4;
  if r == 1 then 'A'
  else if r == 3 then 'B'
  else if r == 2 then 'C'
  else 'D'
}

predicate IsValidResult(x: int, a: int, b: char)
  requires x >= 1
{
  && 0 <= a <= 2
  && b == CategoryChar(x + a)
  && (forall delta | 0 <= delta <= 2 :: CategoryRank(x + delta) <= CategoryRank(x + a))
  && (forall delta | 0 <= delta < a :: CategoryRank(x + delta) < CategoryRank(x + a))
}

method TokitsukazeAndEnhancement(x: int) returns (a: int, b: char)
  requires x >= 1
  ensures 0 <= a <= 2
  ensures b == CategoryChar(x + a)
  ensures forall delta | 0 <= delta <= 2 :: CategoryRank(x + delta) <= CategoryRank(x + a)
  ensures forall delta | 0 <= delta < a :: CategoryRank(x + delta) < CategoryRank(x + a)
{
  var r := x % 4;
  if r == 0 {
    a := 1;
    b := 'A';
  } else if r == 1 {
    a := 0;
    b := 'A';
  } else if r == 2 {
    a := 1;
    b := 'B';
  } else {
    a := 2;
    b := 'A';
  }
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  expect IsValidResult(33, 0, 'A'), "spec positive 1";
  expect IsValidResult(98, 1, 'B'), "spec positive 2";
  expect IsValidResult(100, 1, 'A'), "spec positive 3";
  expect IsValidResult(30, 1, 'B'), "spec positive 4";
  expect IsValidResult(43, 2, 'A'), "spec positive 5";
  expect IsValidResult(85, 0, 'A'), "spec positive 6";
  expect IsValidResult(91, 2, 'A'), "spec positive 7";
  expect IsValidResult(50, 1, 'B'), "spec positive 8";
  expect IsValidResult(67, 2, 'A'), "spec positive 9";
  expect IsValidResult(95, 2, 'A'), "spec positive 10";

  // === SPEC NEGATIVE TESTS ===
  expect !IsValidResult(33, 1, 'A'), "spec negative 1";
  expect !IsValidResult(98, 2, 'B'), "spec negative 2";
  expect !IsValidResult(100, 2, 'A'), "spec negative 3";
  expect !IsValidResult(30, 2, 'B'), "spec negative 4";
  expect !IsValidResult(43, 3, 'A'), "spec negative 5";
  expect !IsValidResult(85, 1, 'A'), "spec negative 6";
  expect !IsValidResult(91, 3, 'A'), "spec negative 7";
  expect !IsValidResult(50, 2, 'B'), "spec negative 8";
  expect !IsValidResult(67, 3, 'A'), "spec negative 9";
  expect !IsValidResult(95, 3, 'A'), "spec negative 10";

  // === IMPLEMENTATION TESTS ===
  var a: int;
  var b: char;

  a, b := TokitsukazeAndEnhancement(33);
  expect a == 0 && b == 'A', "impl test 1 failed";

  a, b := TokitsukazeAndEnhancement(98);
  expect a == 1 && b == 'B', "impl test 2 failed";

  a, b := TokitsukazeAndEnhancement(100);
  expect a == 1 && b == 'A', "impl test 3 failed";

  a, b := TokitsukazeAndEnhancement(30);
  expect a == 1 && b == 'B', "impl test 4 failed";

  a, b := TokitsukazeAndEnhancement(43);
  expect a == 2 && b == 'A', "impl test 5 failed";

  a, b := TokitsukazeAndEnhancement(85);
  expect a == 0 && b == 'A', "impl test 6 failed";

  a, b := TokitsukazeAndEnhancement(91);
  expect a == 2 && b == 'A', "impl test 7 failed";

  a, b := TokitsukazeAndEnhancement(50);
  expect a == 1 && b == 'B', "impl test 8 failed";

  a, b := TokitsukazeAndEnhancement(67);
  expect a == 2 && b == 'A', "impl test 9 failed";

  a, b := TokitsukazeAndEnhancement(95);
  expect a == 2 && b == 'A', "impl test 10 failed";

  print "All tests passed\n";
}