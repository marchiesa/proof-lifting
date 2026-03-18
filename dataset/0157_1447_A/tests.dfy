// --- Formal Specification: Add Candies Problem ---

function OperationGain(a: seq<int>, bag: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else OperationGain(a[..|a|-1], bag) + (if a[|a|-1] == bag then 0 else |a|)
}

function FinalCandies(n: int, a: seq<int>, bag: int): int
  requires 1 <= bag <= n
{
  bag + OperationGain(a, bag)
}

predicate AllBagsEqual(n: int, a: seq<int>)
  requires n >= 1
{
  forall i | 1 <= i <= n :: FinalCandies(n, a, i) == FinalCandies(n, a, 1)
}

predicate ValidChoices(n: int, a: seq<int>)
{
  forall j | 0 <= j < |a| :: 1 <= a[j] <= n
}

predicate ValidSolution(n: int, m: int, a: seq<int>)
  requires n >= 1
{
  1 <= m <= 1000 &&
  |a| == m &&
  ValidChoices(n, a) &&
  AllBagsEqual(n, a)
}

// --- Implementation ---

method AddCandies(n: int) returns (m: int, a: seq<int>)
  requires 1 <= n <= 1000
  ensures ValidSolution(n, m, a)
{
  m := n;
  a := [];
  var i := 1;
  while i <= n {
    a := a + [i];
    i := i + 1;
  }
}

method MakeSeq1ToN(n: int) returns (s: seq<int>)
{
  s := [];
  var i := 1;
  while i <= n {
    s := s + [i];
    i := i + 1;
  }
}

method Main() {
  // ======= SPEC POSITIVE TESTS =======
  // ValidSolution(n, m, a) with correct outputs, small n only

  // Test 1: n=2
  expect ValidSolution(2, 2, [1, 2]), "spec positive 1a";
  // Test 1: n=3
  expect ValidSolution(3, 3, [1, 2, 3]), "spec positive 1b";
  // Test 3: n=2
  expect ValidSolution(2, 2, [1, 2]), "spec positive 3";
  // Test 4: n=5
  expect ValidSolution(5, 5, [1, 2, 3, 4, 5]), "spec positive 4";
  // Test 6: n=2,3,4
  expect ValidSolution(2, 2, [1, 2]), "spec positive 6a";
  expect ValidSolution(3, 3, [1, 2, 3]), "spec positive 6b";
  expect ValidSolution(4, 4, [1, 2, 3, 4]), "spec positive 6c";
  // Test 7: n=10 (smallest sub-case)
  expect ValidSolution(10, 10, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]), "spec positive 7a";
  // Test 8: n=7
  expect ValidSolution(7, 7, [1, 2, 3, 4, 5, 6, 7]), "spec positive 8";
  // Test 9: n=3, n=6
  expect ValidSolution(3, 3, [1, 2, 3]), "spec positive 9a";
  expect ValidSolution(6, 6, [1, 2, 3, 4, 5, 6]), "spec positive 9b";
  // Test 10: n=2, n=5
  expect ValidSolution(2, 2, [1, 2]), "spec positive 10a";
  expect ValidSolution(5, 5, [1, 2, 3, 4, 5]), "spec positive 10b";
  // Test 12: n=2..7
  expect ValidSolution(2, 2, [1, 2]), "spec positive 12a";
  expect ValidSolution(3, 3, [1, 2, 3]), "spec positive 12b";
  expect ValidSolution(4, 4, [1, 2, 3, 4]), "spec positive 12c";
  expect ValidSolution(5, 5, [1, 2, 3, 4, 5]), "spec positive 12d";
  expect ValidSolution(6, 6, [1, 2, 3, 4, 5, 6]), "spec positive 12e";
  expect ValidSolution(7, 7, [1, 2, 3, 4, 5, 6, 7]), "spec positive 12f";

  // ======= SPEC NEGATIVE TESTS =======
  // ValidSolution(n, m_wrong, a) should be false

  // Neg 1: n=2, wrong m=3, a=[1,2]
  expect !ValidSolution(2, 3, [1, 2]), "spec negative 1";
  // Neg 3: n=2, wrong m=3, a=[1,2]
  expect !ValidSolution(2, 3, [1, 2]), "spec negative 3";
  // Neg 4: n=5, wrong m=6, a=[1,2,3,4,5]
  expect !ValidSolution(5, 6, [1, 2, 3, 4, 5]), "spec negative 4";
  // Neg 6: n=2, wrong m=3, a=[1,2]
  expect !ValidSolution(2, 3, [1, 2]), "spec negative 6";
  // Neg 7: n=10, wrong m=11, a=[1..10]
  expect !ValidSolution(10, 11, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]), "spec negative 7";
  // Neg 8: n=7, wrong m=8, a=[1..7]
  expect !ValidSolution(7, 8, [1, 2, 3, 4, 5, 6, 7]), "spec negative 8";
  // Neg 9: n=3, wrong m=4, a=[1,2,3]
  expect !ValidSolution(3, 4, [1, 2, 3]), "spec negative 9";
  // Neg 10: n=2, wrong m=3, a=[1,2]
  expect !ValidSolution(2, 3, [1, 2]), "spec negative 10";

  // ======= IMPLEMENTATION TESTS =======
  var m: int;
  var a: seq<int>;
  var expected: seq<int>;

  // Test 1: n=2, n=3
  m, a := AddCandies(2);
  expect m == 2 && a == [1, 2], "impl test 1a";
  m, a := AddCandies(3);
  expect m == 3 && a == [1, 2, 3], "impl test 1b";

  // Test 2: n=100, then n=2..100
  m, a := AddCandies(100);
  expected := MakeSeq1ToN(100);
  expect m == 100 && a == expected, "impl test 2a";
  var i := 2;
  while i <= 100 {
    m, a := AddCandies(i);
    expected := MakeSeq1ToN(i);
    expect m == i && a == expected, "impl test 2 loop";
    i := i + 1;
  }

  // Test 3: n=2
  m, a := AddCandies(2);
  expect m == 2 && a == [1, 2], "impl test 3";

  // Test 4: n=5
  m, a := AddCandies(5);
  expect m == 5 && a == [1, 2, 3, 4, 5], "impl test 4";

  // Test 5: n=100
  m, a := AddCandies(100);
  expected := MakeSeq1ToN(100);
  expect m == 100 && a == expected, "impl test 5";

  // Test 6: n=2,3,4
  m, a := AddCandies(2);
  expect m == 2 && a == [1, 2], "impl test 6a";
  m, a := AddCandies(3);
  expect m == 3 && a == [1, 2, 3], "impl test 6b";
  m, a := AddCandies(4);
  expect m == 4 && a == [1, 2, 3, 4], "impl test 6c";

  // Test 7: n=10,20,30,40,50
  m, a := AddCandies(10);
  expected := MakeSeq1ToN(10);
  expect m == 10 && a == expected, "impl test 7a";
  m, a := AddCandies(20);
  expected := MakeSeq1ToN(20);
  expect m == 20 && a == expected, "impl test 7b";
  m, a := AddCandies(30);
  expected := MakeSeq1ToN(30);
  expect m == 30 && a == expected, "impl test 7c";
  m, a := AddCandies(40);
  expected := MakeSeq1ToN(40);
  expect m == 40 && a == expected, "impl test 7d";
  m, a := AddCandies(50);
  expected := MakeSeq1ToN(50);
  expect m == 50 && a == expected, "impl test 7e";

  // Test 8: n=7
  m, a := AddCandies(7);
  expect m == 7 && a == [1, 2, 3, 4, 5, 6, 7], "impl test 8";

  // Test 9: n=3, n=6
  m, a := AddCandies(3);
  expect m == 3 && a == [1, 2, 3], "impl test 9a";
  m, a := AddCandies(6);
  expected := MakeSeq1ToN(6);
  expect m == 6 && a == expected, "impl test 9b";

  // Test 10: n=2,5,11,99
  m, a := AddCandies(2);
  expect m == 2 && a == [1, 2], "impl test 10a";
  m, a := AddCandies(5);
  expect m == 5 && a == [1, 2, 3, 4, 5], "impl test 10b";
  m, a := AddCandies(11);
  expected := MakeSeq1ToN(11);
  expect m == 11 && a == expected, "impl test 10c";
  m, a := AddCandies(99);
  expected := MakeSeq1ToN(99);
  expect m == 99 && a == expected, "impl test 10d";

  // Test 11: n=50
  m, a := AddCandies(50);
  expected := MakeSeq1ToN(50);
  expect m == 50 && a == expected, "impl test 11";

  // Test 12: n=2,3,4,5,6,7
  m, a := AddCandies(2);
  expect m == 2 && a == [1, 2], "impl test 12a";
  m, a := AddCandies(3);
  expect m == 3 && a == [1, 2, 3], "impl test 12b";
  m, a := AddCandies(4);
  expect m == 4 && a == [1, 2, 3, 4], "impl test 12c";
  m, a := AddCandies(5);
  expect m == 5 && a == [1, 2, 3, 4, 5], "impl test 12d";
  m, a := AddCandies(6);
  expected := MakeSeq1ToN(6);
  expect m == 6 && a == expected, "impl test 12e";
  m, a := AddCandies(7);
  expect m == 7 && a == [1, 2, 3, 4, 5, 6, 7], "impl test 12f";

  print "All tests passed\n";
}