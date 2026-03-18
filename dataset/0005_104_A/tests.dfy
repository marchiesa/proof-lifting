// --- Specification ---

function FacePoints(face: int): seq<int>
  requires 0 <= face <= 12
{
  if face <= 8 then [face + 2]
  else if face <= 11 then [10]
  else [1, 11]
}

predicate CanScore(face: int, p: int)
  requires 0 <= face <= 12
{
  exists k | 0 <= k < |FacePoints(face)| :: FacePoints(face)[k] == p
}

function SuitsAvailable(face: int): int
  requires 0 <= face <= 12
{
  if face == 10 then 3 else 4
}

function AllFaces(): seq<int>
{
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
}

function CountWinningCards(n: int, faces: seq<int>): int
  decreases |faces|
{
  if |faces| == 0 then 0
  else
    var face := faces[|faces| - 1];
    var rest := CountWinningCards(n, faces[..|faces| - 1]);
    if 0 <= face <= 12 && CanScore(face, n - 10)
    then rest + SuitsAvailable(face)
    else rest
}

function ExpectedWays(n: int): int
{
  CountWinningCards(n, AllFaces())
}

// --- Implementation ---

method Blackjack(n: int) returns (ways: int)
  ensures ways == ExpectedWays(n)
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

// --- Tests ---

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // ensures: ways == ExpectedWays(n)
  // Test that ExpectedWays(input) == correct_output
  expect ExpectedWays(12) == 4, "spec positive 1";
  expect ExpectedWays(20) == 15, "spec positive 2";
  expect ExpectedWays(10) == 0, "spec positive 3";
  expect ExpectedWays(11) == 4, "spec positive 4";
  expect ExpectedWays(15) == 4, "spec positive 5";
  expect ExpectedWays(18) == 4, "spec positive 6";
  expect ExpectedWays(25) == 0, "spec positive 7";
  expect ExpectedWays(22) == 0, "spec positive 8";
  expect ExpectedWays(1) == 0, "spec positive 9";
  expect ExpectedWays(2) == 0, "spec positive 10";

  // === SPEC NEGATIVE TESTS ===
  // Test that ExpectedWays(input) != wrong_output
  expect !(ExpectedWays(12) == 5), "spec negative 1";
  expect !(ExpectedWays(20) == 16), "spec negative 2";
  expect !(ExpectedWays(10) == 1), "spec negative 3";
  expect !(ExpectedWays(11) == 5), "spec negative 4";
  expect !(ExpectedWays(15) == 5), "spec negative 5";
  expect !(ExpectedWays(18) == 5), "spec negative 6";
  expect !(ExpectedWays(25) == 1), "spec negative 7";
  expect !(ExpectedWays(22) == 1), "spec negative 8";
  expect !(ExpectedWays(1) == 1), "spec negative 9";
  expect !(ExpectedWays(2) == 1), "spec negative 10";

  // === IMPLEMENTATION TESTS ===
  var result: int;

  result := Blackjack(12);
  expect result == 4, "impl test 1 failed";

  result := Blackjack(20);
  expect result == 15, "impl test 2 failed";

  result := Blackjack(10);
  expect result == 0, "impl test 3 failed";

  result := Blackjack(11);
  expect result == 4, "impl test 4 failed";

  result := Blackjack(15);
  expect result == 4, "impl test 5 failed";

  result := Blackjack(18);
  expect result == 4, "impl test 6 failed";

  result := Blackjack(25);
  expect result == 0, "impl test 7 failed";

  result := Blackjack(22);
  expect result == 0, "impl test 8 failed";

  result := Blackjack(1);
  expect result == 0, "impl test 9 failed";

  result := Blackjack(2);
  expect result == 0, "impl test 10 failed";

  print "All tests passed\n";
}