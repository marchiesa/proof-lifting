function Delta(c: char): int
{
  if c == '-' then -1 else 1
}

function SumDeltas(s: seq<char>): int
  decreases |s|
{
  if |s| == 0 then 0
  else SumDeltas(s[..|s|-1]) + Delta(s[|s|-1])
}

predicate ValidExecution(s: seq<char>, init: int)
{
  init >= 0 &&
  forall k | 0 <= k <= |s| :: init + SumDeltas(s[..k]) >= 0
}

function FinalPileSize(s: seq<char>, init: int): int
{
  init + SumDeltas(s)
}

// Combined top-level ensures predicate
predicate MeetsSpec(s: seq<char>, result: int)
{
  (exists init | 0 <= init <= |s| :: ValidExecution(s, init) && FinalPileSize(s, init) == result) &&
  (forall init | 0 <= init <= |s| :: ValidExecution(s, init) ==> FinalPileSize(s, init) >= result)
}

method PileOfStones(s: seq<char>) returns (result: int)
  ensures exists init | 0 <= init <= |s| :: ValidExecution(s, init) && FinalPileSize(s, init) == result
  ensures forall init | 0 <= init <= |s| :: ValidExecution(s, init) ==> FinalPileSize(s, init) >= result
{
  result := 0;
  var i := 0;
  while i < |s|
  {
    if s[i] == '-' {
      if result > 0 {
        result := result - 1;
      }
    } else {
      result := result + 1;
    }
    i := i + 1;
  }
}

method Main()
{
  var r: int;

  // === SPEC POSITIVE TESTS ===
  // Small inputs (length 1-3) to keep bounded quantifier evaluation fast.

  // Scaled from Test 1 ("---" -> 0): "-" -> 0
  expect MeetsSpec("-", 0), "spec positive 1";
  // Scaled from Test 2 ("++++" -> 4): "+" -> 1
  expect MeetsSpec("+", 1), "spec positive 2";
  // Test 3: "-+" -> 1 (already small)
  expect MeetsSpec("-+", 1), "spec positive 3";
  // Scaled from Test 4 ("++-++" -> 3): "++" -> 2
  expect MeetsSpec("++", 2), "spec positive 4";
  // Scaled from Test 7 ("---...---" -> 0): "--" -> 0
  expect MeetsSpec("--", 0), "spec positive 5";
  // Additional small: "+-" -> 0
  expect MeetsSpec("+-", 0), "spec positive 6";
  // Additional small: "+++" -> 3
  expect MeetsSpec("+++", 3), "spec positive 7";
  // Additional small: "-+-" -> 0
  expect MeetsSpec("-+-", 0), "spec positive 8";
  // Additional small: "+--" -> 0
  expect MeetsSpec("+--", 0), "spec positive 9";
  // Additional small: "+-+" -> 1
  expect MeetsSpec("+-+", 1), "spec positive 10";

  // === SPEC NEGATIVE TESTS ===
  // Small inputs with wrong outputs (each off by +1 from correct).

  // Scaled from Neg 1 ("---" wrong 1): "-" wrong 1
  expect !MeetsSpec("-", 1), "spec negative 1";
  // Scaled from Neg 2 ("++++" wrong 5): "+" wrong 2
  expect !MeetsSpec("+", 2), "spec negative 2";
  // Neg 3: "-+" wrong 2 (already small)
  expect !MeetsSpec("-+", 2), "spec negative 3";
  // Scaled from Neg 4 ("++-++" wrong 4): "++" wrong 3
  expect !MeetsSpec("++", 3), "spec negative 4";
  // Scaled from Neg 7 ("---...---" wrong 1): "--" wrong 1
  expect !MeetsSpec("--", 1), "spec negative 5";
  // Additional: "+-" wrong 1
  expect !MeetsSpec("+-", 1), "spec negative 6";
  // Additional: "+++" wrong 4
  expect !MeetsSpec("+++", 4), "spec negative 7";
  // Additional: "-+-" wrong 1
  expect !MeetsSpec("-+-", 1), "spec negative 8";
  // Additional: "+--" wrong 1
  expect !MeetsSpec("+--", 1), "spec negative 9";
  // Additional: "+-+" wrong 2
  expect !MeetsSpec("+-+", 2), "spec negative 10";

  // === IMPLEMENTATION TESTS ===
  // Full-size inputs — the method is fast.

  r := PileOfStones("---");
  expect r == 0, "impl test 1 failed";

  r := PileOfStones("++++");
  expect r == 4, "impl test 2 failed";

  r := PileOfStones("-+");
  expect r == 1, "impl test 3 failed";

  r := PileOfStones("++-++");
  expect r == 3, "impl test 4 failed";

  r := PileOfStones("+");
  expect r == 1, "impl test 5 failed";

  r := PileOfStones("++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++");
  expect r == 100, "impl test 6 failed";

  r := PileOfStones("----------------------------------------------------------------------------------------------------");
  expect r == 0, "impl test 7 failed";

  r := PileOfStones("-+-+-+-+-+-+-+-+-+-+-+-+-+-+++++++++++++++-++++++++++++++++++++++++++++++++++-++++++++++++++++++++++");
  expect r == 69, "impl test 8 failed";

  r := PileOfStones("+-+-+-++--++-++-+-+---+--++++++-++++--++-++---+--++++--+++++++-++-+--+-+-+--+-+++++-+--+---+-++-++-+");
  expect r == 17, "impl test 9 failed";

  r := PileOfStones("++-+-+-+-+++-++++--+++----+-+-+-------+-+-++--++--+-+++++---+-++---++-+-++---+--+-+-++-++-+---++-+--");
  expect r == 0, "impl test 10 failed";

  print "All tests passed\n";
}