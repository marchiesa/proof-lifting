// --- Formal specification for Mau-Mau card game ---

predicate IsRank(c: char)
{
  c in {'2', '3', '4', '5', '6', '7', '8', '9', 'T', 'J', 'Q', 'K', 'A'}
}

predicate IsSuit(c: char)
{
  c in {'D', 'C', 'S', 'H'}
}

predicate IsCard(s: string)
{
  |s| == 2 && IsRank(s[0]) && IsSuit(s[1])
}

predicate IsHand(hand: seq<string>)
{
  |hand| == 5 && forall i | 0 <= i < |hand| :: IsCard(hand[i])
}

function RankOf(card: string): char
  requires |card| >= 1
{
  card[0]
}

function SuitOf(card: string): char
  requires |card| >= 2
{
  card[1]
}

predicate IsPlayable(handCard: string, tableCard: string)
  requires |handCard| >= 2 && |tableCard| >= 2
{
  RankOf(handCard) == RankOf(tableCard) || SuitOf(handCard) == SuitOf(tableCard)
}

predicate HasPlayableCard(hand: seq<string>, tableCard: string)
  requires |tableCard| >= 2
  requires forall i | 0 <= i < |hand| :: |hand[i]| >= 2
{
  exists i | 0 <= i < |hand| :: IsPlayable(hand[i], tableCard)
}

method CardGame(table: string, hand: seq<string>) returns (canPlay: bool)
  requires IsCard(table)
  requires IsHand(hand)
  ensures canPlay == HasPlayableCard(hand, table)
{
  canPlay := false;
  var i := 0;
  while i < |hand|
  {
    if |hand[i]| >= 2 && |table| >= 2 {
      if hand[i][0] == table[0] || hand[i][1] == table[1] {
        canPlay := true;
        return;
      }
    }
    i := i + 1;
  }
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Top-level ensures predicate: HasPlayableCard(hand, table)
  // Scaled down to 1-3 card hands to keep bounded quantifier fast

  // Test 1: table="AS", AD matches rank A -> true
  expect HasPlayableCard(["2H", "AD"], "AS") == true, "spec positive 1";

  // Test 2: table="2H", no matches -> false
  expect HasPlayableCard(["3D", "4C", "AC"], "2H") == false, "spec positive 2";

  // Test 3: table="4D", AD matches suit D -> true
  expect HasPlayableCard(["AS", "AD"], "4D") == true, "spec positive 3";

  // Test 4: table="3D", no matches -> false
  expect HasPlayableCard(["8S", "4S", "2C"], "3D") == false, "spec positive 4";

  // Test 5: table="7H", no matches -> false
  expect HasPlayableCard(["TC", "4C", "KC"], "7H") == false, "spec positive 5";

  // Test 6: table="KH", KS matches rank K -> true
  expect HasPlayableCard(["3C", "KS"], "KH") == true, "spec positive 6";

  // Test 7: table="4H", JH matches suit H -> true
  expect HasPlayableCard(["JH"], "4H") == true, "spec positive 7";

  // Test 8: table="9H", no matches -> false
  expect HasPlayableCard(["KC", "6D", "KD"], "9H") == false, "spec positive 8";

  // Test 9: table="AD", no matches -> false
  expect HasPlayableCard(["QC", "5S", "4H"], "AD") == false, "spec positive 9";

  // Test 10: table="QC", QD matches rank Q -> true
  expect HasPlayableCard(["QD", "KS"], "QC") == true, "spec positive 10";

  // ===== SPEC NEGATIVE TESTS =====
  // Verify spec rejects the WRONG output for each negative test pair

  // Neg 1: table="AS", has match (AD). Wrong=false
  expect !(HasPlayableCard(["2H", "AD"], "AS") == false), "spec negative 1";

  // Neg 2: table="2H", no match. Wrong=true
  expect !(HasPlayableCard(["3D", "4C", "AC"], "2H") == true), "spec negative 2";

  // Neg 3: table="4D", has match (AD). Wrong=false
  expect !(HasPlayableCard(["AS", "AD"], "4D") == false), "spec negative 3";

  // Neg 4: table="3D", no match. Wrong=true
  expect !(HasPlayableCard(["8S", "4S", "2C"], "3D") == true), "spec negative 4";

  // Neg 5: table="7H", no match. Wrong=true
  expect !(HasPlayableCard(["TC", "4C", "KC"], "7H") == true), "spec negative 5";

  // Neg 6: table="KH", has match (KS). Wrong=false
  expect !(HasPlayableCard(["3C", "KS"], "KH") == false), "spec negative 6";

  // Neg 7: table="4H", has match (JH). Wrong=false
  expect !(HasPlayableCard(["JH"], "4H") == false), "spec negative 7";

  // Neg 8: table="9H", no match. Wrong=true
  expect !(HasPlayableCard(["KC", "6D", "KD"], "9H") == true), "spec negative 8";

  // Neg 9: table="AD", no match. Wrong=true
  expect !(HasPlayableCard(["QC", "5S", "4H"], "AD") == true), "spec negative 9";

  // Neg 10: table="QC", has match (QD). Wrong=false
  expect !(HasPlayableCard(["QD", "KS"], "QC") == false), "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====
  var r1 := CardGame("AS", ["2H", "4C", "TH", "JH", "AD"]);
  expect r1 == true, "impl test 1 failed";

  var r2 := CardGame("2H", ["3D", "4C", "AC", "KD", "AS"]);
  expect r2 == false, "impl test 2 failed";

  var r3 := CardGame("4D", ["AS", "AC", "AD", "AH", "5H"]);
  expect r3 == true, "impl test 3 failed";

  var r4 := CardGame("3D", ["8S", "4S", "2C", "AS", "6H"]);
  expect r4 == false, "impl test 4 failed";

  var r5 := CardGame("7H", ["TC", "4C", "KC", "AD", "9S"]);
  expect r5 == false, "impl test 5 failed";

  var r6 := CardGame("KH", ["3C", "QD", "9S", "KS", "8D"]);
  expect r6 == true, "impl test 6 failed";

  var r7 := CardGame("4H", ["JH", "QC", "5H", "9H", "KD"]);
  expect r7 == true, "impl test 7 failed";

  var r8 := CardGame("9H", ["KC", "6D", "KD", "4C", "2S"]);
  expect r8 == false, "impl test 8 failed";

  var r9 := CardGame("AD", ["QC", "5S", "4H", "JH", "2S"]);
  expect r9 == false, "impl test 9 failed";

  var r10 := CardGame("QC", ["QD", "KS", "AH", "7S", "2S"]);
  expect r10 == true, "impl test 10 failed";

  var r11 := CardGame("7H", ["4H", "6D", "AC", "KH", "8H"]);
  expect r11 == true, "impl test 11 failed";

  var r12 := CardGame("4S", ["9D", "4D", "5S", "7D", "5D"]);
  expect r12 == true, "impl test 12 failed";

  var r13 := CardGame("AS", ["2H", "4C", "TH", "JH", "TS"]);
  expect r13 == true, "impl test 13 failed";

  var r14 := CardGame("AS", ["2S", "3S", "4S", "5S", "6S"]);
  expect r14 == true, "impl test 14 failed";

  var r15 := CardGame("KS", ["AD", "2D", "3D", "4D", "5D"]);
  expect r15 == false, "impl test 15 failed";

  var r16 := CardGame("7S", ["7H", "2H", "3H", "4H", "5H"]);
  expect r16 == true, "impl test 16 failed";

  var r17 := CardGame("AS", ["4H", "4C", "TH", "JH", "TS"]);
  expect r17 == true, "impl test 17 failed";

  var r18 := CardGame("7S", ["2H", "4H", "5H", "6H", "2S"]);
  expect r18 == true, "impl test 18 failed";

  var r19 := CardGame("AS", ["2H", "4C", "TH", "JH", "KS"]);
  expect r19 == true, "impl test 19 failed";

  var r20 := CardGame("AS", ["2S", "2H", "3H", "4H", "5H"]);
  expect r20 == true, "impl test 20 failed";

  print "All tests passed\n";
}