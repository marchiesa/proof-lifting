method CardGame(table: string, hand: seq<string>) returns (canPlay: bool)
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
  var r1 := CardGame("AS", ["2H", "4C", "TH", "JH", "AD"]);
  expect r1 == true, "Test 1 failed";

  var r2 := CardGame("2H", ["3D", "4C", "AC", "KD", "AS"]);
  expect r2 == false, "Test 2 failed";

  var r3 := CardGame("4D", ["AS", "AC", "AD", "AH", "5H"]);
  expect r3 == true, "Test 3 failed";

  var r4 := CardGame("3D", ["8S", "4S", "2C", "AS", "6H"]);
  expect r4 == false, "Test 4 failed";

  var r5 := CardGame("7H", ["TC", "4C", "KC", "AD", "9S"]);
  expect r5 == false, "Test 5 failed";

  var r6 := CardGame("KH", ["3C", "QD", "9S", "KS", "8D"]);
  expect r6 == true, "Test 6 failed";

  var r7 := CardGame("4H", ["JH", "QC", "5H", "9H", "KD"]);
  expect r7 == true, "Test 7 failed";

  var r8 := CardGame("9H", ["KC", "6D", "KD", "4C", "2S"]);
  expect r8 == false, "Test 8 failed";

  var r9 := CardGame("AD", ["QC", "5S", "4H", "JH", "2S"]);
  expect r9 == false, "Test 9 failed";

  var r10 := CardGame("QC", ["QD", "KS", "AH", "7S", "2S"]);
  expect r10 == true, "Test 10 failed";

  var r11 := CardGame("7H", ["4H", "6D", "AC", "KH", "8H"]);
  expect r11 == true, "Test 11 failed";

  var r12 := CardGame("4S", ["9D", "4D", "5S", "7D", "5D"]);
  expect r12 == true, "Test 12 failed";

  var r13 := CardGame("AS", ["2H", "4C", "TH", "JH", "TS"]);
  expect r13 == true, "Test 13 failed";

  var r14 := CardGame("AS", ["2S", "3S", "4S", "5S", "6S"]);
  expect r14 == true, "Test 14 failed";

  var r15 := CardGame("KS", ["AD", "2D", "3D", "4D", "5D"]);
  expect r15 == false, "Test 15 failed";

  var r16 := CardGame("7S", ["7H", "2H", "3H", "4H", "5H"]);
  expect r16 == true, "Test 16 failed";

  var r17 := CardGame("AS", ["4H", "4C", "TH", "JH", "TS"]);
  expect r17 == true, "Test 17 failed";

  var r18 := CardGame("7S", ["2H", "4H", "5H", "6H", "2S"]);
  expect r18 == true, "Test 18 failed";

  var r19 := CardGame("AS", ["2H", "4C", "TH", "JH", "KS"]);
  expect r19 == true, "Test 19 failed";

  var r20 := CardGame("AS", ["2S", "2H", "3H", "4H", "5H"]);
  expect r20 == true, "Test 20 failed";

  print "All tests passed\n";
}