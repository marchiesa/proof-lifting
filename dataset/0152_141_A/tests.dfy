function CountChar(s: seq<char>, c: char): nat
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[|s|-1] == c then 1 else 0) + CountChar(s[..|s|-1], c)
}

predicate SameLetters(a: seq<char>, b: seq<char>)
{
  |a| == |b| &&
  (forall i | 0 <= i < |a| :: CountChar(a, a[i]) == CountChar(b, a[i])) &&
  (forall i | 0 <= i < |b| :: CountChar(a, b[i]) == CountChar(b, b[i]))
}

predicate IsSorted(s: seq<char>)
{
  forall i | 0 <= i < |s| - 1 :: s[i] <= s[i + 1]
}

method SortCharSeq(s: seq<char>) returns (sorted: array<char>)
  ensures sorted.Length == |s|
  ensures IsSorted(sorted[..])
  ensures SameLetters(sorted[..], s)
{
  sorted := new char[|s|];
  var i := 0;
  while i < |s| {
    sorted[i] := s[i];
    i := i + 1;
  }
  i := 0;
  while i < sorted.Length {
    var minIdx := i;
    var j := i + 1;
    while j < sorted.Length {
      if sorted[j] < sorted[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    if minIdx != i {
      var tmp := sorted[i];
      sorted[i] := sorted[minIdx];
      sorted[minIdx] := tmp;
    }
    i := i + 1;
  }
}

method AmusingJoke(guest: seq<char>, host: seq<char>, pile: seq<char>) returns (result: bool)
  ensures result == SameLetters(guest + host, pile)
{
  var ab := guest + host;
  var sortedAB := SortCharSeq(ab);
  var sortedC := SortCharSeq(pile);
  if sortedAB.Length != sortedC.Length {
    return false;
  }
  var i := 0;
  while i < sortedAB.Length {
    if sortedAB[i] != sortedC[i] {
      return false;
    }
    i := i + 1;
  }
  return true;
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // SameLetters(guest + host, pile) == expected, using small inputs

  // Test 4: "B" + "A" = "BA", pile = "AB" → YES
  expect SameLetters("BA", "AB") == true, "spec positive 1";
  // Test 6: "Y" + "W" = "YW", pile = "YW" → YES
  expect SameLetters("YW", "YW") == true, "spec positive 2";
  // Test 7: "OI" + "M" = "OIM", pile = "IMO" → YES
  expect SameLetters("OIM", "IMO") == true, "spec positive 3";
  // Test 1 scaled: anagram match, 3 chars
  expect SameLetters("ABC", "CAB") == true, "spec positive 4";
  // Single char identity
  expect SameLetters("A", "A") == true, "spec positive 5";
  // Test 2 scaled (NO): same length, different chars
  expect SameLetters("AB", "AC") == false, "spec positive 6";
  // Test 3 scaled (NO): different char counts
  expect SameLetters("AAB", "ABB") == false, "spec positive 7";
  // Test 9 scaled (NO): single char mismatch
  expect SameLetters("A", "B") == false, "spec positive 8";
  // Test 10 scaled (NO): different lengths
  expect SameLetters("AB", "ABC") == false, "spec positive 9";
  // Empty sequences match
  expect SameLetters("", "") == true, "spec positive 10";

  // ===== SPEC NEGATIVE TESTS =====
  // SameLetters(guest + host, pile) != wrong_output, using small inputs

  // Neg 1: anagram match, wrong output = false
  expect SameLetters("BA", "AB") != false, "spec negative 1";
  // Neg 2: non-anagram, wrong output = true
  expect SameLetters("AB", "AC") != true, "spec negative 2";
  // Neg 3: different counts, wrong output = true
  expect SameLetters("AAB", "ABB") != true, "spec negative 3";
  // Neg 4: anagram match, wrong output = false
  expect SameLetters("A", "A") != false, "spec negative 4";
  // Neg 5: anagram match, wrong output = false
  expect SameLetters("OIM", "IMO") != false, "spec negative 5";
  // Neg 6: anagram match, wrong output = false
  expect SameLetters("YW", "YW") != false, "spec negative 6";
  // Neg 7: anagram match, wrong output = false
  expect SameLetters("AB", "BA") != false, "spec negative 7";
  // Neg 8: anagram match, wrong output = false
  expect SameLetters("XY", "YX") != false, "spec negative 8";
  // Neg 9: non-anagram, wrong output = true
  expect SameLetters("A", "B") != true, "spec negative 9";
  // Neg 10: different lengths, wrong output = true
  expect SameLetters("AB", "ABC") != true, "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====

  var r1 := AmusingJoke("SANTACLAUS", "DEDMOROZ", "SANTAMOROZDEDCLAUS");
  expect r1 == true, "impl test 1 failed";

  var r2 := AmusingJoke("PAPAINOEL", "JOULUPUKKI", "JOULNAPAOILELUPUKKI");
  expect r2 == false, "impl test 2 failed";

  var r3 := AmusingJoke("BABBONATALE", "FATHERCHRISTMAS", "BABCHRISTMASBONATALLEFATHER");
  expect r3 == false, "impl test 3 failed";

  var r4 := AmusingJoke("B", "A", "AB");
  expect r4 == true, "impl test 4 failed";

  var r5 := AmusingJoke("ONDOL", "JNPB", "ONLNJBODP");
  expect r5 == true, "impl test 5 failed";

  var r6 := AmusingJoke("Y", "W", "YW");
  expect r6 == true, "impl test 6 failed";

  var r7 := AmusingJoke("OI", "M", "IMO");
  expect r7 == true, "impl test 7 failed";

  var r8 := AmusingJoke("VFQRWWWACX", "GHZJPOQUSXRAQDGOGMR", "OPAWDOUSGWWCGQXXQAZJRQRGHRMVF");
  expect r8 == true, "impl test 8 failed";

  var r9 := AmusingJoke("JUTCN", "PIGMZOPMEUFADQBW", "NWQGZMAIPUPOMCDUB");
  expect r9 == false, "impl test 9 failed";

  var r10 := AmusingJoke("Z", "O", "ZOCNDOLTBZKQLTBOLDEGXRHZGTTPBJBLSJCVSVXISQZCSFDEBXRCSGBGTHWOVIXYHACAGBRYBKBJAEPIQZHVEGLYH");
  expect r10 == false, "impl test 10 failed";

  var r11 := AmusingJoke("IQ", "OQ", "QOQIGGKFNHJSGCGM");
  expect r11 == false, "impl test 11 failed";

  var r12 := AmusingJoke("ROUWANOPNIGTVMIITVMZ", "OQTUPZMTKUGY", "VTVNGZITGPUNPMQOOATUUIYIWMMKZOTR");
  expect r12 == true, "impl test 12 failed";

  var r13 := AmusingJoke("OVQELLOGFIOLEHXMEMBJDIGBPGEYFG", "JNKFPFFIJOFHRIFHXEWYZOPDJBZTJZKBWQTECNHRFSJPJOAPQT", "YAIPFFFEXJJNEJPLREIGODEGQZVMCOBDFKWTMWJSBEBTOFFQOHIQJLHFNXIGOHEZRZLFOKJBJPTPHPGY");
  expect r13 == true, "impl test 13 failed";

  var r14 := AmusingJoke("NBJGVNGUISUXQTBOBKYHQCOOVQWUXWPXBUDLXPKX", "NSFQDFUMQDQWQ", "WXKKVNTDQQFXCUQBIMQGQHSLVGWSBFYBUPOWPBDUUJUXQNOQDNXOX");
  expect r14 == true, "impl test 14 failed";

  var r15 := AmusingJoke("IJHHGKCXWDBRWJUPRDBZJLNTTNWKXLUGJSBWBOAUKWRAQWGFNL", "NJMWRMBCNPHXTDQQNZ", "WDNJRCLILNQRHWBANLTXWMJBPKUPGKJDJZAQWKTZFBRCTXHHBNXRGUQUNBNMWODGSJWW");
  expect r15 == true, "impl test 15 failed";

  var r16 := AmusingJoke("SRROWANGUGZHCIEFYMQVTWVOMDWPUZJFRDUMVFHYNHNTTGNXCJ", "DJYWGLBFCCECXFHOLORDGDCNRHPWXNHXFCXQCEZUHRRNAEKUIX", "WCUJDNYHNHYOPWMHLDCDYRWBVOGHFFUKOZTXJRXJHRGWICCMRNEVNEGQWTZPNFCSHDRFCFQDCXMHTLUGZAXOFNXNVGUEXIACRERU");
  expect r16 == true, "impl test 16 failed";

  var r17 := AmusingJoke("H", "JKFGHMIAHNDBMFXWYQLZRSVNOTEGCQSVUBYUOZBTNKTXPFQDCMKAGFITEUGOYDFIYQIORMFJEOJDNTFVIQEBICSNGKOSNLNXJWC", "BQSVDOGIHCHXSYNYTQFCHNJGYFIXTSOQINZOKSVQJMTKNTGFNXAVTUYEONMBQMGJLEWJOFGEARIOPKFUFCEMUBRBDNIIDFZDCLWK");
  expect r17 == true, "impl test 17 failed";

  var r18 := AmusingJoke("DSWNZRFVXQ", "PVULCZGOOU", "UOLVZXNUPOQRZGWFVDSCANQTCLEIE");
  expect r18 == false, "impl test 18 failed";

  var r19 := AmusingJoke("EUHTSCENIPXLTSBMLFHD", "IZAVSZPDLXOAGESUSE", "LXAELAZ");
  expect r19 == false, "impl test 19 failed";

  var r20 := AmusingJoke("WYSJFEREGELSKRQRXDXCGBODEFZVSI", "PEJKMGFLBFFDWRCRFSHVEFLEBTJCVCHRJTLDTISHPOGFWPLEWNYJLMXWIAOTYOXMV", "HXERTZWLEXTPIOTFRVMEJVYFFJLRPFMXDEBNSGCEOFFCWTKIDDGCFYSJKGLHBORWEPLDRXRSJYBGASSVCMHEEJFLVI");
  expect r20 == false, "impl test 20 failed";

  print "All tests passed\n";
}