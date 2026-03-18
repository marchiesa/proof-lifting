method SortCharSeq(s: seq<char>) returns (sorted: array<char>)
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
  var r1 := AmusingJoke("SANTACLAUS", "DEDMOROZ", "SANTAMOROZDEDCLAUS");
  expect r1 == true, "Test 1 failed";

  var r2 := AmusingJoke("PAPAINOEL", "JOULUPUKKI", "JOULNAPAOILELUPUKKI");
  expect r2 == false, "Test 2 failed";

  var r3 := AmusingJoke("BABBONATALE", "FATHERCHRISTMAS", "BABCHRISTMASBONATALLEFATHER");
  expect r3 == false, "Test 3 failed";

  var r4 := AmusingJoke("B", "A", "AB");
  expect r4 == true, "Test 4 failed";

  var r5 := AmusingJoke("ONDOL", "JNPB", "ONLNJBODP");
  expect r5 == true, "Test 5 failed";

  var r6 := AmusingJoke("Y", "W", "YW");
  expect r6 == true, "Test 6 failed";

  var r7 := AmusingJoke("OI", "M", "IMO");
  expect r7 == true, "Test 7 failed";

  var r8 := AmusingJoke("VFQRWWWACX", "GHZJPOQUSXRAQDGOGMR", "OPAWDOUSGWWCGQXXQAZJRQRGHRMVF");
  expect r8 == true, "Test 8 failed";

  var r9 := AmusingJoke("JUTCN", "PIGMZOPMEUFADQBW", "NWQGZMAIPUPOMCDUB");
  expect r9 == false, "Test 9 failed";

  var r10 := AmusingJoke("Z", "O", "ZOCNDOLTBZKQLTBOLDEGXRHZGTTPBJBLSJCVSVXISQZCSFDEBXRCSGBGTHWOVIXYHACAGBRYBKBJAEPIQZHVEGLYH");
  expect r10 == false, "Test 10 failed";

  var r11 := AmusingJoke("IQ", "OQ", "QOQIGGKFNHJSGCGM");
  expect r11 == false, "Test 11 failed";

  var r12 := AmusingJoke("ROUWANOPNIGTVMIITVMZ", "OQTUPZMTKUGY", "VTVNGZITGPUNPMQOOATUUIYIWMMKZOTR");
  expect r12 == true, "Test 12 failed";

  var r13 := AmusingJoke("OVQELLOGFIOLEHXMEMBJDIGBPGEYFG", "JNKFPFFIJOFHRIFHXEWYZOPDJBZTJZKBWQTECNHRFSJPJOAPQT", "YAIPFFFEXJJNEJPLREIGODEGQZVMCOBDFKWTMWJSBEBTOFFQOHIQJLHFNXIGOHEZRZLFOKJBJPTPHPGY");
  expect r13 == true, "Test 13 failed";

  var r14 := AmusingJoke("NBJGVNGUISUXQTBOBKYHQCOOVQWUXWPXBUDLXPKX", "NSFQDFUMQDQWQ", "WXKKVNTDQQFXCUQBIMQGQHSLVGWSBFYBUPOWPBDUUJUXQNOQDNXOX");
  expect r14 == true, "Test 14 failed";

  var r15 := AmusingJoke("IJHHGKCXWDBRWJUPRDBZJLNTTNWKXLUGJSBWBOAUKWRAQWGFNL", "NJMWRMBCNPHXTDQQNZ", "WDNJRCLILNQRHWBANLTXWMJBPKUPGKJDJZAQWKTZFBRCTXHHBNXRGUQUNBNMWODGSJWW");
  expect r15 == true, "Test 15 failed";

  var r16 := AmusingJoke("SRROWANGUGZHCIEFYMQVTWVOMDWPUZJFRDUMVFHYNHNTTGNXCJ", "DJYWGLBFCCECXFHOLORDGDCNRHPWXNHXFCXQCEZUHRRNAEKUIX", "WCUJDNYHNHYOPWMHLDCDYRWBVOGHFFUKOZTXJRXJHRGWICCMRNEVNEGQWTZPNFCSHDRFCFQDCXMHTLUGZAXOFNXNVGUEXIACRERU");
  expect r16 == true, "Test 16 failed";

  var r17 := AmusingJoke("H", "JKFGHMIAHNDBMFXWYQLZRSVNOTEGCQSVUBYUOZBTNKTXPFQDCMKAGFITEUGOYDFIYQIORMFJEOJDNTFVIQEBICSNGKOSNLNXJWC", "BQSVDOGIHCHXSYNYTQFCHNJGYFIXTSOQINZOKSVQJMTKNTGFNXAVTUYEONMBQMGJLEWJOFGEARIOPKFUFCEMUBRBDNIIDFZDCLWK");
  expect r17 == true, "Test 17 failed";

  var r18 := AmusingJoke("DSWNZRFVXQ", "PVULCZGOOU", "UOLVZXNUPOQRZGWFVDSCANQTCLEIE");
  expect r18 == false, "Test 18 failed";

  var r19 := AmusingJoke("EUHTSCENIPXLTSBMLFHD", "IZAVSZPDLXOAGESUSE", "LXAELAZ");
  expect r19 == false, "Test 19 failed";

  var r20 := AmusingJoke("WYSJFEREGELSKRQRXDXCGBODEFZVSI", "PEJKMGFLBFFDWRCRFSHVEFLEBTJCVCHRJTLDTISHPOGFWPLEWNYJLMXWIAOTYOXMV", "HXERTZWLEXTPIOTFRVMEJVYFFJLRPFMXDEBNSGCEOFFCWTKIDDGCFYSJKGLHBORWEPLDRXRSJYBGASSVCMHEEJFLVI");
  expect r20 == false, "Test 20 failed";

  print "All tests passed\n";
}