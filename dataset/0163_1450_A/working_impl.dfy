method AvoidTrygub(s: string) returns (b: string)
{
  var a := new char[|s|];
  var i := 0;
  while i < |s|
  {
    a[i] := s[i];
    i := i + 1;
  }

  // Insertion sort
  i := 1;
  while i < a.Length
  {
    var key := a[i];
    var j := i - 1;
    while j >= 0 && a[j] > key
    {
      a[j + 1] := a[j];
      j := j - 1;
    }
    a[j + 1] := key;
    i := i + 1;
  }

  b := a[..];
}

method Main()
{
  // Test 1.1
  var r1 := AvoidTrygub("antontrygub");
  expect r1 == "abgnnorttuy", "Test 1.1 failed";

  // Test 1.2
  var r2 := AvoidTrygub("bestcoordinator");
  expect r2 == "abcdeinooorrstt", "Test 1.2 failed";

  // Test 1.3
  var r3 := AvoidTrygub("trywatchinggurabruh");
  expect r3 == "aabcgghhinrrrttuuwy", "Test 1.3 failed";

  // Test 2
  var r4 := AvoidTrygub("byeaeksdkrmobuhcmvyzaqhsftfcthmsmxrwfajcygnmgqprvaclcswjxvaxdqcsfrolvrdxpnfsnbbhohqoppvikmiojnlaoehawsnafxdsomcaydrentk");
  expect r4 == "aaaaaaaaabbbbcccccccdddddeeeeffffffgghhhhhhiijjjkkkklllmmmmmmmnnnnnnoooooooppppqqqqrrrrrrsssssssstttuvvvvvwwwxxxxxyyyyz", "Test 2 failed";

  // Test 3
  var r5 := AvoidTrygub("rgygrbbbrrbbuuggbburgybrtuybubtrbryrtutuuutrrgtbbgtggrggtttbgtbuubyuyyugtgygytbgrgttruturbyuytyyggruttrbbgggbrbryrtuggbuuburrttyubybbyygubrbguybgybubgbrruubbggugtbyurgrtruyrguruygyybygbyytygttbrryrubg");
  expect r5 == "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbgggggggggggggggggggggggggggggggggggggrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrtttttttttttttttttttttttttttuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy", "Test 3 failed";

  // Test 4
  var r6 := AvoidTrygub("ygrbbbrrbbuuggbburgybrtuybubtrbryrtutuuutrrgtbbgtggrggtttbgtbuubyuyyugtgygytbgrgttruturbyuytyyggruttrbbgggbrbryrtuggbuu");
  expect r6 == "bbbbbbbbbbbbbbbbbbbbbbbgggggggggggggggggggggggrrrrrrrrrrrrrrrrrrrttttttttttttttttttttuuuuuuuuuuuuuuuuuuuuyyyyyyyyyyyyyy", "Test 4 failed";

  // Test 5
  var r7 := AvoidTrygub("tbyrguruybtgtybugryrtbugbrgyutruygbtyrgtubrtgybubguytrbtyrugtyugrbuygrtbtrguybybrutgtbgurybygrtugytubrtuyrbgytbugrtrgyburtbygubygtrurbugyttuygbrutbgyrubgrtytugybrytbgurugrbtygtybrurbygutrtgbyubuyrtgrb");
  expect r7 == "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbgggggggggggggggggggggggggggggggggrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrtttttttttttttttttttttttttttttttttuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy", "Test 5 failed";

  // Test 6
  var r8 := AvoidTrygub("rtrttt");
  expect r8 == "rrtttt", "Test 6 failed";

  // Test 7.1
  var r9 := AvoidTrygub("t");
  expect r9 == "t", "Test 7.1 failed";

  // Test 7.2
  var r10 := AvoidTrygub("tt");
  expect r10 == "tt", "Test 7.2 failed";

  // Test 7.3
  var r11 := AvoidTrygub("ttt");
  expect r11 == "ttt", "Test 7.3 failed";

  // Test 8
  var r12 := AvoidTrygub("yyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy");
  expect r12 == "yyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy", "Test 8 failed";

  // Test 9
  var r13 := AvoidTrygub("trygub");
  expect r13 == "bgrtuy", "Test 9 failed";

  print "All tests passed\n";
}