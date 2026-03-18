predicate IsSubsequence(sub: seq<char>, s: seq<char>)
  decreases |s|
{
  if |sub| == 0 then true
  else if |s| == 0 then false
  else if sub[|sub| - 1] == s[|s| - 1] then
    IsSubsequence(sub[..|sub| - 1], s[..|s| - 1])
  else
    IsSubsequence(sub, s[..|s| - 1])
}

predicate IsPermutation(a: seq<char>, b: seq<char>)
{
  multiset(a) == multiset(b)
}

method AvoidTrygub(s: string) returns (b: string)
  ensures IsPermutation(s, b)
  ensures !IsSubsequence("trygub", b)
{
  var a := new char[|s|];
  var i := 0;
  while i < |s|
  {
    a[i] := s[i];
    i := i + 1;
  }

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
  // ===== SPEC POSITIVE TESTS =====
  // ensures IsPermutation(s, b) && !IsSubsequence("trygub", b)

  // From Test 7.1: "t" -> "t"
  expect IsPermutation("t", "t"), "spec pos 1a";
  expect !IsSubsequence("trygub", "t"), "spec pos 1b";

  // From Test 7.2: "tt" -> "tt"
  expect IsPermutation("tt", "tt"), "spec pos 2a";
  expect !IsSubsequence("trygub", "tt"), "spec pos 2b";

  // From Test 7.3: "ttt" -> "ttt"
  expect IsPermutation("ttt", "ttt"), "spec pos 3a";
  expect !IsSubsequence("trygub", "ttt"), "spec pos 3b";

  // From Test 6: "rtrttt" -> "rrtttt"
  expect IsPermutation("rtrttt", "rrtttt"), "spec pos 4a";
  expect !IsSubsequence("trygub", "rrtttt"), "spec pos 4b";

  // From Test 9: "trygub" -> "bgrtuy"
  expect IsPermutation("trygub", "bgrtuy"), "spec pos 5a";
  expect !IsSubsequence("trygub", "bgrtuy"), "spec pos 5b";

  // From Test 1.1: "antontrygub" -> "abgnnorttuy"
  expect IsPermutation("antontrygub", "abgnnorttuy"), "spec pos 6a";
  expect !IsSubsequence("trygub", "abgnnorttuy"), "spec pos 6b";

  // ===== SPEC NEGATIVE TESTS =====
  // Wrong outputs violate at least one ensures clause

  // From Neg 7 sub1: input "t", wrong output not a permutation
  expect !IsPermutation("t", "tx"), "spec neg 1";

  // From Neg 7 sub2: input "tt", wrong output not a permutation
  expect !IsPermutation("tt", "ttx"), "spec neg 2";

  // From Neg 7 sub3: input "ttt", wrong output not a permutation
  expect !IsPermutation("ttt", "tttx"), "spec neg 3";

  // From Neg 6: input "rtrttt", wrong output not a permutation
  expect !IsPermutation("rtrttt", "rrtttx"), "spec neg 4";

  // From Neg 8: input all y's, wrong output not a permutation
  expect !IsPermutation("yy", "yyx"), "spec neg 5";

  // From Neg 9: input "trygub", wrong output not a permutation
  expect !IsPermutation("trygub", "bgrtuv"), "spec neg 6";

  // Subsequence violation: unsorted "trygub" contains "trygub" as subsequence
  expect IsSubsequence("trygub", "trygub"), "spec neg 7: subseq violated";

  // ===== IMPLEMENTATION TESTS =====

  // Test 1.1
  var r1 := AvoidTrygub("antontrygub");
  expect r1 == "abgnnorttuy", "impl test 1.1 failed";

  // Test 1.2
  var r2 := AvoidTrygub("bestcoordinator");
  expect r2 == "abcdeinooorrstt", "impl test 1.2 failed";

  // Test 1.3
  var r3 := AvoidTrygub("trywatchinggurabruh");
  expect r3 == "aabcgghhinrrrttuuwy", "impl test 1.3 failed";

  // Test 2
  var r4 := AvoidTrygub("byeaeksdkrmobuhcmvyzaqhsftfcthmsmxrwfajcygnmgqprvaclcswjxvaxdqcsfrolvrdxpnfsnbbhohqoppvikmiojnlaoehawsnafxdsomcaydrentk");
  expect r4 == "aaaaaaaaabbbbcccccccdddddeeeeffffffgghhhhhhiijjjkkkklllmmmmmmmnnnnnnoooooooppppqqqqrrrrrrsssssssstttuvvvvvwwwxxxxxyyyyz", "impl test 2 failed";

  // Test 3
  var r5 := AvoidTrygub("rgygrbbbrrbbuuggbburgybrtuybubtrbryrtutuuutrrgtbbgtggrggtttbgtbuubyuyyugtgygytbgrgttruturbyuytyyggruttrbbgggbrbryrtuggbuuburrttyubybbyygubrbguybgybubgbrruubbggugtbyurgrtruyrguruygyybygbyytygttbrryrubg");
  expect r5 == "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbgggggggggggggggggggggggggggggggggggggrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrtttttttttttttttttttttttttttuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy", "impl test 3 failed";

  // Test 4
  var r6 := AvoidTrygub("ygrbbbrrbbuuggbburgybrtuybubtrbryrtutuuutrrgtbbgtggrggtttbgtbuubyuyyugtgygytbgrgttruturbyuytyyggruttrbbgggbrbryrtuggbuu");
  expect r6 == "bbbbbbbbbbbbbbbbbbbbbbbgggggggggggggggggggggggrrrrrrrrrrrrrrrrrrrttttttttttttttttttttuuuuuuuuuuuuuuuuuuuuyyyyyyyyyyyyyy", "impl test 4 failed";

  // Test 5
  var r7 := AvoidTrygub("tbyrguruybtgtybugryrtbugbrgyutruygbtyrgtubrtgybubguytrbtyrugtyugrbuygrtbtrguybybrutgtbgurybygrtugytubrtuyrbgytbugrtrgyburtbygubygtrurbugyttuygbrutbgyrubgrtytugybrytbgurugrbtygtybrurbygutrtgbyubuyrtgrb");
  expect r7 == "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbgggggggggggggggggggggggggggggggggrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrtttttttttttttttttttttttttttttttttuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuuyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy", "impl test 5 failed";

  // Test 6
  var r8 := AvoidTrygub("rtrttt");
  expect r8 == "rrtttt", "impl test 6 failed";

  // Test 7.1
  var r9 := AvoidTrygub("t");
  expect r9 == "t", "impl test 7.1 failed";

  // Test 7.2
  var r10 := AvoidTrygub("tt");
  expect r10 == "tt", "impl test 7.2 failed";

  // Test 7.3
  var r11 := AvoidTrygub("ttt");
  expect r11 == "ttt", "impl test 7.3 failed";

  // Test 8
  var r12 := AvoidTrygub("yyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy");
  expect r12 == "yyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyyy", "impl test 8 failed";

  // Test 9
  var r13 := AvoidTrygub("trygub");
  expect r13 == "bgrtuy", "impl test 9 failed";

  print "All tests passed\n";
}