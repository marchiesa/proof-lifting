// Testable spec functions
function Encrypt(s: string): string
  decreases |s|
{
  if |s| == 0 then ""
  else if |s| == 1 then [s[0]]
  else if |s| % 2 == 0 then
    Encrypt(s[..|s|-1]) + [s[|s|-1]]
  else
    [s[|s|-1]] + Encrypt(s[..|s|-1])
}

predicate IsDecryptionOf(s: string, t: string)
{
  |s| == |t| && Encrypt(s) == t
}

// Implementation
method Decrypt(t: string) returns (s: string)
  ensures IsDecryptionOf(s, t)
{
  var n := |t|;
  if n == 0 {
    s := "";
    return;
  }
  var mid := (n - 1) / 2;
  s := [t[mid]];
  var u1: int := mid + 1;
  var u2: int := mid - 1;
  while u1 < n && u2 >= 0
  {
    s := s + [t[u1]];
    s := s + [t[u2]];
    u1 := u1 + 1;
    u2 := u2 - 1;
  }
  if n % 2 == 0 {
    s := s + [t[n - 1]];
  }
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // IsDecryptionOf(plaintext, ciphertext) should be true
  expect IsDecryptionOf("z", "z"), "spec positive 1";
  expect IsDecryptionOf("bz", "bz"), "spec positive 2";
  expect IsDecryptionOf("eat", "tea"), "spec positive 3";
  expect IsDecryptionOf("odce", "code"), "spec positive 4";
  expect IsDecryptionOf("techno", "ncteho"), "spec positive 5";
  expect IsDecryptionOf("codeforces", "erfdcoeocs"), "spec positive 6";
  expect IsDecryptionOf("steat", "testa"), "spec positive 7";
  expect IsDecryptionOf("cdbeaf", "abcdef"), "spec positive 8";
  expect IsDecryptionOf("dfogihujyktlrqlwkejrhtgyfudisoaaosidufystsrdedwxqb", "qwertyuioasdfghjklrtyuiodfghjklqwertyuioasdfssddxb"), "spec positive 9";
  expect IsDecryptionOf("odifugyhtjrkllkqjwhegrftdysuaiooiausydtfrseswdq", "qwertyuioasdfghjklrtyuiodfghjklqwertyuioasdfssd"), "spec positive 10";

  // === SPEC NEGATIVE TESTS ===
  // IsDecryptionOf(wrong_plaintext, ciphertext) should be false
  expect !IsDecryptionOf("techno WRONG", "ncteho"), "spec negative 1";
  expect !IsDecryptionOf("codeforces WRONG", "erfdcoeocs"), "spec negative 2";
  expect !IsDecryptionOf("z WRONG", "z"), "spec negative 3";
  expect !IsDecryptionOf("bz WRONG", "bz"), "spec negative 4";
  expect !IsDecryptionOf("eat WRONG", "tea"), "spec negative 5";
  expect !IsDecryptionOf("odce WRONG", "code"), "spec negative 6";
  expect !IsDecryptionOf("dfogihujyktlrqlwkejrhtgyfudisoaaosidufystsrdedwxqb WRONG", "qwertyuioasdfghjklrtyuiodfghjklqwertyuioasdfssddxb"), "spec negative 7";
  expect !IsDecryptionOf("odifugyhtjrkllkqjwhegrftdysuaiooiausydtfrseswdq WRONG", "qwertyuioasdfghjklrtyuiodfghjklqwertyuioasdfssd"), "spec negative 8";
  expect !IsDecryptionOf("steat WRONG", "testa"), "spec negative 9";
  expect !IsDecryptionOf("cdbeaf WRONG", "abcdef"), "spec negative 10";

  // === IMPLEMENTATION TESTS ===
  var r1 := Decrypt("ncteho");
  expect r1 == "techno", "impl test 1 failed";

  var r2 := Decrypt("erfdcoeocs");
  expect r2 == "codeforces", "impl test 2 failed";

  var r3 := Decrypt("z");
  expect r3 == "z", "impl test 3 failed";

  var r4 := Decrypt("bz");
  expect r4 == "bz", "impl test 4 failed";

  var r5 := Decrypt("tea");
  expect r5 == "eat", "impl test 5 failed";

  var r6 := Decrypt("code");
  expect r6 == "odce", "impl test 6 failed";

  var r7 := Decrypt("qwertyuioasdfghjklrtyuiodfghjklqwertyuioasdfssddxb");
  expect r7 == "dfogihujyktlrqlwkejrhtgyfudisoaaosidufystsrdedwxqb", "impl test 7 failed";

  var r8 := Decrypt("qwertyuioasdfghjklrtyuiodfghjklqwertyuioasdfssd");
  expect r8 == "odifugyhtjrkllkqjwhegrftdysuaiooiausydtfrseswdq", "impl test 8 failed";

  var r9 := Decrypt("testa");
  expect r9 == "steat", "impl test 9 failed";

  var r10 := Decrypt("abcdef");
  expect r10 == "cdbeaf", "impl test 10 failed";

  print "All tests passed\n";
}