method Decrypt(t: string) returns (s: string)
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
  var r1 := Decrypt("ncteho");
  expect r1 == "techno", "Test 1 failed";

  var r2 := Decrypt("erfdcoeocs");
  expect r2 == "codeforces", "Test 2 failed";

  var r3 := Decrypt("z");
  expect r3 == "z", "Test 3 failed";

  var r4 := Decrypt("bz");
  expect r4 == "bz", "Test 4 failed";

  var r5 := Decrypt("tea");
  expect r5 == "eat", "Test 5 failed";

  var r6 := Decrypt("code");
  expect r6 == "odce", "Test 6 failed";

  var r7 := Decrypt("qwertyuioasdfghjklrtyuiodfghjklqwertyuioasdfssddxb");
  expect r7 == "dfogihujyktlrqlwkejrhtgyfudisoaaosidufystsrdedwxqb", "Test 7 failed";

  var r8 := Decrypt("qwertyuioasdfghjklrtyuiodfghjklqwertyuioasdfssd");
  expect r8 == "odifugyhtjrkllkqjwhegrftdysuaiooiausydtfrseswdq", "Test 8 failed";

  var r9 := Decrypt("testa");
  expect r9 == "steat", "Test 9 failed";

  var r10 := Decrypt("abcdef");
  expect r10 == "cdbeaf", "Test 10 failed";

  var r11 := Decrypt("abcdefg");
  expect r11 == "decfbga", "Test 11 failed";

  var r12 := Decrypt("qwertyuioasdfghjklrtyuiodfghjklqwertyuioasdfssdda");
  expect r12 == "dfogihujyktlrqlwkejrhtgyfudisoaaosidufystsrdedwaq", "Test 12 failed";

  var r13 := Decrypt("zqwertyuioasdfghjklrtyuiodfghjklqwertyuioasdfssd");
  expect r13 == "ioudyftgrhljkkjlhqgwfedrstayouiiuoyatsrdefwsqszd", "Test 13 failed";

  var r14 := Decrypt("gecabdfh");
  expect r14 == "abcdefgh", "Test 14 failed";

  var r15 := Decrypt("aechs");
  expect r15 == "chesa", "Test 15 failed";

  print "All tests passed\n";
}