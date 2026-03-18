method DecryptRepeatingCipher(t: string, n: int) returns (s: string)
{
  s := "";
  var x := 0;
  var y := 1;
  while x < n && x < |t|
  {
    s := s + [t[x]];
    x := x + y;
    y := y + 1;
  }
}

method Main()
{
  var r1 := DecryptRepeatingCipher("baabbb", 6);
  expect r1 == "bab", "Test 1 failed";

  var r2 := DecryptRepeatingCipher("ooopppssss", 10);
  expect r2 == "oops", "Test 2 failed";

  var r3 := DecryptRepeatingCipher("z", 1);
  expect r3 == "z", "Test 3 failed";

  var r4 := DecryptRepeatingCipher("zww", 3);
  expect r4 == "zw", "Test 4 failed";

  var r5 := DecryptRepeatingCipher("cooooonnnnttttteeeeeeeeeeeeessssssssttttttttttttttttttt", 55);
  expect r5 == "coonteestt", "Test 5 failed";

  var r6 := DecryptRepeatingCipher("coodddeeeecccccoooooo", 21);
  expect r6 == "codeco", "Test 6 failed";

  var r7 := DecryptRepeatingCipher("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", 55);
  expect r7 == "aaaaaaaaaa", "Test 7 failed";

  var r8 := DecryptRepeatingCipher("abbcccddddeeeeeffffffggggggghhhhhhhh", 36);
  expect r8 == "abcdefgh", "Test 8 failed";

  print "All tests passed\n";
}