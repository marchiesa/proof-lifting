function TriNum(k: nat): nat
{
  k * (k + 1) / 2
}

function Repeat(c: char, count: nat): string
  decreases count
{
  if count == 0 then ""
  else [c] + Repeat(c, count - 1)
}

function Encrypt(s: string): string
  decreases |s|
{
  if |s| == 0 then ""
  else Encrypt(s[..|s|-1]) + Repeat(s[|s|-1], |s|)
}

function AllSameChar(t: string, lo: nat, hi: nat, c: char): bool
  decreases hi - lo
{
  if lo >= hi || lo >= |t| then true
  else t[lo] == c && AllSameChar(t, lo + 1, hi, c)
}

function CheckBlocks(t: string, m: nat, i: nat): bool
  decreases m - i
{
  if i >= m then true
  else if TriNum(i + 1) > |t| then false
  else AllSameChar(t, TriNum(i), TriNum(i + 1), t[TriNum(i)]) && CheckBlocks(t, m, i + 1)
}

predicate IsValidEncryption(t: string)
{
  exists m | 0 <= m <= |t| ::
    TriNum(m) == |t| && CheckBlocks(t, m, 0)
}

method DecryptRepeatingCipher(t: string, n: int) returns (s: string)
  requires n == |t|
  requires IsValidEncryption(t)
  ensures Encrypt(s) == t
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
  // === SPEC POSITIVE tests: Encrypt(correct_output) == encrypted_input ===
  expect Encrypt("z") == "z", "spec positive 1";              // Test 3
  expect Encrypt("zw") == "zww", "spec positive 2";           // Test 4
  expect Encrypt("bab") == "baabbb", "spec positive 3";       // Test 1
  expect Encrypt("oo") == "ooo", "spec positive 4";           // Scaled Test 2
  expect Encrypt("ab") == "abb", "spec positive 5";           // Scaled Test 8
  expect Encrypt("aa") == "aaa", "spec positive 6";           // Scaled Test 7
  expect Encrypt("co") == "coo", "spec positive 7";           // Scaled Test 6

  // === SPEC NEGATIVE tests: Encrypt(wrong_output) != encrypted_input ===
  expect Encrypt("z WRONG") != "z", "spec negative 1";        // Neg 3
  expect Encrypt("zw WRONG") != "zww", "spec negative 2";     // Neg 4
  expect Encrypt("bab WRONG") != "baabbb", "spec negative 3"; // Neg 1
  expect Encrypt("ox") != "ooo", "spec negative 4";           // Scaled Neg 2
  expect Encrypt("ba") != "abb", "spec negative 5";           // Scaled Neg 8
  expect Encrypt("ab") != "aaa", "spec negative 6";           // Scaled Neg 7
  expect Encrypt("oc") != "coo", "spec negative 7";           // Scaled Neg 6

  // === IMPLEMENTATION tests ===
  var r1 := DecryptRepeatingCipher("baabbb", 6);
  expect r1 == "bab", "impl test 1 failed";

  var r2 := DecryptRepeatingCipher("ooopppssss", 10);
  expect r2 == "oops", "impl test 2 failed";

  var r3 := DecryptRepeatingCipher("z", 1);
  expect r3 == "z", "impl test 3 failed";

  var r4 := DecryptRepeatingCipher("zww", 3);
  expect r4 == "zw", "impl test 4 failed";

  var r5 := DecryptRepeatingCipher("cooooonnnnttttteeeeeeeeeeeeessssssssttttttttttttttttttt", 55);
  expect r5 == "coonteestt", "impl test 5 failed";

  var r6 := DecryptRepeatingCipher("coodddeeeecccccoooooo", 21);
  expect r6 == "codeco", "impl test 6 failed";

  var r7 := DecryptRepeatingCipher("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", 55);
  expect r7 == "aaaaaaaaaa", "impl test 7 failed";

  var r8 := DecryptRepeatingCipher("abbcccddddeeeeeffffffggggggghhhhhhhh", 36);
  expect r8 == "abcdefgh", "impl test 8 failed";

  print "All tests passed\n";
}