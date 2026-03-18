function SwapResultA(a_i: char, c_i: char, swapWithA: bool): char
{
  if swapWithA then c_i else a_i
}

function SwapResultB(b_i: char, c_i: char, swapWithA: bool): char
{
  if swapWithA then b_i else c_i
}

predicate ValidSwapChoice(a_i: char, b_i: char, c_i: char, swapWithA: bool)
{
  SwapResultA(a_i, c_i, swapWithA) == SwapResultB(b_i, c_i, swapWithA)
}

predicate CanMakeEqual(a: string, b: string, c: string)
  requires |a| == |b| == |c|
{
  forall i | 0 <= i < |a| ::
    exists swapWithA: bool :: ValidSwapChoice(a[i], b[i], c[i], swapWithA)
}

method ThreeStrings(a: string, b: string, c: string) returns (result: bool)
  requires |a| == |b| == |c|
  ensures result == CanMakeEqual(a, b, c)
{
  var i := 0;
  while i < |a|
  {
    if a[i] != c[i] && b[i] != c[i] {
      return false;
    }
    i := i + 1;
  }
  return true;
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // Top-level ensures predicate: result == CanMakeEqual(a, b, c)
  // Testing CanMakeEqual with correct outputs from positive test pairs

  // Positive test 1, sub-case 1: ("aaa","bbb","ccc") -> NO (false), length 3
  expect CanMakeEqual("aaa", "bbb", "ccc") == false, "spec positive 1";

  // Positive test 1, sub-case 2: ("abc","bca","bca") -> YES (true), length 3
  expect CanMakeEqual("abc", "bca", "bca") == true, "spec positive 2";

  // Positive test 1, sub-case 3: ("aabb","bbaa","baba") -> YES (true)
  // Scaled to length 3: ("aab","bba","bab") -> true
  expect CanMakeEqual("aab", "bba", "bab") == true, "spec positive 3";

  // Positive test 1, sub-case 4: ("imi","mii","iim") -> NO (false), length 3
  expect CanMakeEqual("imi", "mii", "iim") == false, "spec positive 4";

  // Positive test 2: ("ab","ab","bb") -> NO (false), length 2
  expect CanMakeEqual("ab", "ab", "bb") == false, "spec positive 5";

  // Additional small positive cases
  expect CanMakeEqual("a", "a", "a") == true, "spec positive 6";
  expect CanMakeEqual("ab", "ba", "ab") == true, "spec positive 7";

  // === SPEC NEGATIVE TESTS ===
  // Testing CanMakeEqual with WRONG outputs — spec must reject these

  // Negative 1, sub-case 4: ("imi","mii","iim") correct=false, wrong=true
  expect CanMakeEqual("imi", "mii", "iim") != true, "spec negative 1";

  // Negative 2: ("ab","ab","bb") correct=false, wrong=true
  expect CanMakeEqual("ab", "ab", "bb") != true, "spec negative 2";

  // Additional small negative cases (wrong output is opposite of correct)
  // ("a","b","c") -> correct=false, wrong=true
  expect CanMakeEqual("a", "b", "c") != true, "spec negative 3";

  // ("ab","ba","cc") -> correct=false, wrong=true
  expect CanMakeEqual("ab", "ba", "cc") != true, "spec negative 4";

  // ("abc","bca","bca") -> correct=true, wrong=false
  expect CanMakeEqual("abc", "bca", "bca") != false, "spec negative 5";

  // === IMPLEMENTATION TESTS ===
  // Full-size test pairs, testing the method returns correct output

  // Positive test 1
  var r1 := ThreeStrings("aaa", "bbb", "ccc");
  expect r1 == false, "impl test 1 failed";

  var r2 := ThreeStrings("abc", "bca", "bca");
  expect r2 == true, "impl test 2 failed";

  var r3 := ThreeStrings("aabb", "bbaa", "baba");
  expect r3 == true, "impl test 3 failed";

  var r4 := ThreeStrings("imi", "mii", "iim");
  expect r4 == false, "impl test 4 failed";

  // Positive test 2
  var r5 := ThreeStrings("ab", "ab", "bb");
  expect r5 == false, "impl test 5 failed";

  print "All tests passed\n";
}