function Digits(n: int): seq<int>
  requires n >= 0
  decreases n
{
  if n == 0 then []
  else Digits(n / 10) + [n % 10]
}

predicate AllDistinct(s: seq<int>)
{
  forall i, j | 0 <= i < |s| && 0 <= j < |s| && i != j :: s[i] != s[j]
}

predicate HasDistinctDigits(n: int)
  requires n >= 1
{
  AllDistinct(Digits(n))
}

// Combined ensures predicate for spec testing
predicate DistinctDigitsEnsures(l: int, r: int, x: int)
  requires l >= 1
{
  (x != -1 ==> (l <= x <= r && HasDistinctDigits(x))) &&
  (x == -1 ==> (forall i | l <= i <= r :: !HasDistinctDigits(i)))
}

method DistinctDigits(l: int, r: int) returns (x: int)
  requires l >= 1
  ensures x != -1 ==> l <= x <= r && HasDistinctDigits(x)
  ensures x == -1 ==> forall i | l <= i <= r :: !HasDistinctDigits(i)
{
  var i := l;
  while i <= r
  {
    var cnt := new int[10](_ => 0);
    var n := i;
    var ok := true;
    while n > 0
    {
      var d := n % 10;
      cnt[d] := cnt[d] + 1;
      if cnt[d] > 1 {
        ok := false;
      }
      n := n / 10;
    }
    if ok {
      return i;
    }
    i := i + 1;
  }
  return -1;
}

method Main()
{
  var result: int;

  // ========== SPEC POSITIVE TESTS ==========
  // Scaled-down inputs where correct output satisfies the ensures predicate

  // From Test 7: (1,1) -> 1
  expect DistinctDigitsEnsures(1, 1, 1), "spec positive 1";
  // From Test 11: (5,5) -> 5
  expect DistinctDigitsEnsures(5, 5, 5), "spec positive 2";
  // From Test 13: (1,100000) -> 1, scaled to (2,5) -> 2
  expect DistinctDigitsEnsures(2, 5, 2), "spec positive 3";
  // From Test 3: (25610,80988) -> 25610, scaled to (3,5) -> 3
  expect DistinctDigitsEnsures(3, 5, 3), "spec positive 4";
  // From Test 9: (25139,86116) -> 25139, scaled to (1,3) -> 1
  expect DistinctDigitsEnsures(1, 3, 1), "spec positive 5";
  // From Test 2/10: result == -1, scaled to (11,11) -> -1 (range size 1)
  expect DistinctDigitsEnsures(11, 11, -1), "spec positive 6";
  // From Test 19: (22,22) -> -1 (range size 1)
  expect DistinctDigitsEnsures(22, 22, -1), "spec positive 7";

  // ========== SPEC NEGATIVE TESTS ==========
  // Scaled-down inputs where wrong output violates the ensures predicate
  // (Skipping Neg 1,4,9 whose wrong outputs still satisfy the spec)

  // From Neg 7: (1,1) wrong=2 — out of range
  expect !DistinctDigitsEnsures(1, 1, 2), "spec negative 1";
  // From Neg 2: (98766,100000) wrong=0, scaled to (1,5) wrong=0 — out of range
  expect !DistinctDigitsEnsures(1, 5, 0), "spec negative 2";
  // From Neg 5: (23452,23456) wrong=23457, scaled to (2,3) wrong=4 — out of range
  expect !DistinctDigitsEnsures(2, 3, 4), "spec negative 3";
  // From Neg 6: (47142,47149) wrong=0, scaled to (1,3) wrong=0 — out of range
  expect !DistinctDigitsEnsures(1, 3, 0), "spec negative 4";
  // From Neg 8: (10,10) wrong=11, scaled to (1,2) wrong=3 — out of range
  expect !DistinctDigitsEnsures(1, 2, 3), "spec negative 5";
  // From Neg 10: (9878,9999) wrong=0, scaled to (3,5) wrong=0 — out of range
  expect !DistinctDigitsEnsures(3, 5, 0), "spec negative 6";
  // From Neg 3: (25610,80988) wrong=25611 (repeated digit), scaled to (11,15) wrong=11
  expect !DistinctDigitsEnsures(11, 15, 11), "spec negative 7";

  // ========== IMPLEMENTATION TESTS ==========
  result := DistinctDigits(121, 130);
  expect result == 123, "impl test 1 failed";

  result := DistinctDigits(98766, 100000);
  expect result == -1, "impl test 2 failed";

  result := DistinctDigits(25610, 80988);
  expect result == 25610, "impl test 3 failed";

  result := DistinctDigits(76330, 80769);
  expect result == 76340, "impl test 4 failed";

  result := DistinctDigits(23452, 23456);
  expect result == 23456, "impl test 5 failed";

  result := DistinctDigits(47142, 47149);
  expect result == -1, "impl test 6 failed";

  result := DistinctDigits(1, 1);
  expect result == 1, "impl test 7 failed";

  result := DistinctDigits(10, 10);
  expect result == 10, "impl test 8 failed";

  result := DistinctDigits(25139, 86116);
  expect result == 25139, "impl test 9 failed";

  result := DistinctDigits(9878, 9999);
  expect result == -1, "impl test 10 failed";

  print "All tests passed\n";
}