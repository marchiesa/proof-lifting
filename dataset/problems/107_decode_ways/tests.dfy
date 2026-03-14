// Decode Ways -- Runtime spec tests

predicate ValidDigit(d: int) { 1 <= d && d <= 9 }
predicate ValidTwoDigit(d1: int, d2: int) { d1 * 10 + d2 >= 10 && d1 * 10 + d2 <= 26 }

function NumDecodings(s: seq<int>, n: int): nat
  requires 0 <= n <= |s|
  requires forall i :: 0 <= i < |s| ==> 0 <= s[i] <= 9
  decreases n
{
  if n == 0 then 1
  else if n == 1 then (if ValidDigit(s[0]) then 1 else 0)
  else
    (if ValidDigit(s[n-1]) then NumDecodings(s, n-1) else 0) +
    (if ValidTwoDigit(s[n-2], s[n-1]) then NumDecodings(s, n-2) else 0)
}

method Main()
{
  // ValidDigit tests
  expect ValidDigit(1), "1 is valid digit";
  expect ValidDigit(9), "9 is valid digit";
  expect !ValidDigit(0), "0 is not valid digit";
  expect !ValidDigit(10), "10 is not valid digit";

  // ValidTwoDigit tests
  expect ValidTwoDigit(1, 0), "10 is valid two-digit";
  expect ValidTwoDigit(2, 6), "26 is valid two-digit";
  expect !ValidTwoDigit(2, 7), "27 is not valid two-digit";
  expect !ValidTwoDigit(0, 9), "09 is not valid two-digit";
  expect ValidTwoDigit(1, 2), "12 is valid two-digit";

  // NumDecodings: base cases
  expect NumDecodings([1], 0) == 1, "NumDecodings(*, 0) = 1";
  expect NumDecodings([1], 1) == 1, "NumDecodings([1], 1) = 1";
  expect NumDecodings([0], 1) == 0, "NumDecodings([0], 1) = 0 (0 is not valid)";

  // NumDecodings: [1, 2] -> can decode as (1,2) or (12) = 2 ways
  expect NumDecodings([1, 2], 2) == 2, "NumDecodings([1,2], 2) = 2";

  // NumDecodings: [2, 6] -> can decode as (2,6) or (26) = 2 ways
  expect NumDecodings([2, 6], 2) == 2, "NumDecodings([2,6], 2) = 2";

  // NumDecodings: [2, 7] -> only (2,7) = 1 way
  expect NumDecodings([2, 7], 2) == 1, "NumDecodings([2,7], 2) = 1";

  // NumDecodings: [1, 1, 1] -> (1,1,1), (11,1), (1,11) = 3 ways
  expect NumDecodings([1, 1, 1], 3) == 3, "NumDecodings([1,1,1], 3) = 3";

  // NumDecodings: negative test
  expect NumDecodings([1, 2], 2) != 1, "NumDecodings([1,2]) != 1";
  expect NumDecodings([1, 2], 2) != 3, "NumDecodings([1,2]) != 3";

  // NumDecodings: with zero
  expect NumDecodings([1, 0], 2) == 1, "NumDecodings([1,0]) = 1 (only 10)";
  expect NumDecodings([2, 0], 2) == 1, "NumDecodings([2,0]) = 1 (only 20)";

  print "All spec tests passed\n";
}
