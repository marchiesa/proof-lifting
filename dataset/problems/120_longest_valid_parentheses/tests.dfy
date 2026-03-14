// Longest Valid Parentheses -- Runtime spec tests

function Balance(s: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |s|
  decreases hi - lo
{
  if lo == hi then 0
  else (if s[lo] == 1 then 1 else -1) + Balance(s, lo + 1, hi)
}

// Bounded BalanceNeverNeg for runtime
function BalanceNeverNegBounded(s: seq<int>, lo: int, hi: int): bool
  requires 0 <= lo <= hi <= |s|
  decreases hi - lo
{
  if lo == hi then Balance(s, lo, lo) >= 0
  else Balance(s, lo, lo) >= 0 && BalanceNeverNegBounded(s, lo, hi - 1) &&
       Balance(s, lo, hi) >= 0
}

// Simpler bounded check: check all prefixes
function AllPrefixBalancesNonNeg(s: seq<int>, lo: int, hi: int, k: int): bool
  requires 0 <= lo <= hi <= |s|
  requires lo <= k <= hi
  decreases hi - k
{
  Balance(s, lo, k) >= 0 &&
  (if k == hi then true else AllPrefixBalancesNonNeg(s, lo, hi, k + 1))
}

function ValidParensBounded(s: seq<int>, lo: int, hi: int): bool
  requires 0 <= lo <= hi <= |s|
{
  AllPrefixBalancesNonNeg(s, lo, hi, lo) && Balance(s, lo, hi) == 0
}

method Main()
{
  // Balance tests
  expect Balance([1, 0], 0, 0) == 0, "Balance of empty = 0";
  expect Balance([1, 0], 0, 1) == 1, "Balance of '(' = 1";
  expect Balance([1, 0], 0, 2) == 0, "Balance of '()' = 0";
  expect Balance([1, 1, 0, 0], 0, 4) == 0, "Balance of '(())' = 0";
  expect Balance([0, 1], 0, 1) == -1, "Balance of ')' = -1";
  expect Balance([0, 1], 0, 2) == 0, "Balance of ')(' = 0";

  // ValidParensBounded: positive
  expect ValidParensBounded([1, 0], 0, 2), "'()' is valid parens";
  expect ValidParensBounded([1, 1, 0, 0], 0, 4), "'(())' is valid parens";
  expect ValidParensBounded([1, 0, 1, 0], 0, 4), "'()()' is valid parens";
  expect ValidParensBounded([], 0, 0), "Empty is valid parens";

  // ValidParensBounded: negative
  expect !ValidParensBounded([0, 1], 0, 2), "')(' is not valid parens (balance goes -1)";
  expect !ValidParensBounded([1, 1, 0], 0, 3), "'((' is not valid (unbalanced)";
  expect !ValidParensBounded([1], 0, 1), "'(' is not valid (unbalanced)";
  expect !ValidParensBounded([0], 0, 1), "')' is not valid";

  // ValidParensBounded: subranges
  expect ValidParensBounded([0, 1, 0, 0], 1, 3), "'()' within ')())'";
  expect !ValidParensBounded([0, 1, 0, 0], 0, 4), "')())' is not valid";

  // Balance: negative tests
  expect Balance([1, 0], 0, 2) != 1, "Balance of '()' is not 1";
  expect Balance([1, 1, 0], 0, 3) != 0, "Balance of '((' is not 0";

  // Test '()()'  - the longest valid substring in ')()()' is 4
  var s := [0, 1, 0, 1, 0];
  expect ValidParensBounded(s, 1, 5), "'()()' is valid parens";
  expect !ValidParensBounded(s, 0, 5), "')()()' is not valid";

  print "All spec tests passed\n";
}
