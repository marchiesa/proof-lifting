// ── Formal Specification for the Coins Problem ──

function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

predicate AllValid(coins: seq<int>, n: int)
{
  forall i | 0 <= i < |coins| :: 1 <= coins[i] <= n
}

predicate IsValidSelection(coins: seq<int>, n: int, S: int)
{
  |coins| >= 1 && AllValid(coins, n) && Sum(coins) == S
}

predicate Achievable(k: int, n: int, S: int)
{
  k >= 1 && n >= 1 && k <= S && S <= k * n
}

function Witness(k: int, n: int, S: int): seq<int>
{
  if k >= 1 && n >= 1 && k <= S && S <= k * n then
    seq(k, i requires 0 <= i < k => if i < k - 1 then n else S - (k - 1) * n)
  else
    []
}

// ── Method with contracts ──

method Coins(n: int, S: int) returns (minCoins: int)
  requires n >= 1
  requires S >= 1
  ensures Achievable(minCoins, n, S)
  ensures forall k | 1 <= k < minCoins :: !Achievable(k, n, S)
{
  minCoins := (S - 1) / n + 1;
}

// ── Tests ──

method Main()
{
  // ════════════════════════════════════════════════
  // SPEC POSITIVE tests (8 tests)
  // ensures 1: Achievable(minCoins, n, S)
  // ensures 2: forall k | 1 <= k < minCoins :: !Achievable(k, n, S)
  // ════════════════════════════════════════════════

  // Pos 1: n=5, S=11, correct=3
  expect Achievable(3, 5, 11), "spec pos 1a";
  expect forall k | 1 <= k < 3 :: !Achievable(k, 5, 11), "spec pos 1b";

  // Pos 2: n=6, S=16, correct=3
  expect Achievable(3, 6, 16), "spec pos 2a";
  expect forall k | 1 <= k < 3 :: !Achievable(k, 6, 16), "spec pos 2b";

  // Pos 3: n=14, S=28, correct=2
  expect Achievable(2, 14, 28), "spec pos 3a";
  expect forall k | 1 <= k < 2 :: !Achievable(k, 14, 28), "spec pos 3b";

  // Pos 4: n=5, S=29, correct=6
  expect Achievable(6, 5, 29), "spec pos 4a";
  expect forall k | 1 <= k < 6 :: !Achievable(k, 5, 29), "spec pos 4b";

  // Pos 5: n=10, S=24, correct=3
  expect Achievable(3, 10, 24), "spec pos 5a";
  expect forall k | 1 <= k < 3 :: !Achievable(k, 10, 24), "spec pos 5b";

  // Pos 6: n=100000, S=1, correct=1
  expect Achievable(1, 100000, 1), "spec pos 6a";
  expect forall k | 1 <= k < 1 :: !Achievable(k, 100000, 1), "spec pos 6b";

  // Pos 7: n=10, S=46, correct=5
  expect Achievable(5, 10, 46), "spec pos 7a";
  expect forall k | 1 <= k < 5 :: !Achievable(k, 10, 46), "spec pos 7b";

  // Pos 8: n=1, S=30, correct=30
  expect Achievable(30, 1, 30), "spec pos 8a";
  expect forall k | 1 <= k < 30 :: !Achievable(k, 1, 30), "spec pos 8b";

  // ════════════════════════════════════════════════
  // SPEC NEGATIVE tests (8 tests)
  // Wrong output must violate at least one ensures clause
  // ════════════════════════════════════════════════

  // Neg 1: n=5, S=11, wrong=4 (correct=3)
  expect !(Achievable(4, 5, 11) && (forall k | 1 <= k < 4 :: !Achievable(k, 5, 11))), "spec neg 1";

  // Neg 2: n=6, S=16, wrong=4 (correct=3)
  expect !(Achievable(4, 6, 16) && (forall k | 1 <= k < 4 :: !Achievable(k, 6, 16))), "spec neg 2";

  // Neg 3: n=14, S=28, wrong=3 (correct=2)
  expect !(Achievable(3, 14, 28) && (forall k | 1 <= k < 3 :: !Achievable(k, 14, 28))), "spec neg 3";

  // Neg 4: n=5, S=29, wrong=7 (correct=6)
  expect !(Achievable(7, 5, 29) && (forall k | 1 <= k < 7 :: !Achievable(k, 5, 29))), "spec neg 4";

  // Neg 5: n=10, S=24, wrong=4 (correct=3)
  expect !(Achievable(4, 10, 24) && (forall k | 1 <= k < 4 :: !Achievable(k, 10, 24))), "spec neg 5";

  // Neg 6: n=1, S=30, wrong=31 (correct=30)
  expect !(Achievable(31, 1, 30) && (forall k | 1 <= k < 31 :: !Achievable(k, 1, 30))), "spec neg 6";

  // Neg 7: n=100000, S=1, wrong=2 (correct=1)
  expect !(Achievable(2, 100000, 1) && (forall k | 1 <= k < 2 :: !Achievable(k, 100000, 1))), "spec neg 7";

  // Neg 8: n=10, S=46, wrong=6 (correct=5)
  expect !(Achievable(6, 10, 46) && (forall k | 1 <= k < 6 :: !Achievable(k, 10, 46))), "spec neg 8";

  // ════════════════════════════════════════════════
  // IMPLEMENTATION tests (full-size inputs, 10 tests)
  // ════════════════════════════════════════════════
  var r: int;

  r := Coins(5, 11);
  expect r == 3, "impl test 1 failed";

  r := Coins(6, 16);
  expect r == 3, "impl test 2 failed";

  r := Coins(14, 28);
  expect r == 2, "impl test 3 failed";

  r := Coins(5, 29);
  expect r == 6, "impl test 4 failed";

  r := Coins(10, 24);
  expect r == 3, "impl test 5 failed";

  r := Coins(1, 30);
  expect r == 30, "impl test 6 failed";

  r := Coins(14969, 66991573);
  expect r == 4476, "impl test 7 failed";

  r := Coins(1, 1000000000);
  expect r == 1000000000, "impl test 8 failed";

  r := Coins(100000, 1);
  expect r == 1, "impl test 9 failed";

  r := Coins(10, 46);
  expect r == 5, "impl test 10 failed";

  print "All tests passed\n";
}