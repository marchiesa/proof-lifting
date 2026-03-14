/*
 * Tests for Problem 4: Minimum Coin Change with Optimality
 *
 * We test the spec predicates on small concrete examples.
 */

ghost predicate IsValidCombination(coins: seq<int>, amount: int, combo: seq<int>)
  requires forall i :: 0 <= i < |coins| ==> coins[i] > 0
{
  |combo| == |coins| &&
  (forall i :: 0 <= i < |combo| ==> combo[i] >= 0) &&
  DotProduct(coins, combo) == amount
}

function DotProduct(a: seq<int>, b: seq<int>): int
  requires |a| == |b|
{
  if |a| == 0 then 0
  else a[0] * b[0] + DotProduct(a[1..], b[1..])
}

function TotalCoins(combo: seq<int>): int
{
  if |combo| == 0 then 0
  else combo[0] + TotalCoins(combo[1..])
}

ghost predicate MinCoinChangeSpec(coins: seq<int>, amount: int, result: int)
  requires forall i :: 0 <= i < |coins| ==> coins[i] > 0
  requires amount >= 0
{
  if result == -1 then
    (forall combo: seq<int> :: !IsValidCombination(coins, amount, combo))
  else
    result >= 0 &&
    (exists combo: seq<int> ::
      IsValidCombination(coins, amount, combo) &&
      TotalCoins(combo) == result) &&
    (forall combo: seq<int> ::
      IsValidCombination(coins, amount, combo) ==>
      TotalCoins(combo) >= result)
}

// Helper lemmas for DotProduct
lemma DotProduct1(a: seq<int>, b: seq<int>)
  requires |a| == 1 && |b| == 1
  ensures DotProduct(a, b) == a[0] * b[0]
{
  assert a[1..] == [];
  assert b[1..] == [];
}

lemma DotProduct2(a: seq<int>, b: seq<int>)
  requires |a| == 2 && |b| == 2
  ensures DotProduct(a, b) == a[0] * b[0] + a[1] * b[1]
{
  assert a[1..] == [a[1]];
  assert b[1..] == [b[1]];
  DotProduct1(a[1..], b[1..]);
}

lemma DotProduct3(a: seq<int>, b: seq<int>)
  requires |a| == 3 && |b| == 3
  ensures DotProduct(a, b) == a[0] * b[0] + a[1] * b[1] + a[2] * b[2]
{
  assert a[1..] == [a[1], a[2]];
  assert b[1..] == [b[1], b[2]];
  DotProduct2(a[1..], b[1..]);
}

// Helper lemmas for TotalCoins
lemma TotalCoins1(c: seq<int>)
  requires |c| == 1
  ensures TotalCoins(c) == c[0]
{
  assert c[1..] == [];
}

lemma TotalCoins2(c: seq<int>)
  requires |c| == 2
  ensures TotalCoins(c) == c[0] + c[1]
{
  assert c[1..] == [c[1]];
  TotalCoins1(c[1..]);
}

lemma TotalCoins3(c: seq<int>)
  requires |c| == 3
  ensures TotalCoins(c) == c[0] + c[1] + c[2]
{
  assert c[1..] == [c[1], c[2]];
  TotalCoins2(c[1..]);
}

// Test 1: coins = [1], amount = 0, result = 0
// Zero amount needs zero coins.
method test1()
{
  var coins := [1];

  // combo = [0]: DotProduct([1],[0]) = 0, TotalCoins([0]) = 0
  var combo := [0];
  DotProduct1(coins, combo);
  TotalCoins1(combo);
  assert DotProduct(coins, combo) == 0;
  assert TotalCoins(combo) == 0;
  assert IsValidCombination(coins, 0, combo);

  // Optimality: any valid combo for amount 0 has TotalCoins >= 0
  // Since all combo[i] >= 0, TotalCoins >= 0 trivially
  assert MinCoinChangeSpec(coins, 0, 0);
}

// Test 2: coins = [1, 5], amount = 6, result = 2
// Best: 1 one + 1 five = 2 coins
method test2()
{
  var coins := [1, 5];

  // Witness: combo = [1, 1] -> 1*1 + 1*5 = 6, total = 2
  var combo := [1, 1];
  DotProduct2(coins, combo);
  TotalCoins2(combo);
  assert DotProduct(coins, combo) == 6;
  assert TotalCoins(combo) == 2;
  assert IsValidCombination(coins, 6, combo);

  // For optimality, we need: any valid combo has TotalCoins >= 2
  // A valid combo [a, b] satisfies: a + 5b = 6, a >= 0, b >= 0
  // Total = a + b = (6 - 5b) + b = 6 - 4b
  // b can be 0 (total=6) or 1 (total=2). So min is 2.
  forall c: seq<int> | IsValidCombination(coins, 6, c)
    ensures TotalCoins(c) >= 2
  {
    DotProduct2(coins, c);
    TotalCoins2(c);
    assert c[0] + 5 * c[1] == 6;
    assert c[0] >= 0 && c[1] >= 0;
    // c[1] <= 1 since 5*c[1] <= 6
    // if c[1] == 0: total = c[0] + 0 = 6 >= 2
    // if c[1] == 1: c[0] = 1, total = 2
  }

  assert MinCoinChangeSpec(coins, 6, 2);
}

// Test 3: coins = [3], amount = 5, result = -1 (impossible)
// 3 does not divide 5
method test3()
{
  var coins := [3];

  forall combo: seq<int> | |combo| == |coins| && (forall i :: 0 <= i < |combo| ==> combo[i] >= 0)
    ensures DotProduct(coins, combo) != 5
  {
    DotProduct1(coins, combo);
    assert DotProduct(coins, combo) == 3 * combo[0];
    // 3 * combo[0] can be 0, 3, 6, 9, ... never 5
    if combo[0] == 0 { assert 3 * combo[0] == 0; }
    else if combo[0] == 1 { assert 3 * combo[0] == 3; }
    else { assert 3 * combo[0] >= 6; }
  }

  assert forall combo: seq<int> :: !IsValidCombination(coins, 5, combo);
  assert MinCoinChangeSpec(coins, 5, -1);
}

// Test 4: coins = [1, 3, 4], amount = 6, result = 2
// Best: 2 coins of value 3 (combo = [0, 2, 0])
method test4()
{
  var coins := [1, 3, 4];

  var combo := [0, 2, 0];
  DotProduct3(coins, combo);
  TotalCoins3(combo);
  assert DotProduct(coins, combo) == 6;
  assert TotalCoins(combo) == 2;
  assert IsValidCombination(coins, 6, combo);

  // Optimality: any valid combo has TotalCoins >= 2
  forall c: seq<int> | IsValidCombination(coins, 6, c)
    ensures TotalCoins(c) >= 2
  {
    DotProduct3(coins, c);
    TotalCoins3(c);
    assert c[0] + 3 * c[1] + 4 * c[2] == 6;
    assert c[0] >= 0 && c[1] >= 0 && c[2] >= 0;
    // total = c[0] + c[1] + c[2]
    // If total <= 1: at most 1 coin, max value = 4. Can't reach 6.
    // If c[0] + c[1] + c[2] <= 1, then c[0]+3*c[1]+4*c[2] <= 4 < 6. Contradiction.
    if c[0] + c[1] + c[2] <= 1 {
      assert c[0] + 3 * c[1] + 4 * c[2] <= 4;
      assert false;
    }
  }

  assert MinCoinChangeSpec(coins, 6, 2);
}
