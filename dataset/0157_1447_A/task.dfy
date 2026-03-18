// --- Formal Specification: Add Candies Problem ---
//
// n bags, bag i (1-indexed) initially has i candies.
// Perform m operations (1 ≤ m ≤ 1000). In operation j, pick one bag
// and add j candies to every OTHER bag. After all operations, all bags
// must contain equal candies.

// Candies gained by `bag` from operations described by sequence `a`.
// Operation j (1-indexed) adds j candies to all bags except a[j-1].
ghost function OperationGain(a: seq<int>, bag: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else OperationGain(a[..|a|-1], bag) + (if a[|a|-1] == bag then 0 else |a|)
}

// Final candies in bag `bag` (1-indexed, starts with `bag` candies).
ghost function FinalCandies(n: int, a: seq<int>, bag: int): int
  requires 1 <= bag <= n
{
  bag + OperationGain(a, bag)
}

// After all operations, every bag has the same number of candies.
ghost predicate AllBagsEqual(n: int, a: seq<int>)
  requires n >= 1
{
  forall i | 1 <= i <= n :: FinalCandies(n, a, i) == FinalCandies(n, a, 1)
}

// Each operation picks a valid bag index.
ghost predicate ValidChoices(n: int, a: seq<int>)
{
  forall j | 0 <= j < |a| :: 1 <= a[j] <= n
}

// A complete valid solution to the Add Candies problem.
ghost predicate ValidSolution(n: int, m: int, a: seq<int>)
  requires n >= 1
{
  m >= 1 &&
  |a| == m &&
  ValidChoices(n, a) &&
  AllBagsEqual(n, a)
}

// --- Methods ---

method AddCandies(n: int) returns (m: int, a: seq<int>)
  requires 1 <= n <= 1000
  ensures ValidSolution(n, m, a)
{
  m := n;
  a := [];
  var i := 1;
  while i <= n {
    a := a + [i];
    i := i + 1;
  }
}

method MakeSeq1ToN(n: int) returns (s: seq<int>)
{
  s := [];
  var i := 1;
  while i <= n {
    s := s + [i];
    i := i + 1;
  }
}

method CheckAddCandies(n: int, testName: string)
  requires 1 <= n <= 1000
{
  var m, a := AddCandies(n);
  var expected := MakeSeq1ToN(n);
  expect m == n, testName + ": m mismatch";
  expect a == expected, testName + ": a mismatch";
}