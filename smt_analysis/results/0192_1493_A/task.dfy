// --- Formal specification predicates ---

ghost predicate AllDistinct(s: seq<int>)
{
  forall i, j | 0 <= i < |s| && 0 <= j < |s| && i != j :: s[i] != s[j]
}

ghost predicate AllInRange(s: seq<int>, n: int)
{
  forall i | 0 <= i < |s| :: 1 <= s[i] <= n
}

ghost predicate Contains(s: seq<int>, x: int)
{
  exists i | 0 <= i < |s| :: s[i] == x
}

// The set of all sums achievable by selecting any subset of elements from s.
// At each step we either include or exclude the last element.
ghost function AchievableSums(s: seq<int>): set<int>
  decreases |s|
{
  if |s| == 0 then {0}
  else
    var prev := AchievableSums(s[..|s|-1]);
    prev + set x | x in prev :: x + s[|s|-1]
}

// No subset of chosen has sum exactly equal to target
ghost predicate NoSubsetSumsTo(chosen: seq<int>, target: int)
{
  target !in AchievableSums(chosen)
}

// A valid anti-knapsack selection: distinct elements from {1..n}, no subset sums to k
ghost predicate IsValidSelection(chosen: seq<int>, n: int, k: int)
{
  AllDistinct(chosen) && AllInRange(chosen, n) && NoSubsetSumsTo(chosen, k)
}

// Maximal: every element from {1..n} not already chosen would create a subset summing to k
ghost predicate IsMaximal(chosen: seq<int>, n: int, k: int)
{
  forall x | 1 <= x <= n && !Contains(chosen, x) ::
    k in AchievableSums(chosen + [x])
}

// --- Method with formal specification ---

method AntiKnapsack(n: int, k: int) returns (chosen: seq<int>)
  requires 1 <= k <= n
  ensures IsValidSelection(chosen, n, k)
  ensures IsMaximal(chosen, n, k)
{
  chosen := [];
  var i := k + 1;
  while i <= n {
    chosen := chosen + [i];
    i := i + 1;
  }
  i := (k + 1) / 2;
  while i <= k - 1 {
    chosen := chosen + [i];
    i := i + 1;
  }
}

// --- Tests with runtime spec verification ---

method TestAntiKnapsack(n: int, k: int, expected: seq<int>)
  requires 1 <= k <= n
{
  var chosen := AntiKnapsack(n, k);
  expect chosen == expected;
  expect IsValidSelection(chosen, n, k);
  expect IsMaximal(chosen, n, k);
}