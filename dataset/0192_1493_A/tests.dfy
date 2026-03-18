// --- Formal specification predicates ---

predicate AllDistinct(s: seq<int>)
{
  forall i, j | 0 <= i < |s| && 0 <= j < |s| && i != j :: s[i] != s[j]
}

predicate AllInRange(s: seq<int>, n: int)
{
  forall i | 0 <= i < |s| :: 1 <= s[i] <= n
}

predicate Contains(s: seq<int>, x: int)
{
  exists i | 0 <= i < |s| :: s[i] == x
}

function AchievableSums(s: seq<int>): set<int>
  decreases |s|
{
  if |s| == 0 then {0}
  else
    var prev := AchievableSums(s[..|s|-1]);
    prev + set x | x in prev :: x + s[|s|-1]
}

predicate NoSubsetSumsTo(chosen: seq<int>, target: int)
{
  target !in AchievableSums(chosen)
}

predicate IsValidSelection(chosen: seq<int>, n: int, k: int)
{
  AllDistinct(chosen) && AllInRange(chosen, n) && NoSubsetSumsTo(chosen, k)
}

predicate IsMaximal(chosen: seq<int>, n: int, k: int)
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

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Verify IsValidSelection and IsMaximal accept correct outputs (small inputs only)

  // From test pair (1,1) -> []
  expect IsValidSelection([], 1, 1), "spec positive 1a";
  expect IsMaximal([], 1, 1), "spec positive 1b";

  // From test pair (2,1) -> [2]
  expect IsValidSelection([2], 2, 1), "spec positive 2a";
  expect IsMaximal([2], 2, 1), "spec positive 2b";

  // From test pair (2,2) -> [1]
  expect IsValidSelection([1], 2, 2), "spec positive 3a";
  expect IsMaximal([1], 2, 2), "spec positive 3b";

  // From test pair (3,1) -> [2,3]
  expect IsValidSelection([2, 3], 3, 1), "spec positive 4a";
  expect IsMaximal([2, 3], 3, 1), "spec positive 4b";

  // From test pair (3,2) -> [3,1]
  expect IsValidSelection([3, 1], 3, 2), "spec positive 5a";
  expect IsMaximal([3, 1], 3, 2), "spec positive 5b";

  // From test pair (3,3) -> [2]
  expect IsValidSelection([2], 3, 3), "spec positive 6a";
  expect IsMaximal([2], 3, 3), "spec positive 6b";

  // From test pair (4,1) -> [2,3,4]
  expect IsValidSelection([2, 3, 4], 4, 1), "spec positive 7a";
  expect IsMaximal([2, 3, 4], 4, 1), "spec positive 7b";

  // From test pair (4,2) -> [3,4,1]
  expect IsValidSelection([3, 4, 1], 4, 2), "spec positive 8a";
  expect IsMaximal([3, 4, 1], 4, 2), "spec positive 8b";

  // From test pair (4,3) -> [4,2]
  expect IsValidSelection([4, 2], 4, 3), "spec positive 9a";
  expect IsMaximal([4, 2], 4, 3), "spec positive 9b";

  // From test pair (4,4) -> [2,3]
  expect IsValidSelection([2, 3], 4, 4), "spec positive 10a";
  expect IsMaximal([2, 3], 4, 4), "spec positive 10b";

  // From test pair (5,1) -> [2,3,4,5]
  expect IsValidSelection([2, 3, 4, 5], 5, 1), "spec positive 11a";
  expect IsMaximal([2, 3, 4, 5], 5, 1), "spec positive 11b";

  // From test pair (5,3) -> [4,5,2]
  expect IsValidSelection([4, 5, 2], 5, 3), "spec positive 12a";
  expect IsMaximal([4, 5, 2], 5, 3), "spec positive 12b";

  // From test pair (5,5) -> [3,4]
  expect IsValidSelection([3, 4], 5, 5), "spec positive 13a";
  expect IsMaximal([3, 4], 5, 5), "spec positive 13b";

  // ===== SPEC NEGATIVE TESTS =====
  // Verify spec rejects wrong outputs (small inputs only)
  // Wrong sequences derived from negative test pairs (count+1 -> extra invalid element)

  // Neg 4: (1,1), correct=[], wrong=[1] — {1} sums to k=1, fails IsValidSelection
  expect !(IsValidSelection([1], 1, 1) && IsMaximal([1], 1, 1)), "spec negative 1";

  // Neg 9 case 1: (2,1), correct=[2], wrong=[1,2] — {1} sums to k=1
  expect !(IsValidSelection([1, 2], 2, 1) && IsMaximal([1, 2], 2, 1)), "spec negative 2";

  // Neg 9 case 2: (3,3), correct=[2], wrong=[1,2] — {1,2} sums to k=3
  expect !(IsValidSelection([1, 2], 3, 3) && IsMaximal([1, 2], 3, 3)), "spec negative 3";

  // Neg 1 case 1: (3,2), correct=[3,1], wrong=[2,3,1] — {2} sums to k=2
  expect !(IsValidSelection([2, 3, 1], 3, 2) && IsMaximal([2, 3, 1], 3, 2)), "spec negative 4";

  // Neg 9 case 5: (4,4), correct=[2,3], wrong=[1,2,3] — {1,3} sums to k=4
  expect !(IsValidSelection([1, 2, 3], 4, 4) && IsMaximal([1, 2, 3], 4, 4)), "spec negative 5";

  // Neg 6 scaled: (2,2), correct=[1], wrong=[1,2] — {2} sums to k=2
  expect !(IsValidSelection([1, 2], 2, 2) && IsMaximal([1, 2], 2, 2)), "spec negative 6";

  // Valid but non-maximal: (3,2), wrong=[3] — can still add 1 without subset summing to 2
  expect !(IsValidSelection([3], 3, 2) && IsMaximal([3], 3, 2)), "spec negative 7";

  // Valid but non-maximal: (4,4), wrong=[3] — can still add 2 without subset summing to 4
  expect !(IsValidSelection([3], 4, 4) && IsMaximal([3], 4, 4)), "spec negative 8";

  // Neg 1 case 2 scaled: (3,1), wrong=[1,2,3] — {1} sums to k=1
  expect !(IsValidSelection([1, 2, 3], 3, 1) && IsMaximal([1, 2, 3], 3, 1)), "spec negative 9";

  // Neg 3 scaled: (4,2), correct=[3,4,1], wrong=[2,3,4,1] — {2} sums to k=2
  expect !(IsValidSelection([2, 3, 4, 1], 4, 2) && IsMaximal([2, 3, 4, 1], 4, 2)), "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====
  var chosen: seq<int>;

  // n=1
  chosen := AntiKnapsack(1, 1);
  expect chosen == [], "impl test 1 failed";

  // n=2
  chosen := AntiKnapsack(2, 1);
  expect chosen == [2], "impl test 2 failed";
  chosen := AntiKnapsack(2, 2);
  expect chosen == [1], "impl test 3 failed";

  // n=3
  chosen := AntiKnapsack(3, 1);
  expect chosen == [2, 3], "impl test 4 failed";
  chosen := AntiKnapsack(3, 2);
  expect chosen == [3, 1], "impl test 5 failed";
  chosen := AntiKnapsack(3, 3);
  expect chosen == [2], "impl test 6 failed";

  // n=4
  chosen := AntiKnapsack(4, 1);
  expect chosen == [2, 3, 4], "impl test 7 failed";
  chosen := AntiKnapsack(4, 2);
  expect chosen == [3, 4, 1], "impl test 8 failed";
  chosen := AntiKnapsack(4, 3);
  expect chosen == [4, 2], "impl test 9 failed";
  chosen := AntiKnapsack(4, 4);
  expect chosen == [2, 3], "impl test 10 failed";

  // n=5
  chosen := AntiKnapsack(5, 1);
  expect chosen == [2, 3, 4, 5], "impl test 11 failed";
  chosen := AntiKnapsack(5, 2);
  expect chosen == [3, 4, 5, 1], "impl test 12 failed";
  chosen := AntiKnapsack(5, 3);
  expect chosen == [4, 5, 2], "impl test 13 failed";
  chosen := AntiKnapsack(5, 4);
  expect chosen == [5, 2, 3], "impl test 14 failed";
  chosen := AntiKnapsack(5, 5);
  expect chosen == [3, 4], "impl test 15 failed";

  // n=6
  chosen := AntiKnapsack(6, 1);
  expect chosen == [2, 3, 4, 5, 6], "impl test 16 failed";
  chosen := AntiKnapsack(6, 2);
  expect chosen == [3, 4, 5, 6, 1], "impl test 17 failed";
  chosen := AntiKnapsack(6, 3);
  expect chosen == [4, 5, 6, 2], "impl test 18 failed";
  chosen := AntiKnapsack(6, 4);
  expect chosen == [5, 6, 2, 3], "impl test 19 failed";
  chosen := AntiKnapsack(6, 5);
  expect chosen == [6, 3, 4], "impl test 20 failed";
  chosen := AntiKnapsack(6, 6);
  expect chosen == [3, 4, 5], "impl test 21 failed";

  // n=7
  chosen := AntiKnapsack(7, 1);
  expect chosen == [2, 3, 4, 5, 6, 7], "impl test 22 failed";
  chosen := AntiKnapsack(7, 2);
  expect chosen == [3, 4, 5, 6, 7, 1], "impl test 23 failed";
  chosen := AntiKnapsack(7, 3);
  expect chosen == [4, 5, 6, 7, 2], "impl test 24 failed";
  chosen := AntiKnapsack(7, 4);
  expect chosen == [5, 6, 7, 2, 3], "impl test 25 failed";
  chosen := AntiKnapsack(7, 5);
  expect chosen == [6, 7, 3, 4], "impl test 26 failed";
  chosen := AntiKnapsack(7, 6);
  expect chosen == [7, 3, 4, 5], "impl test 27 failed";
  chosen := AntiKnapsack(7, 7);
  expect chosen == [4, 5, 6], "impl test 28 failed";

  // n=8
  chosen := AntiKnapsack(8, 1);
  expect chosen == [2, 3, 4, 5, 6, 7, 8], "impl test 29 failed";
  chosen := AntiKnapsack(8, 2);
  expect chosen == [3, 4, 5, 6, 7, 8, 1], "impl test 30 failed";
  chosen := AntiKnapsack(8, 3);
  expect chosen == [4, 5, 6, 7, 8, 2], "impl test 31 failed";
  chosen := AntiKnapsack(8, 4);
  expect chosen == [5, 6, 7, 8, 2, 3], "impl test 32 failed";
  chosen := AntiKnapsack(8, 5);
  expect chosen == [6, 7, 8, 3, 4], "impl test 33 failed";
  chosen := AntiKnapsack(8, 6);
  expect chosen == [7, 8, 3, 4, 5], "impl test 34 failed";
  chosen := AntiKnapsack(8, 7);
  expect chosen == [8, 4, 5, 6], "impl test 35 failed";
  chosen := AntiKnapsack(8, 8);
  expect chosen == [4, 5, 6, 7], "impl test 36 failed";

  // n=9
  chosen := AntiKnapsack(9, 1);
  expect chosen == [2, 3, 4, 5, 6, 7, 8, 9], "impl test 37 failed";
  chosen := AntiKnapsack(9, 2);
  expect chosen == [3, 4, 5, 6, 7, 8, 9, 1], "impl test 38 failed";
  chosen := AntiKnapsack(9, 3);
  expect chosen == [4, 5, 6, 7, 8, 9, 2], "impl test 39 failed";
  chosen := AntiKnapsack(9, 4);
  expect chosen == [5, 6, 7, 8, 9, 2, 3], "impl test 40 failed";
  chosen := AntiKnapsack(9, 5);
  expect chosen == [6, 7, 8, 9, 3, 4], "impl test 41 failed";
  chosen := AntiKnapsack(9, 6);
  expect chosen == [7, 8, 9, 3, 4, 5], "impl test 42 failed";
  chosen := AntiKnapsack(9, 7);
  expect chosen == [8, 9, 4, 5, 6], "impl test 43 failed";
  chosen := AntiKnapsack(9, 8);
  expect chosen == [9, 4, 5, 6, 7], "impl test 44 failed";
  chosen := AntiKnapsack(9, 9);
  expect chosen == [5, 6, 7, 8], "impl test 45 failed";

  // n=10
  chosen := AntiKnapsack(10, 1);
  expect chosen == [2, 3, 4, 5, 6, 7, 8, 9, 10], "impl test 46 failed";
  chosen := AntiKnapsack(10, 2);
  expect chosen == [3, 4, 5, 6, 7, 8, 9, 10, 1], "impl test 47 failed";
  chosen := AntiKnapsack(10, 3);
  expect chosen == [4, 5, 6, 7, 8, 9, 10, 2], "impl test 48 failed";
  chosen := AntiKnapsack(10, 4);
  expect chosen == [5, 6, 7, 8, 9, 10, 2, 3], "impl test 49 failed";
  chosen := AntiKnapsack(10, 5);
  expect chosen == [6, 7, 8, 9, 10, 3, 4], "impl test 50 failed";
  chosen := AntiKnapsack(10, 6);
  expect chosen == [7, 8, 9, 10, 3, 4, 5], "impl test 51 failed";
  chosen := AntiKnapsack(10, 7);
  expect chosen == [8, 9, 10, 4, 5, 6], "impl test 52 failed";
  chosen := AntiKnapsack(10, 8);
  expect chosen == [9, 10, 4, 5, 6, 7], "impl test 53 failed";
  chosen := AntiKnapsack(10, 9);
  expect chosen == [10, 5, 6, 7, 8], "impl test 54 failed";
  chosen := AntiKnapsack(10, 10);
  expect chosen == [5, 6, 7, 8, 9], "impl test 55 failed";

  // n=15
  chosen := AntiKnapsack(15, 1);
  expect chosen == [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], "impl test 56 failed";
  chosen := AntiKnapsack(15, 2);
  expect chosen == [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1], "impl test 57 failed";
  chosen := AntiKnapsack(15, 3);
  expect chosen == [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 2], "impl test 58 failed";
  chosen := AntiKnapsack(15, 4);
  expect chosen == [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 2, 3], "impl test 59 failed";
  chosen := AntiKnapsack(15, 5);
  expect chosen == [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 3, 4], "impl test 60 failed";
  chosen := AntiKnapsack(15, 6);
  expect chosen == [7, 8, 9, 10, 11, 12, 13, 14, 15, 3, 4, 5], "impl test 61 failed";
  chosen := AntiKnapsack(15, 7);
  expect chosen == [8, 9, 10, 11, 12, 13, 14, 15, 4, 5, 6], "impl test 62 failed";
  chosen := AntiKnapsack(15, 8);
  expect chosen == [9, 10, 11, 12, 13, 14, 15, 4, 5, 6, 7], "impl test 63 failed";
  chosen := AntiKnapsack(15, 9);
  expect chosen == [10, 11, 12, 13, 14, 15, 5, 6, 7, 8], "impl test 64 failed";
  chosen := AntiKnapsack(15, 10);
  expect chosen == [11, 12, 13, 14, 15, 5, 6, 7, 8, 9], "impl test 65 failed";
  chosen := AntiKnapsack(15, 11);
  expect chosen == [12, 13, 14, 15, 6, 7, 8, 9, 10], "impl test 66 failed";
  chosen := AntiKnapsack(15, 12);
  expect chosen == [13, 14, 15, 6, 7, 8, 9, 10, 11], "impl test 67 failed";
  chosen := AntiKnapsack(15, 13);
  expect chosen == [14, 15, 7, 8, 9, 10, 11, 12], "impl test 68 failed";
  chosen := AntiKnapsack(15, 14);
  expect chosen == [15, 7, 8, 9, 10, 11, 12, 13], "impl test 69 failed";
  chosen := AntiKnapsack(15, 15);
  expect chosen == [8, 9, 10, 11, 12, 13, 14], "impl test 70 failed";

  // Larger cases
  chosen := AntiKnapsack(20, 11);
  expect chosen == [12, 13, 14, 15, 16, 17, 18, 19, 20, 6, 7, 8, 9, 10], "impl test 71 failed";
  chosen := AntiKnapsack(30, 15);
  expect chosen == [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 8, 9, 10, 11, 12, 13, 14], "impl test 72 failed";
  chosen := AntiKnapsack(50, 25);
  expect chosen == [26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24], "impl test 73 failed";

  print "All tests passed\n";
}