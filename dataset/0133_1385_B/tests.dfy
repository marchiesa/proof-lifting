predicate IsPermutation(p: seq<int>, n: int)
{
  n >= 1 &&
  |p| == n &&
  (forall i | 1 <= i <= n :: exists j | 0 <= j < n :: p[j] == i)
}

predicate IsMerge(a: seq<int>, s1: seq<int>, s2: seq<int>)
  decreases |a|
{
  if |a| == 0 then
    |s1| == 0 && |s2| == 0
  else
    (|s1| > 0 && a[0] == s1[0] && IsMerge(a[1..], s1[1..], s2)) ||
    (|s2| > 0 && a[0] == s2[0] && IsMerge(a[1..], s1, s2[1..]))
}

method RestorePermutation(n: int, a: seq<int>) returns (p: seq<int>)
  requires n >= 1
  requires |a| == 2 * n
  requires forall i | 0 <= i < |a| :: 1 <= a[i] <= n
  ensures IsPermutation(p, n)
  ensures IsMerge(a, p, p)
{
  var seen: set<int> := {};
  p := [];
  for i := 0 to |a| {
    if a[i] !in seen {
      p := p + [a[i]];
      seen := seen + {a[i]};
    }
  }
}

method Main()
{
  // ===== SPEC POSITIVE TESTS (small inputs, n <= 3) =====

  // Spec positive 1: n=1, a=[1,1], p=[1]
  expect IsPermutation([1], 1), "spec positive 1 (IsPermutation)";
  expect IsMerge([1,1], [1], [1]), "spec positive 1 (IsMerge)";

  // Spec positive 2: n=2, a=[1,1,2,2], p=[1,2]
  expect IsPermutation([1,2], 2), "spec positive 2 (IsPermutation)";
  expect IsMerge([1,1,2,2], [1,2], [1,2]), "spec positive 2 (IsMerge)";

  // Spec positive 3: n=2, a=[1,2,1,2], p=[1,2]
  expect IsPermutation([1,2], 2), "spec positive 3 (IsPermutation)";
  expect IsMerge([1,2,1,2], [1,2], [1,2]), "spec positive 3 (IsMerge)";

  // Spec positive 4: n=2, a=[2,1,2,1], p=[2,1]
  expect IsPermutation([2,1], 2), "spec positive 4 (IsPermutation)";
  expect IsMerge([2,1,2,1], [2,1], [2,1]), "spec positive 4 (IsMerge)";

  // Spec positive 5: n=3, a=[1,2,3,1,2,3], p=[1,2,3]
  expect IsPermutation([1,2,3], 3), "spec positive 5 (IsPermutation)";
  expect IsMerge([1,2,3,1,2,3], [1,2,3], [1,2,3]), "spec positive 5 (IsMerge)";

  // Spec positive 6: n=3, a=[3,3,1,1,2,2], p=[3,1,2]
  expect IsPermutation([3,1,2], 3), "spec positive 6 (IsPermutation)";
  expect IsMerge([3,3,1,1,2,2], [3,1,2], [3,1,2]), "spec positive 6 (IsMerge)";

  // Spec positive 7: n=3, a=[3,1,3,1,2,2], p=[3,1,2]
  expect IsPermutation([3,1,2], 3), "spec positive 7 (IsPermutation)";
  expect IsMerge([3,1,3,1,2,2], [3,1,2], [3,1,2]), "spec positive 7 (IsMerge)";

  // Spec positive 8: n=3, a=[1,1,2,2,3,3], p=[1,2,3]
  expect IsPermutation([1,2,3], 3), "spec positive 8 (IsPermutation)";
  expect IsMerge([1,1,2,2,3,3], [1,2,3], [1,2,3]), "spec positive 8 (IsMerge)";

  // ===== SPEC NEGATIVE TESTS (small inputs, n <= 3) =====

  // Spec negative 1: n=2, a=[1,1,2,2], wrong=[2,2] (from Neg 1 — missing value 1)
  expect !(IsPermutation([2,2], 2) && IsMerge([1,1,2,2], [2,2], [2,2])), "spec negative 1";

  // Spec negative 2: n=1, a=[1,1], wrong=[2] (from Neg 2 — out of range)
  expect !(IsPermutation([2], 1) && IsMerge([1,1], [2], [2])), "spec negative 2";

  // Spec negative 3: n=2, a=[1,2,1,2], wrong=[2,2] (from Neg 5 — missing value 1)
  expect !(IsPermutation([2,2], 2) && IsMerge([1,2,1,2], [2,2], [2,2])), "spec negative 3";

  // Spec negative 4: n=3, a=[1,1,2,2,3,3], wrong=[2,2,3] (from Neg 9 — missing value 1)
  expect !(IsPermutation([2,2,3], 3) && IsMerge([1,1,2,2,3,3], [2,2,3], [2,2,3])), "spec negative 4";

  // Spec negative 5: n=2, a=[2,1,2,1], wrong=[1,1] (scaled Neg 4 — duplicate value)
  expect !(IsPermutation([1,1], 2) && IsMerge([2,1,2,1], [1,1], [1,1])), "spec negative 5";

  // Spec negative 6: n=2, a=[1,1,2,2], wrong=[2,1] (IsPermutation ok but IsMerge fails)
  expect !(IsPermutation([2,1], 2) && IsMerge([1,1,2,2], [2,1], [2,1])), "spec negative 6";

  // Spec negative 7: n=2, a=[1,1,2,2], wrong=[3,2] (scaled Neg 3 — value out of range)
  expect !(IsPermutation([3,2], 2) && IsMerge([1,1,2,2], [3,2], [3,2])), "spec negative 7";

  // ===== IMPLEMENTATION TESTS =====
  var r: seq<int>;

  r := RestorePermutation(2, [1,1,2,2]);
  expect r == [1,2], "impl test 1 failed";

  r := RestorePermutation(4, [1,3,1,4,3,4,2,2]);
  expect r == [1,3,4,2], "impl test 2 failed";

  r := RestorePermutation(5, [1,2,1,2,3,4,3,5,4,5]);
  expect r == [1,2,3,4,5], "impl test 3 failed";

  r := RestorePermutation(3, [1,2,3,1,2,3]);
  expect r == [1,2,3], "impl test 4 failed";

  r := RestorePermutation(4, [2,3,2,4,1,3,4,1]);
  expect r == [2,3,4,1], "impl test 5 failed";

  r := RestorePermutation(1, [1,1]);
  expect r == [1], "impl test 6 failed";

  r := RestorePermutation(4, [4,1,4,3,2,1,3,2]);
  expect r == [4,1,3,2], "impl test 7 failed";

  r := RestorePermutation(4, [2,2,4,4,3,3,1,1]);
  expect r == [2,4,3,1], "impl test 8 failed";

  r := RestorePermutation(5, [5,5,4,4,3,2,3,1,2,1]);
  expect r == [5,4,3,2,1], "impl test 9 failed";

  r := RestorePermutation(2, [1,2,1,2]);
  expect r == [1,2], "impl test 10 failed";

  r := RestorePermutation(10, [7,7,2,3,6,2,4,3,6,4,9,10,8,9,10,1,8,1,5,5]);
  expect r == [7,2,3,6,4,9,10,8,1,5], "impl test 11 failed";

  r := RestorePermutation(4, [4,4,3,3,2,2,1,1]);
  expect r == [4,3,2,1], "impl test 12 failed";

  r := RestorePermutation(6, [5,5,1,4,1,4,6,2,6,2,3,3]);
  expect r == [5,1,4,6,2,3], "impl test 13 failed";

  r := RestorePermutation(7, [1,1,4,4,7,7,2,2,5,6,3,5,6,3]);
  expect r == [1,4,7,2,5,6,3], "impl test 14 failed";

  r := RestorePermutation(5, [5,4,3,5,2,4,3,2,1,1]);
  expect r == [5,4,3,2,1], "impl test 15 failed";

  r := RestorePermutation(3, [3,3,1,1,2,2]);
  expect r == [3,1,2], "impl test 16 failed";

  r := RestorePermutation(10, [8,3,8,3,1,4,5,9,2,6,1,4,5,10,7,9,2,6,10,7]);
  expect r == [8,3,1,4,5,9,2,6,10,7], "impl test 17 failed";

  r := RestorePermutation(9, [4,4,8,8,9,7,9,7,3,3,5,5,6,6,2,2,1,1]);
  expect r == [4,8,9,7,3,5,6,2,1], "impl test 18 failed";

  r := RestorePermutation(9, [3,4,3,4,1,1,9,9,8,8,6,7,5,6,2,7,5,2]);
  expect r == [3,4,1,9,8,6,7,5,2], "impl test 19 failed";

  r := RestorePermutation(5, [5,5,3,4,3,1,4,1,2,2]);
  expect r == [5,3,4,1,2], "impl test 20 failed";

  r := RestorePermutation(9, [1,8,1,9,8,3,9,3,2,6,5,4,7,2,6,5,4,7]);
  expect r == [1,8,9,3,2,6,5,4,7], "impl test 21 failed";

  r := RestorePermutation(9, [8,3,8,3,5,5,2,2,6,6,7,7,1,9,4,1,9,4]);
  expect r == [8,3,5,2,6,7,1,9,4], "impl test 22 failed";

  r := RestorePermutation(10, [5,5,3,1,2,6,9,7,4,8,3,1,10,2,6,9,7,4,8,10]);
  expect r == [5,3,1,2,6,9,7,4,8,10], "impl test 23 failed";

  r := RestorePermutation(2, [2,1,2,1]);
  expect r == [2,1], "impl test 24 failed";

  r := RestorePermutation(6, [3,3,4,4,6,6,5,2,5,2,1,1]);
  expect r == [3,4,6,5,2,1], "impl test 25 failed";

  r := RestorePermutation(3, [3,1,3,1,2,2]);
  expect r == [3,1,2], "impl test 26 failed";

  r := RestorePermutation(5, [2,2,3,3,1,5,1,5,4,4]);
  expect r == [2,3,1,5,4], "impl test 27 failed";

  r := RestorePermutation(9, [2,2,8,3,8,3,4,5,7,4,9,6,5,7,1,9,6,1]);
  expect r == [2,8,3,4,5,7,9,6,1], "impl test 28 failed";

  print "All tests passed\n";
}