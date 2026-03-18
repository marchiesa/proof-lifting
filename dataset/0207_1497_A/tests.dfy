// --- Specification ---

function SeqToSet(s: seq<int>): set<int>
  decreases |s|
{
  if |s| == 0 then {} else SeqToSet(s[..|s|-1]) + {s[|s|-1]}
}

function MexSearch(s: set<int>, k: nat, fuel: nat): nat
  decreases fuel
{
  if fuel == 0 || k !in s then k
  else MexSearch(s, k + 1, fuel - 1)
}

function Mex(s: set<int>): nat
{
  MexSearch(s, 0, |s|)
}

function PrefixMexSum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0
  else PrefixMexSum(a[..|a|-1]) + Mex(SeqToSet(a))
}

predicate IsPermutation(a: seq<int>, b: seq<int>)
{
  multiset(a) == multiset(b)
}

predicate IsSorted(s: seq<int>)
{
  forall i | 0 <= i < |s| - 1 :: s[i] <= s[i + 1]
}

predicate NoBetterArrangement(target: int, chosen: seq<int>, remaining: seq<int>)
  decreases |remaining|
{
  if |remaining| == 0 then
    PrefixMexSum(chosen) <= target
  else
    forall i | 0 <= i < |remaining| ::
      NoBetterArrangement(
        target,
        chosen + [remaining[i]],
        remaining[..i] + remaining[i+1..]
      )
}

// --- Implementation ---

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures IsPermutation(s, sorted)
  ensures IsSorted(sorted)
{
  var arr := s;
  for i := 1 to |arr| {
    var j := i;
    while j > 0 && arr[j - 1] > arr[j]
      decreases j
    {
      var tmp := arr[j];
      arr := arr[j := arr[j - 1]];
      arr := arr[j - 1 := tmp];
      j := j - 1;
    }
  }
  sorted := arr;
}

method Meximization(a: seq<int>) returns (b: seq<int>)
  ensures IsPermutation(a, b)
  ensures NoBetterArrangement(PrefixMexSum(b), [], a)
{
  var s: set<int> := {};
  var res: seq<int> := [];
  var ss: seq<int> := [];
  for i := 0 to |a| {
    var x := a[i];
    if x in s {
      ss := ss + [x];
    } else {
      res := res + [x];
    }
    s := s + {x};
  }
  res := SortSeq(res);
  b := res + ss;
}

method Main()
{
  // ========================
  // SPEC POSITIVE TESTS
  // ========================
  // Testing both ensures: IsPermutation(a, b) and NoBetterArrangement(PrefixMexSum(b), [], a)
  // Using small inputs (length 1-3) to keep NoBetterArrangement feasible.

  // From Test 6 / Test 1.3: [0] -> [0]
  expect IsPermutation([0], [0]), "spec pos 1a";
  expect NoBetterArrangement(PrefixMexSum([0]), [], [0]), "spec pos 1b";

  // From Test 2: [2] -> [2]
  expect IsPermutation([2], [2]), "spec pos 2a";
  expect NoBetterArrangement(PrefixMexSum([2]), [], [2]), "spec pos 2b";

  // From Test 11.1: [0, 0] -> [0, 0]
  expect IsPermutation([0, 0], [0, 0]), "spec pos 3a";
  expect NoBetterArrangement(PrefixMexSum([0, 0]), [], [0, 0]), "spec pos 3b";

  // From Test 8.2: [0, 1, 0] -> [0, 1, 0]
  expect IsPermutation([0, 1, 0], [0, 1, 0]), "spec pos 4a";
  expect NoBetterArrangement(PrefixMexSum([0, 1, 0]), [], [0, 1, 0]), "spec pos 4b";

  // From Test 11.2: [0, 1, 2] -> [0, 1, 2]
  expect IsPermutation([0, 1, 2], [0, 1, 2]), "spec pos 5a";
  expect NoBetterArrangement(PrefixMexSum([0, 1, 2]), [], [0, 1, 2]), "spec pos 5b";

  // Scaled from Test 10: [5] -> [5]
  expect IsPermutation([5], [5]), "spec pos 6a";
  expect NoBetterArrangement(PrefixMexSum([5]), [], [5]), "spec pos 6b";

  // Scaled from Test 8.1: [3, 3] -> [3, 3]
  expect IsPermutation([3, 3], [3, 3]), "spec pos 7a";
  expect NoBetterArrangement(PrefixMexSum([3, 3]), [], [3, 3]), "spec pos 7b";

  // Scaled from Test 3: [1, 1] -> [1, 1]
  expect IsPermutation([1, 1], [1, 1]), "spec pos 8a";
  expect NoBetterArrangement(PrefixMexSum([1, 1]), [], [1, 1]), "spec pos 8b";

  // ========================
  // SPEC NEGATIVE TESTS
  // ========================
  // Testing !IsPermutation for wrong outputs (element values changed, so not permutations)

  // Neg 6 scaled: input [0], wrong [1]
  expect !IsPermutation([0], [1]), "spec neg 1";

  // Neg 2: input [2], wrong [3]
  expect !IsPermutation([2], [3]), "spec neg 2";

  // Neg 5 scaled: input [0, 0], wrong [1, 0]
  expect !IsPermutation([0, 0], [1, 0]), "spec neg 3";

  // Neg 4 scaled: input [0, 1, 2], wrong [1, 1, 2]
  expect !IsPermutation([0, 1, 2], [1, 1, 2]), "spec neg 4";

  // Neg 8.1 scaled: input [3, 3], wrong [4, 3]
  expect !IsPermutation([3, 3], [4, 3]), "spec neg 5";

  // Neg 7 scaled: input [0, 1], wrong [1, 1]
  expect !IsPermutation([0, 1], [1, 1]), "spec neg 6";

  // Neg 9 scaled: input [0, 1, 0], wrong [1, 1, 0]
  expect !IsPermutation([0, 1, 0], [1, 1, 0]), "spec neg 7";

  // NoBetterArrangement negatives: suboptimal permutations that ARE valid
  // permutations but have lower PrefixMexSum than optimal.

  // [1, 0] is a suboptimal permutation of [0, 1]: PrefixMexSum([1,0])=2 < PrefixMexSum([0,1])=3
  expect !NoBetterArrangement(PrefixMexSum([1, 0]), [], [0, 1]), "spec neg NBA 1";

  // [2, 1, 0] is suboptimal for [0, 1, 2]: PrefixMexSum([2,1,0])=3 < PrefixMexSum([0,1,2])=6
  expect !NoBetterArrangement(PrefixMexSum([2, 1, 0]), [], [0, 1, 2]), "spec neg NBA 2";

  // [1, 0, 0] is suboptimal for [0, 1, 0]: PrefixMexSum([1,0,0])=4 < PrefixMexSum([0,1,0])=5
  expect !NoBetterArrangement(PrefixMexSum([1, 0, 0]), [], [0, 1, 0]), "spec neg NBA 3";

  // ========================
  // IMPLEMENTATION TESTS
  // ========================

  // Test 1, case 1
  var r := Meximization([4, 2, 0, 1, 3, 3, 7]);
  expect r == [0, 1, 2, 3, 4, 7, 3], "impl test 1.1 failed";

  // Test 1, case 2
  r := Meximization([2, 2, 8, 6, 9]);
  expect r == [2, 6, 8, 9, 2], "impl test 1.2 failed";

  // Test 1, case 3
  r := Meximization([0]);
  expect r == [0], "impl test 1.3 failed";

  // Test 2
  r := Meximization([2]);
  expect r == [2], "impl test 2 failed";

  // Test 3
  var ones := seq(100, (i: int) => 1);
  r := Meximization(ones);
  expect r == ones, "impl test 3 failed";

  // Test 4
  r := Meximization([0, 1, 2, 3, 4]);
  expect r == [0, 1, 2, 3, 4], "impl test 4 failed";

  // Test 5
  r := Meximization([0, 0, 0, 0, 0, 0]);
  expect r == [0, 0, 0, 0, 0, 0], "impl test 5 failed";

  // Test 6
  r := Meximization([0]);
  expect r == [0], "impl test 6 failed";

  // Test 7
  r := Meximization([0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
  expect r == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9], "impl test 7 failed";

  // Test 8, case 1
  r := Meximization([3, 3, 3, 3]);
  expect r == [3, 3, 3, 3], "impl test 8.1 failed";

  // Test 8, case 2
  r := Meximization([0, 1, 0]);
  expect r == [0, 1, 0], "impl test 8.2 failed";

  // Test 9
  r := Meximization([0, 1, 0, 1, 0, 1, 2, 3]);
  expect r == [0, 1, 2, 3, 0, 1, 0, 1], "impl test 9 failed";

  // Test 10
  r := Meximization([5, 6, 7, 8, 9]);
  expect r == [5, 6, 7, 8, 9], "impl test 10 failed";

  // Test 11, case 1
  r := Meximization([0, 0]);
  expect r == [0, 0], "impl test 11.1 failed";

  // Test 11, case 2
  r := Meximization([0, 1, 2]);
  expect r == [0, 1, 2], "impl test 11.2 failed";

  // Test 11, case 3
  r := Meximization([1, 2, 3, 4]);
  expect r == [1, 2, 3, 4], "impl test 11.3 failed";

  // Test 12
  r := Meximization([0, 1, 2, 0, 1, 2, 0, 1, 2, 3]);
  expect r == [0, 1, 2, 3, 0, 1, 2, 0, 1, 2], "impl test 12 failed";

  print "All tests passed\n";
}