// Spec predicates and functions
predicate AllOnes(s: seq<int>, l: int, r: int)
{
  0 <= l <= r < |s| && forall i | l <= i <= r :: s[i] == 1
}

predicate CanShiftRight(s: seq<int>, l: int, r: int)
{
  AllOnes(s, l, r) && r + 1 < |s| && s[r + 1] == 0
}

function ApplyShiftRight(s: seq<int>, l: int, r: int): seq<int>
  requires CanShiftRight(s, l, r)
{
  s[l := 0][r + 1 := 1]
}

predicate CanShiftLeft(s: seq<int>, l: int, r: int)
{
  AllOnes(s, l, r) && l - 1 >= 0 && s[l - 1] == 0
}

function ApplyShiftLeft(s: seq<int>, l: int, r: int): seq<int>
  requires CanShiftLeft(s, l, r)
{
  s[r := 0][l - 1 := 1]
}

predicate BooksContiguous(s: seq<int>)
{
  forall i, j, k | 0 <= i < j < k < |s| :: !(s[i] == 1 && s[j] == 0 && s[k] == 1)
}

predicate Reachable(s: seq<int>, steps: nat)
  decreases steps
{
  BooksContiguous(s)
  || (steps > 0
      && (exists l, r | 0 <= l <= r < |s| ::
            (CanShiftRight(s, l, r) && Reachable(ApplyShiftRight(s, l, r), steps - 1))
            || (CanShiftLeft(s, l, r) && Reachable(ApplyShiftLeft(s, l, r), steps - 1))))
}

method YetAnotherBookshelf(a: seq<int>) returns (moves: int)
  requires forall i | 0 <= i < |a| :: a[i] == 0 || a[i] == 1
  ensures moves >= 0 && Reachable(a, moves) && (moves == 0 || !Reachable(a, moves - 1))
{
  var n := |a|;
  var one := 0;
  var i := 0;
  while i < n {
    one := one + a[i];
    i := i + 1;
  }

  if one == 0 {
    return 0;
  }

  var first := 0;
  i := 0;
  while i < n {
    if a[i] == 1 {
      first := i;
      break;
    }
    i := i + 1;
  }

  var last := n;
  i := n - 1;
  while i >= 0 {
    if a[i] == 1 {
      last := i;
      break;
    }
    i := i - 1;
  }

  moves := last - first - one + 1;
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // ensures: moves >= 0 && Reachable(a, moves) && (moves == 0 || !Reachable(a, moves - 1))
  // For moves==0 cases, only Reachable(a, 0) is the non-trivial conjunct.

  // Test 3: [1] -> 0
  expect Reachable([1], 0), "spec pos 1";

  // Test 1.2: [1,0,0] -> 0
  expect Reachable([1,0,0], 0), "spec pos 2";

  // Test 5: [1,1,1] -> 0
  expect Reachable([1,1,1], 0), "spec pos 3";

  // Test 8.2: [0,1,0] -> 0
  expect Reachable([0,1,0], 0), "spec pos 4";

  // Test 10.2: [1,1] -> 0
  expect Reachable([1,1], 0), "spec pos 5";

  // Scaled from Test 2: [0,1,1] -> 0
  expect Reachable([0,1,1], 0), "spec pos 6";

  // Scaled from Test 4: [1,0,1] -> 1 (full ensures check)
  expect Reachable([1,0,1], 1), "spec pos 7a";
  expect !Reachable([1,0,1], 0), "spec pos 7b";

  // ===== SPEC NEGATIVE TESTS =====
  // Wrong output must fail the optimality condition:
  // !(Reachable(a, wrong) && (wrong == 0 || !Reachable(a, wrong - 1)))

  // Neg 3: [1], wrong=1 (correct=0)
  expect !(Reachable([1], 1) && !Reachable([1], 0)), "spec neg 1";

  // Neg 5: [1,1,1], wrong=1 (correct=0)
  expect !(Reachable([1,1,1], 1) && !Reachable([1,1,1], 0)), "spec neg 2";

  // Scaled Neg 2: [0,1,1], wrong=1 (correct=0)
  expect !(Reachable([0,1,1], 1) && !Reachable([0,1,1], 0)), "spec neg 3";

  // Scaled Neg 4: [1,0,1], wrong=2 (correct=1)
  expect !(Reachable([1,0,1], 2) && !Reachable([1,0,1], 1)), "spec neg 4";

  // Scaled Neg 9: [1,0,0], wrong=1 (correct=0)
  expect !(Reachable([1,0,0], 1) && !Reachable([1,0,0], 0)), "spec neg 5";

  // Scaled Neg 7: [0,1,0], wrong=1 (correct=0)
  expect !(Reachable([0,1,0], 1) && !Reachable([0,1,0], 0)), "spec neg 6";

  // Scaled Neg 10: [1,1], wrong=1 (correct=0)
  expect !(Reachable([1,1], 1) && !Reachable([1,1], 0)), "spec neg 7";

  // ===== IMPLEMENTATION TESTS =====

  var r1 := YetAnotherBookshelf([0, 0, 1, 0, 1, 0, 1]);
  expect r1 == 2, "impl 1.1";

  var r2 := YetAnotherBookshelf([1, 0, 0]);
  expect r2 == 0, "impl 1.2";

  var r3 := YetAnotherBookshelf([1, 1, 0, 0, 1]);
  expect r3 == 2, "impl 1.3";

  var r4 := YetAnotherBookshelf([1, 0, 0, 0, 0, 1]);
  expect r4 == 4, "impl 1.4";

  var r5 := YetAnotherBookshelf([1, 1, 0, 1, 1]);
  expect r5 == 1, "impl 1.5";

  var r6 := YetAnotherBookshelf([0, 0, 0, 1, 1, 1, 1, 1]);
  expect r6 == 0, "impl 2";

  var r7 := YetAnotherBookshelf([1]);
  expect r7 == 0, "impl 3";

  var r8 := YetAnotherBookshelf([0, 0, 1, 0, 1]);
  expect r8 == 1, "impl 4";

  var r9 := YetAnotherBookshelf([1, 1, 1]);
  expect r9 == 0, "impl 5";

  var r10 := YetAnotherBookshelf([1, 0, 0, 1, 0, 1, 0, 0, 1, 1]);
  expect r10 == 5, "impl 6";

  var r11 := YetAnotherBookshelf([0, 1, 0, 0, 0, 1]);
  expect r11 == 3, "impl 7";

  var r12 := YetAnotherBookshelf([1, 0, 0, 1]);
  expect r12 == 2, "impl 8.1";

  var r13 := YetAnotherBookshelf([0, 1, 0]);
  expect r13 == 0, "impl 8.2";

  var r14 := YetAnotherBookshelf([0, 0, 0, 1, 0, 0, 0, 0]);
  expect r14 == 0, "impl 9";

  var r15 := YetAnotherBookshelf([1, 0, 1, 0, 1]);
  expect r15 == 2, "impl 10.1";

  var r16 := YetAnotherBookshelf([1, 1]);
  expect r16 == 0, "impl 10.2";

  var r17 := YetAnotherBookshelf([0, 1, 1, 0]);
  expect r17 == 0, "impl 10.3";

  var r18 := YetAnotherBookshelf([1, 0, 1, 0, 1, 0, 1, 0, 1, 0]);
  expect r18 == 4, "impl 11";

  var r19 := YetAnotherBookshelf([0, 1, 0, 0, 1, 0, 1]);
  expect r19 == 3, "impl 12.1";

  var r20 := YetAnotherBookshelf([1, 1, 0, 0, 1, 1]);
  expect r20 == 2, "impl 12.2";

  print "All tests passed\n";
}