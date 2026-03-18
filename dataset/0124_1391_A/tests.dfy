// --- Spec: Bitwise OR for non-negative integers ---
function BitwiseOr(a: int, b: int): int
  requires a >= 0 && b >= 0
  ensures BitwiseOr(a, b) >= 0
  decreases a + b
{
  if a == 0 && b == 0 then 0
  else
    (if a % 2 == 1 || b % 2 == 1 then 1 else 0) + 2 * BitwiseOr(a / 2, b / 2)
}

// --- Spec: OR of all elements in a non-empty sequence ---
function OrOfSeq(s: seq<int>): int
  requires |s| > 0
  requires forall i | 0 <= i < |s| :: s[i] >= 0
  ensures OrOfSeq(s) >= 0
  decreases |s|
{
  if |s| == 1 then s[0]
  else BitwiseOr(OrOfSeq(s[..|s|-1]), s[|s|-1])
}

// --- Spec: p is a permutation of [1..n] ---
predicate IsPermutation(p: seq<int>, n: int)
{
  n >= 0 &&
  |p| == n &&
  (forall i | 0 <= i < n :: 1 <= p[i] <= n) &&
  (forall i, j | 0 <= i < j < n :: p[i] != p[j])
}

// --- Spec: every subarray's bitwise OR >= the subarray's length ---
predicate IsGood(p: seq<int>)
{
  (forall k | 0 <= k < |p| :: p[k] >= 0) &&
  (forall i, j | 0 <= i <= j < |p| :: OrOfSeq(p[i..j+1]) >= j - i + 1)
}

method GoodPermutation(n: int) returns (p: seq<int>)
  requires n >= 1
  ensures IsPermutation(p, n)
  ensures IsGood(p)
{
  p := [];
  var i := 1;
  while i <= n
  {
    p := p + [i];
    i := i + 1;
  }
}

method ExpectedPermutation(n: int) returns (e: seq<int>)
{
  e := [];
  var i := 1;
  while i <= n
  {
    e := e + [i];
    i := i + 1;
  }
}

method ToString(n: int) returns (s: string)
{
  if n == 0 { return "0"; }
  s := "";
  var val := n;
  if val < 0 { val := -val; }
  while val > 0
  {
    s := [(val % 10) as char + '0'] + s;
    val := val / 10;
  }
  if n < 0 { s := "-" + s; }
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Testing ensures predicates IsPermutation and IsGood with correct small outputs

  // From positive test 1 (n=1): correct output [1]
  expect IsPermutation([1], 1), "spec pos 1a";
  expect IsGood([1]), "spec pos 1b";

  // From positive test 2 (n=2): correct output [1,2]
  expect IsPermutation([1, 2], 2), "spec pos 2a";
  expect IsGood([1, 2]), "spec pos 2b";

  // From positive test 1 (n=3): correct output [1,2,3]
  expect IsPermutation([1, 2, 3], 3), "spec pos 3a";
  expect IsGood([1, 2, 3]), "spec pos 3b";

  // ===== SPEC NEGATIVE TESTS =====
  // Testing ensures predicates reject wrong outputs
  // All negative mutations change the first element from 1 to 2

  // From neg 1: n=1, wrong=[2] (first element changed 1->2)
  expect !IsPermutation([2], 1), "spec neg 1";

  // From neg 2: n=1, wrong=[2] (conjunction test)
  expect !(IsPermutation([2], 1) && IsGood([2])), "spec neg 2";

  // From neg 3: n=77 first elem=2, scaled to n=2 wrong=[2,2]
  expect !IsPermutation([2, 2], 2), "spec neg 3";

  // From neg 3: n=77 first elem=2, scaled to n=3 wrong=[2,2,3]
  expect !IsPermutation([2, 2, 3], 3), "spec neg 4";

  // From neg 4: n=57 first elem=2, scaled to n=3 wrong=[2,2,3] (conjunction)
  expect !(IsPermutation([2, 2, 3], 3) && IsGood([2, 2, 3])), "spec neg 5";

  // ===== IMPLEMENTATION TESTS =====
  var p: seq<int>;
  var e: seq<int>;

  // Test 1: n=1, n=3, n=7
  p := GoodPermutation(1);
  e := ExpectedPermutation(1);
  expect p == e, "impl test 1a failed";

  p := GoodPermutation(3);
  e := ExpectedPermutation(3);
  expect p == e, "impl test 1b failed";

  p := GoodPermutation(7);
  e := ExpectedPermutation(7);
  expect p == e, "impl test 1c failed";

  // Test 2: n=1..100
  var i := 1;
  while i <= 100
  {
    p := GoodPermutation(i);
    e := ExpectedPermutation(i);
    var s := ToString(i);
    expect p == e, "impl test 2 n=" + s + " failed";
    i := i + 1;
  }

  // Test 3: n=77
  p := GoodPermutation(77);
  e := ExpectedPermutation(77);
  expect p == e, "impl test 3 failed";

  // Test 4: n=57
  p := GoodPermutation(57);
  e := ExpectedPermutation(57);
  expect p == e, "impl test 4 failed";

  print "All tests passed\n";
}