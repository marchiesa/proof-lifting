// --- Specification: modeling the problem structure ---

predicate IsBinary(s: seq<int>) {
  forall i | 0 <= i < |s| :: s[i] == 0 || s[i] == 1
}

function Pow2(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

function IntToBinary(k: int, n: int): (result: seq<int>)
  requires k >= 0
  requires n >= 0
  decreases n
  ensures |result| == n
{
  if n == 0 then []
  else IntToBinary(k / 2, n - 1) + [k % 2]
}

function BitwiseSum(a: seq<int>, b: seq<int>): (result: seq<int>)
  requires |a| == |b|
  decreases |a|
  ensures |result| == |a|
{
  if |a| == 0 then []
  else BitwiseSum(a[..|a|-1], b[..|b|-1]) + [a[|a|-1] + b[|b|-1]]
}

function Deduplicate(c: seq<int>): seq<int>
  decreases |c|
{
  if |c| == 0 then []
  else if |c| == 1 then c
  else if c[0] == c[1] then Deduplicate(c[1..])
  else [c[0]] + Deduplicate(c[1..])
}

function ComputeD(a: seq<int>, b: seq<int>): seq<int>
  requires |a| == |b|
{
  Deduplicate(BitwiseSum(a, b))
}

function StripLeadingZeros(d: seq<int>): seq<int>
  decreases |d|
{
  if |d| == 0 then []
  else if d[0] == 0 then StripLeadingZeros(d[1..])
  else d
}

predicate LexGeq(s1: seq<int>, s2: seq<int>)
  requires |s1| == |s2|
  decreases |s1|
{
  if |s1| == 0 then true
  else if s1[0] != s2[0] then s1[0] > s2[0]
  else LexGeq(s1[1..], s2[1..])
}

predicate IntGeq(d1: seq<int>, d2: seq<int>) {
  var s1 := StripLeadingZeros(d1);
  var s2 := StripLeadingZeros(d2);
  if |s1| != |s2| then |s1| > |s2|
  else LexGeq(s1, s2)
}

predicate IsOptimalD(a: seq<int>, n: int, b: seq<int>)
  requires n >= 1
  requires |a| == n
  requires |b| == n
{
  forall k | 0 <= k < Pow2(n) ::
    IntGeq(ComputeD(a, b), ComputeD(IntToBinary(k, n), b))
}

// --- Method with specification ---

method PuzzleFromTheFuture(n: int, b: seq<int>) returns (a: seq<int>)
  requires n >= 1
  requires |b| == n
  requires IsBinary(b)
  ensures |a| == n
  ensures IsBinary(a)
  ensures IsOptimalD(a, n, b)
{
  a := [1];
  var i := 1;
  while i < n
  {
    if a[i - 1] + b[i - 1] == 1 + b[i] {
      a := a + [0];
    } else {
      a := a + [1];
    }
    i := i + 1;
  }
}

method Main()
{
  // ====== SPEC POSITIVE TESTS ======
  // Testing IsOptimalD(correct_a, n, b) with small inputs (n <= 3)

  // From Test 1.1 / 2.1 / 8.1 / 11.1: n=1, b=[0], a=[1]
  expect IsOptimalD([1], 1, [0]), "spec positive 1";

  // From Test 2.2 / 5.1 / 11.2: n=1, b=[1], a=[1]
  expect IsOptimalD([1], 1, [1]), "spec positive 2";

  // From Test 2.3 / 11.3: n=2, b=[0,1], a=[1,1]
  expect IsOptimalD([1, 1], 2, [0, 1]), "spec positive 3";

  // From Test 6.1: n=2, b=[0,0], a=[1,0]
  expect IsOptimalD([1, 0], 2, [0, 0]), "spec positive 4";

  // From Test 6.2: n=2, b=[1,1], a=[1,0]
  expect IsOptimalD([1, 0], 2, [1, 1]), "spec positive 5";

  // From Test 8.2: n=2, b=[1,0], a=[1,1]
  expect IsOptimalD([1, 1], 2, [1, 0]), "spec positive 6";

  // From Test 1.2: n=3, b=[0,1,1], a=[1,1,0]
  expect IsOptimalD([1, 1, 0], 3, [0, 1, 1]), "spec positive 7";

  // From Test 1.3 / 11.4: n=3, b=[1,1,0], a=[1,0,0]
  expect IsOptimalD([1, 0, 0], 3, [1, 1, 0]), "spec positive 8";

  // From Test 8.3: n=3, b=[1,0,1], a=[1,1,1]
  expect IsOptimalD([1, 1, 1], 3, [1, 0, 1]), "spec positive 9";

  // From Test 4.1: n=3, b=[0,1,0], a=[1,1,1]
  expect IsOptimalD([1, 1, 1], 3, [0, 1, 0]), "spec positive 10";

  // ====== SPEC NEGATIVE TESTS ======
  // For non-binary wrong outputs: test !IsBinary
  // For binary wrong outputs: test !IsOptimalD

  // From Neg 1: n=1, b=[0], wrong a=[2] — not binary
  expect !IsBinary([2]), "spec negative 1";

  // From Neg 2: n=1, b=[0], wrong a=[2] — not binary
  expect !IsBinary([2]), "spec negative 2";

  // From Neg 3: n=5, b=[1,0,1,0,1], wrong a=[1,1,1,1,2] — not binary
  expect !IsBinary([1, 1, 1, 1, 2]), "spec negative 3";

  // From Neg 4: n=3, b=[0,1,0], wrong a=[1,1,2] — not binary
  expect !IsBinary([1, 1, 2]), "spec negative 4";

  // From Neg 5: n=1, b=[1], wrong a=[2] — not binary
  expect !IsBinary([2]), "spec negative 5";

  // From Neg 6: n=2, b=[0,0], wrong a=[1,1] — binary but not optimal
  expect !IsOptimalD([1, 1], 2, [0, 0]), "spec negative 6";

  // From Neg 7: n=4, b=[0,1,1,0], wrong a=[1,1,0,1] — binary but not optimal
  expect !IsOptimalD([1, 1, 0, 1], 4, [0, 1, 1, 0]), "spec negative 7";

  // From Neg 8: n=1, b=[0], wrong a=[2] — not binary
  expect !IsBinary([2]), "spec negative 8";

  // From Neg 9: n=5, b=[0,0,0,0,0], wrong a=[1,0,1,0,2] — not binary
  expect !IsBinary([1, 0, 1, 0, 2]), "spec negative 9";

  // From Neg 10: n=6, b=[1,0,1,0,1,0], wrong a=[1,1,1,1,1,2] — not binary
  expect !IsBinary([1, 1, 1, 1, 1, 2]), "spec negative 10";

  // ====== IMPLEMENTATION TESTS ======
  var r: seq<int>;

  // n=1, b=[0]
  r := PuzzleFromTheFuture(1, [0]);
  expect r == [1], "impl test 1 failed";

  // n=1, b=[1]
  r := PuzzleFromTheFuture(1, [1]);
  expect r == [1], "impl test 2 failed";

  // n=2, b=[0,1]
  r := PuzzleFromTheFuture(2, [0, 1]);
  expect r == [1, 1], "impl test 3 failed";

  // n=2, b=[0,0]
  r := PuzzleFromTheFuture(2, [0, 0]);
  expect r == [1, 0], "impl test 4 failed";

  // n=2, b=[1,1]
  r := PuzzleFromTheFuture(2, [1, 1]);
  expect r == [1, 0], "impl test 5 failed";

  // n=2, b=[1,0]
  r := PuzzleFromTheFuture(2, [1, 0]);
  expect r == [1, 1], "impl test 6 failed";

  // n=3, b=[0,1,1]
  r := PuzzleFromTheFuture(3, [0, 1, 1]);
  expect r == [1, 1, 0], "impl test 7 failed";

  // n=3, b=[1,1,0]
  r := PuzzleFromTheFuture(3, [1, 1, 0]);
  expect r == [1, 0, 0], "impl test 8 failed";

  // n=3, b=[0,1,0]
  r := PuzzleFromTheFuture(3, [0, 1, 0]);
  expect r == [1, 1, 1], "impl test 9 failed";

  // n=3, b=[1,0,1]
  r := PuzzleFromTheFuture(3, [1, 0, 1]);
  expect r == [1, 1, 1], "impl test 10 failed";

  // n=4, b=[1,1,0,0]
  r := PuzzleFromTheFuture(4, [1, 1, 0, 0]);
  expect r == [1, 0, 0, 1], "impl test 11 failed";

  // n=4, b=[0,1,1,0]
  r := PuzzleFromTheFuture(4, [0, 1, 1, 0]);
  expect r == [1, 1, 0, 0], "impl test 12 failed";

  // n=5, b=[1,0,1,0,1]
  r := PuzzleFromTheFuture(5, [1, 0, 1, 0, 1]);
  expect r == [1, 1, 1, 1, 1], "impl test 13 failed";

  // n=5, b=[0,0,0,0,0]
  r := PuzzleFromTheFuture(5, [0, 0, 0, 0, 0]);
  expect r == [1, 0, 1, 0, 1], "impl test 14 failed";

  // n=5, b=[1,1,1,1,1]
  r := PuzzleFromTheFuture(5, [1, 1, 1, 1, 1]);
  expect r == [1, 0, 1, 0, 1], "impl test 15 failed";

  // n=6, b=[1,1,1,0,0,0]
  r := PuzzleFromTheFuture(6, [1, 1, 1, 0, 0, 0]);
  expect r == [1, 0, 1, 1, 0, 1], "impl test 16 failed";

  // n=6, b=[0,0,1,0,1,1]
  r := PuzzleFromTheFuture(6, [0, 0, 1, 0, 1, 1]);
  expect r == [1, 0, 1, 1, 1, 0], "impl test 17 failed";

  // n=6, b=[1,0,1,0,1,0]
  r := PuzzleFromTheFuture(6, [1, 0, 1, 0, 1, 0]);
  expect r == [1, 1, 1, 1, 1, 1], "impl test 18 failed";

  print "All tests passed\n";
}