// --- Specification functions ---

function Pow10(e: nat): int
  decreases e
{
  if e == 0 then 1 else 10 * Pow10(e - 1)
}

function SeqToNumber(digits: seq<int>): int
  decreases |digits|
{
  if |digits| == 0 then 0
  else digits[0] * Pow10(|digits| - 1) + SeqToNumber(digits[1..])
}

function Reorder(s: seq<int>, perm: seq<int>): seq<int>
  decreases |perm|
{
  if |perm| == 0 then []
  else (if 0 <= perm[0] < |s| then [s[perm[0]]] else [0])
       + Reorder(s, perm[1..])
}

function Range(n: nat): seq<int>
  decreases n
{
  if n == 0 then [] else Range(n - 1) + [n - 1]
}

function PrependToAll(x: int, seqs: seq<seq<int>>): seq<seq<int>>
  decreases |seqs|
{
  if |seqs| == 0 then []
  else [[x] + seqs[0]] + PrependToAll(x, seqs[1..])
}

function InsertAtAll(x: int, s: seq<int>): seq<seq<int>>
  decreases |s|
{
  [[x] + s] +
  (if |s| == 0 then []
   else PrependToAll(s[0], InsertAtAll(x, s[1..])))
}

function Distribute(x: int, perms: seq<seq<int>>): seq<seq<int>>
  decreases |perms|
{
  if |perms| == 0 then []
  else InsertAtAll(x, perms[0]) + Distribute(x, perms[1..])
}

function AllPermsOf(elems: seq<int>): seq<seq<int>>
  decreases |elems|
{
  if |elems| == 0 then [[]]
  else Distribute(elems[0], AllPermsOf(elems[1..]))
}

function AllPerms(n: nat): seq<seq<int>>
{
  AllPermsOf(Range(n))
}

function CountRedWins(perms: seq<seq<int>>, r: seq<int>, b: seq<int>): nat
  decreases |perms|
{
  if |perms| == 0 then 0
  else
    (if SeqToNumber(Reorder(r, perms[0])) > SeqToNumber(Reorder(b, perms[0]))
     then 1 else 0)
    + CountRedWins(perms[1..], r, b)
}

function CountBlueWins(perms: seq<seq<int>>, r: seq<int>, b: seq<int>): nat
  decreases |perms|
{
  if |perms| == 0 then 0
  else
    (if SeqToNumber(Reorder(r, perms[0])) < SeqToNumber(Reorder(b, perms[0]))
     then 1 else 0)
    + CountBlueWins(perms[1..], r, b)
}

// --- Top-level spec predicate (mirrors the ensures clause) ---

predicate EnsuresHolds(n: int, r: seq<int>, b: seq<int>, result: string)
  requires n >= 1
  requires |r| == n && |b| == n
{
  var perms := AllPerms(n);
  var redWins := CountRedWins(perms, r, b);
  var blueWins := CountBlueWins(perms, r, b);
  (result == "RED" <==> redWins > blueWins) &&
  (result == "BLUE" <==> redWins < blueWins) &&
  (result == "EQUAL" <==> redWins == blueWins)
}

// --- Implementation ---

method RedBlueShuffle(n: int, r: seq<int>, b: seq<int>) returns (result: string)
  requires n >= 1
  requires |r| == n && |b| == n
  requires forall i | 0 <= i < n :: 0 <= r[i] <= 9 && 0 <= b[i] <= 9
  ensures var perms := AllPerms(n);
          var redWins := CountRedWins(perms, r, b);
          var blueWins := CountBlueWins(perms, r, b);
          (result == "RED" <==> redWins > blueWins) &&
          (result == "BLUE" <==> redWins < blueWins) &&
          (result == "EQUAL" <==> redWins == blueWins)
{
  var x := 0;
  var y := 0;
  var i := 0;
  while i < n
  {
    if r[i] > b[i] {
      x := x + 1;
    } else if r[i] < b[i] {
      y := y + 1;
    }
    i := i + 1;
  }
  if x > y {
    result := "RED";
  } else if x < y {
    result := "BLUE";
  } else {
    result := "EQUAL";
  }
}

method Main()
{
  // === SPEC POSITIVE TESTS (small inputs, n <= 3) ===

  // From Test 2: n=1, r=[5], b=[3] -> RED
  expect EnsuresHolds(1, [5], [3], "RED"), "spec positive 1";
  // From Test 3: n=2, r=[0,0], b=[0,0] -> EQUAL
  expect EnsuresHolds(2, [0, 0], [0, 0], "EQUAL"), "spec positive 2";
  // From Test 4: n=3, r=[1,2,3], b=[4,5,6] -> BLUE
  expect EnsuresHolds(3, [1, 2, 3], [4, 5, 6], "BLUE"), "spec positive 3";
  // From Test 1.1: n=3, r=[7,7,7], b=[1,1,1] -> RED
  expect EnsuresHolds(3, [7, 7, 7], [1, 1, 1], "RED"), "spec positive 4";
  // From Test 1.2/7: n=3, r=[3,1,4], b=[1,5,9] -> BLUE
  expect EnsuresHolds(3, [3, 1, 4], [1, 5, 9], "BLUE"), "spec positive 5";
  // Scaled from Test 5 (n=4->2): r=[1,1], b=[2,2] -> BLUE
  expect EnsuresHolds(2, [1, 1], [2, 2], "BLUE"), "spec positive 6";
  // Scaled from Test 6 (n=5->2): r=[9,9], b=[0,0] -> RED
  expect EnsuresHolds(2, [9, 9], [0, 0], "RED"), "spec positive 7";
  // Scaled from Test 8 (n=6->2): r=[0,1], b=[1,0] -> EQUAL
  expect EnsuresHolds(2, [0, 1], [1, 0], "EQUAL"), "spec positive 8";
  // Scaled from Test 9 (n=5->2): r=[0,9], b=[0,9] -> EQUAL
  expect EnsuresHolds(2, [0, 9], [0, 9], "EQUAL"), "spec positive 9";
  // Scaled from Test 10 (n=7->3): r=[1,2,3], b=[3,2,1] -> EQUAL
  expect EnsuresHolds(3, [1, 2, 3], [3, 2, 1], "EQUAL"), "spec positive 10";

  // === SPEC NEGATIVE TESTS (wrong outputs rejected by spec) ===

  // Scaled from Negative 1 (n=5->2): identical digits, wrong="EQUAL WRONG"
  expect !EnsuresHolds(2, [0, 9], [0, 9], "EQUAL WRONG"), "spec negative 1";
  // From Negative 2: n=1, r=[5], b=[3], wrong="RED WRONG"
  expect !EnsuresHolds(1, [5], [3], "RED WRONG"), "spec negative 2";
  // From Negative 3: n=2, r=[0,0], b=[0,0], wrong="EQUAL WRONG"
  expect !EnsuresHolds(2, [0, 0], [0, 0], "EQUAL WRONG"), "spec negative 3";
  // From Negative 4: n=3, r=[1,2,3], b=[4,5,6], wrong="BLUE WRONG"
  expect !EnsuresHolds(3, [1, 2, 3], [4, 5, 6], "BLUE WRONG"), "spec negative 4";
  // Scaled from Negative 5 (n=4->2): r=[1,1], b=[2,2], wrong="BLUE WRONG"
  expect !EnsuresHolds(2, [1, 1], [2, 2], "BLUE WRONG"), "spec negative 5";
  // Scaled from Negative 6 (n=5->2): r=[9,9], b=[0,0], wrong="RED WRONG"
  expect !EnsuresHolds(2, [9, 9], [0, 0], "RED WRONG"), "spec negative 6";
  // From Negative 7: n=3, r=[3,1,4], b=[1,5,9], wrong="BLUE WRONG"
  expect !EnsuresHolds(3, [3, 1, 4], [1, 5, 9], "BLUE WRONG"), "spec negative 7";
  // Scaled from Negative 8 (n=6->2): r=[0,1], b=[1,0], wrong="EQUAL WRONG"
  expect !EnsuresHolds(2, [0, 1], [1, 0], "EQUAL WRONG"), "spec negative 8";
  // Scaled from Negative 9 (n=5->2): r=[0,9], b=[0,9], wrong="EQUAL WRONG"
  expect !EnsuresHolds(2, [0, 9], [0, 9], "EQUAL WRONG"), "spec negative 9";
  // Scaled from Negative 10 (n=7->3): r=[1,2,3], b=[3,2,1], wrong="EQUAL WRONG"
  expect !EnsuresHolds(3, [1, 2, 3], [3, 2, 1], "EQUAL WRONG"), "spec negative 10";

  // === IMPLEMENTATION TESTS (full-size inputs) ===

  var r1 := RedBlueShuffle(3, [7, 7, 7], [1, 1, 1]);
  expect r1 == "RED", "impl test 1 failed";

  var r2 := RedBlueShuffle(3, [3, 1, 4], [1, 5, 9]);
  expect r2 == "BLUE", "impl test 2 failed";

  var r3 := RedBlueShuffle(5, [0, 9, 2, 8, 1], [0, 9, 2, 8, 1]);
  expect r3 == "EQUAL", "impl test 3 failed";

  var r4 := RedBlueShuffle(1, [5], [3]);
  expect r4 == "RED", "impl test 4 failed";

  var r5 := RedBlueShuffle(2, [0, 0], [0, 0]);
  expect r5 == "EQUAL", "impl test 5 failed";

  var r6 := RedBlueShuffle(3, [1, 2, 3], [4, 5, 6]);
  expect r6 == "BLUE", "impl test 6 failed";

  var r7 := RedBlueShuffle(4, [1, 1, 1, 1], [2, 2, 2, 2]);
  expect r7 == "BLUE", "impl test 7 failed";

  var r8 := RedBlueShuffle(5, [9, 9, 9, 9, 9], [0, 0, 0, 0, 0]);
  expect r8 == "RED", "impl test 8 failed";

  var r9 := RedBlueShuffle(3, [3, 1, 4], [1, 5, 9]);
  expect r9 == "BLUE", "impl test 9 failed";

  var r10 := RedBlueShuffle(6, [0, 1, 2, 3, 4, 5], [5, 4, 3, 2, 1, 0]);
  expect r10 == "EQUAL", "impl test 10 failed";

  var r11 := RedBlueShuffle(5, [0, 9, 2, 8, 1], [0, 9, 2, 8, 1]);
  expect r11 == "EQUAL", "impl test 11 failed";

  var r12 := RedBlueShuffle(7, [1, 2, 3, 4, 5, 6, 7], [7, 6, 5, 4, 3, 2, 1]);
  expect r12 == "EQUAL", "impl test 12 failed";

  var r13 := RedBlueShuffle(3, [7, 7, 7], [1, 1, 1]);
  expect r13 == "RED", "impl test 13 failed";

  var r14 := RedBlueShuffle(4, [0, 0, 0, 0], [0, 0, 0, 0]);
  expect r14 == "EQUAL", "impl test 14 failed";

  print "All tests passed\n";
}