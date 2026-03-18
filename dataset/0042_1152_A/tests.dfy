// --- Specification functions and predicates ---

function CountEven(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountEven(s[..|s|-1]) + (if s[|s|-1] % 2 == 0 then 1 else 0)
}

function CountOdd(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountOdd(s[..|s|-1]) + (if s[|s|-1] % 2 != 0 then 1 else 0)
}

function Min(x: int, y: int): int
{
  if x <= y then x else y
}

function EvenIndices(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else EvenIndices(s[..|s|-1]) + (if s[|s|-1] % 2 == 0 then [|s|-1] else [])
}

function OddIndices(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else OddIndices(s[..|s|-1]) + (if s[|s|-1] % 2 != 0 then [|s|-1] else [])
}

function Zip(xs: seq<int>, ys: seq<int>): seq<(int, int)>
  decreases |xs|
{
  if |xs| == 0 || |ys| == 0 then []
  else [(xs[0], ys[0])] + Zip(xs[1..], ys[1..])
}

predicate IsValidMatching(a: seq<int>, b: seq<int>, m: seq<(int, int)>)
{
  (forall k | 0 <= k < |m| ::
    0 <= m[k].0 < |a| &&
    0 <= m[k].1 < |b| &&
    (a[m[k].0] + b[m[k].1]) % 2 == 1)
  &&
  (forall i | 0 <= i < |m| :: forall j | i + 1 <= j < |m| :: m[i].0 != m[j].0)
  &&
  (forall i | 0 <= i < |m| :: forall j | i + 1 <= j < |m| :: m[i].1 != m[j].1)
}

function WitnessMatching(a: seq<int>, b: seq<int>): seq<(int, int)>
{
  Zip(EvenIndices(a), OddIndices(b)) + Zip(OddIndices(a), EvenIndices(b))
}

function MatchingUpperBound(a: seq<int>, b: seq<int>): int
{
  Min(CountEven(a), CountOdd(b)) + Min(CountOdd(a), CountEven(b))
}

// --- Implementation ---

method NekoFindsGrapes(a: seq<int>, b: seq<int>) returns (maxChests: int)
  ensures IsValidMatching(a, b, WitnessMatching(a, b))
  ensures |WitnessMatching(a, b)| == maxChests
  ensures maxChests == MatchingUpperBound(a, b)
{
  var a0 := 0;
  var a1 := 0;
  var b0 := 0;
  var b1 := 0;

  var i := 0;
  while i < |a|
  {
    if a[i] % 2 == 0 {
      a0 := a0 + 1;
    } else {
      a1 := a1 + 1;
    }
    i := i + 1;
  }

  i := 0;
  while i < |b|
  {
    if b[i] % 2 == 0 {
      b0 := b0 + 1;
    } else {
      b1 := b1 + 1;
    }
    i := i + 1;
  }

  var x := if a0 < b1 then a0 else b1;
  var y := if a1 < b0 then a1 else b0;
  maxChests := x + y;
}

// --- Tests ---

method Main()
{
  var result: int;

  // ===== SPEC POSITIVE TESTS (small inputs, values 0-5, length 1-3) =====

  // Spec positive 1: a=[1,2], b=[2,1] -> 2
  expect IsValidMatching([1,2], [2,1], WitnessMatching([1,2], [2,1])), "spec positive 1a";
  expect |WitnessMatching([1,2], [2,1])| == 2, "spec positive 1b";
  expect MatchingUpperBound([1,2], [2,1]) == 2, "spec positive 1c";

  // Spec positive 2: a=[2], b=[1] -> 1
  expect IsValidMatching([2], [1], WitnessMatching([2], [1])), "spec positive 2a";
  expect |WitnessMatching([2], [1])| == 1, "spec positive 2b";
  expect MatchingUpperBound([2], [1]) == 1, "spec positive 2c";

  // Spec positive 3: a=[2], b=[2,2] -> 0 (all same parity, no valid pairs)
  expect IsValidMatching([2], [2,2], WitnessMatching([2], [2,2])), "spec positive 3a";
  expect |WitnessMatching([2], [2,2])| == 0, "spec positive 3b";
  expect MatchingUpperBound([2], [2,2]) == 0, "spec positive 3c";

  // Spec positive 4: a=[1,2,3], b=[4,5] -> 2
  expect IsValidMatching([1,2,3], [4,5], WitnessMatching([1,2,3], [4,5])), "spec positive 4a";
  expect |WitnessMatching([1,2,3], [4,5])| == 2, "spec positive 4b";
  expect MatchingUpperBound([1,2,3], [4,5]) == 2, "spec positive 4c";

  // Spec positive 5: a=[1,3,5], b=[2] -> 1
  expect IsValidMatching([1,3,5], [2], WitnessMatching([1,3,5], [2])), "spec positive 5a";
  expect |WitnessMatching([1,3,5], [2])| == 1, "spec positive 5b";
  expect MatchingUpperBound([1,3,5], [2]) == 1, "spec positive 5c";

  // Spec positive 6: a=[1,2,3], b=[4,5,2] -> 3
  expect IsValidMatching([1,2,3], [4,5,2], WitnessMatching([1,2,3], [4,5,2])), "spec positive 6a";
  expect |WitnessMatching([1,2,3], [4,5,2])| == 3, "spec positive 6b";
  expect MatchingUpperBound([1,2,3], [4,5,2]) == 3, "spec positive 6c";

  // Spec positive 7: a=[1,3], b=[2,4] -> 2
  expect IsValidMatching([1,3], [2,4], WitnessMatching([1,3], [2,4])), "spec positive 7a";
  expect |WitnessMatching([1,3], [2,4])| == 2, "spec positive 7b";
  expect MatchingUpperBound([1,3], [2,4]) == 2, "spec positive 7c";

  // Spec positive 8: a=[1], b=[2,3] -> 1
  expect IsValidMatching([1], [2,3], WitnessMatching([1], [2,3])), "spec positive 8a";
  expect |WitnessMatching([1], [2,3])| == 1, "spec positive 8b";
  expect MatchingUpperBound([1], [2,3]) == 1, "spec positive 8c";

  // Spec positive 9: a=[1,2,3], b=[1] -> 1
  expect IsValidMatching([1,2,3], [1], WitnessMatching([1,2,3], [1])), "spec positive 9a";
  expect |WitnessMatching([1,2,3], [1])| == 1, "spec positive 9b";
  expect MatchingUpperBound([1,2,3], [1]) == 1, "spec positive 9c";

  // Spec positive 10: a=[2,1,1], b=[2,1] -> 2
  expect IsValidMatching([2,1,1], [2,1], WitnessMatching([2,1,1], [2,1])), "spec positive 10a";
  expect |WitnessMatching([2,1,1], [2,1])| == 2, "spec positive 10b";
  expect MatchingUpperBound([2,1,1], [2,1]) == 2, "spec positive 10c";

  // ===== SPEC NEGATIVE TESTS (small inputs, wrong outputs must be rejected) =====

  // Spec negative 1: a=[1,2], b=[2,1], wrong=3 (correct is 2)
  expect |WitnessMatching([1,2], [2,1])| != 3, "spec negative 1a";
  expect MatchingUpperBound([1,2], [2,1]) != 3, "spec negative 1b";

  // Spec negative 2: a=[2], b=[1], wrong=2 (correct is 1)
  expect |WitnessMatching([2], [1])| != 2, "spec negative 2a";
  expect MatchingUpperBound([2], [1]) != 2, "spec negative 2b";

  // Spec negative 3: a=[2], b=[2,2], wrong=1 (correct is 0)
  expect |WitnessMatching([2], [2,2])| != 1, "spec negative 3a";
  expect MatchingUpperBound([2], [2,2]) != 1, "spec negative 3b";

  // Spec negative 4: a=[1,2,3], b=[4,5], wrong=3 (correct is 2)
  expect |WitnessMatching([1,2,3], [4,5])| != 3, "spec negative 4a";
  expect MatchingUpperBound([1,2,3], [4,5]) != 3, "spec negative 4b";

  // Spec negative 5: a=[1,3,5], b=[2], wrong=2 (correct is 1)
  expect |WitnessMatching([1,3,5], [2])| != 2, "spec negative 5a";
  expect MatchingUpperBound([1,3,5], [2]) != 2, "spec negative 5b";

  // Spec negative 6: a=[1,2,3], b=[4,5,2], wrong=4 (correct is 3)
  expect |WitnessMatching([1,2,3], [4,5,2])| != 4, "spec negative 6a";
  expect MatchingUpperBound([1,2,3], [4,5,2]) != 4, "spec negative 6b";

  // Spec negative 7: a=[1,3], b=[2,4], wrong=3 (correct is 2)
  expect |WitnessMatching([1,3], [2,4])| != 3, "spec negative 7a";
  expect MatchingUpperBound([1,3], [2,4]) != 3, "spec negative 7b";

  // Spec negative 8: a=[1], b=[2,3], wrong=2 (correct is 1)
  expect |WitnessMatching([1], [2,3])| != 2, "spec negative 8a";
  expect MatchingUpperBound([1], [2,3]) != 2, "spec negative 8b";

  // Spec negative 9: a=[1,2,3], b=[1], wrong=2 (correct is 1)
  expect |WitnessMatching([1,2,3], [1])| != 2, "spec negative 9a";
  expect MatchingUpperBound([1,2,3], [1]) != 2, "spec negative 9b";

  // Spec negative 10: a=[2,1,1], b=[2,1], wrong=3 (correct is 2)
  expect |WitnessMatching([2,1,1], [2,1])| != 3, "spec negative 10a";
  expect MatchingUpperBound([2,1,1], [2,1]) != 3, "spec negative 10b";

  // ===== IMPLEMENTATION TESTS (full-size inputs) =====

  // Impl test 1
  result := NekoFindsGrapes([9, 14, 6, 2, 11], [8, 4, 7, 20]);
  expect result == 3, "impl test 1 failed";

  // Impl test 2
  result := NekoFindsGrapes([2, 4, 6, 8, 10], [5]);
  expect result == 1, "impl test 2 failed";

  // Impl test 3
  result := NekoFindsGrapes([10], [20, 30, 40, 50]);
  expect result == 0, "impl test 3 failed";

  // Impl test 4
  result := NekoFindsGrapes(
    [72, 105, 100, 105, 110, 103, 32, 109, 101, 115, 115, 97, 103, 101, 115, 32, 105, 110, 32, 116, 101, 115, 116, 99, 97, 115, 101],
    [83, 110, 101, 97, 107, 32, 49, 48, 48]
  );
  expect result == 9, "impl test 4 failed";

  // Impl test 5
  result := NekoFindsGrapes([107, 117, 110], [71, 114, 101, 101, 110, 71, 114, 97, 112, 101]);
  expect result == 3, "impl test 5 failed";

  // Impl test 6
  result := NekoFindsGrapes([116, 111, 117, 114, 105, 115, 116], [112, 101, 116, 114]);
  expect result == 4, "impl test 6 failed";

  // Impl test 7
  result := NekoFindsGrapes(
    [522312461, 931001459, 598654597, 488228616, 544064902, 21923894, 329635457, 980089248, 988262691, 654502493],
    [967529230, 543358150, 835120075, 128123793, 809901567, 613170206, 152157661, 479980560, 859252956, 318029856]
  );
  expect result == 10, "impl test 7 failed";

  // Impl test 8
  result := NekoFindsGrapes([1], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
  expect result == 1, "impl test 8 failed";

  // Impl test 9
  result := NekoFindsGrapes([1, 2, 3, 4, 5], [1]);
  expect result == 1, "impl test 9 failed";

  // Impl test 10
  result := NekoFindsGrapes([2, 2, 1, 1, 1, 1, 1], [2, 2, 2, 1]);
  expect result == 4, "impl test 10 failed";

  // Impl test 11
  result := NekoFindsGrapes([1, 1, 1, 2], [2]);
  expect result == 1, "impl test 11 failed";

  // Impl test 12
  result := NekoFindsGrapes([3, 5, 7, 8], [2]);
  expect result == 1, "impl test 12 failed";

  // Impl test 13
  result := NekoFindsGrapes([1, 2, 2, 2, 2], [1, 1]);
  expect result == 2, "impl test 13 failed";

  // Impl test 14
  result := NekoFindsGrapes([3, 2, 1, 4], [2, 3]);
  expect result == 2, "impl test 14 failed";

  // Impl test 15
  result := NekoFindsGrapes([1, 2], [1, 1, 2, 2]);
  expect result == 2, "impl test 15 failed";

  // Impl test 16
  result := NekoFindsGrapes([2, 2, 3, 3], [2]);
  expect result == 1, "impl test 16 failed";

  // Impl test 17
  result := NekoFindsGrapes([2, 2, 2, 3, 3], [3]);
  expect result == 1, "impl test 17 failed";

  // Impl test 18
  result := NekoFindsGrapes([1, 1, 2, 2], [2]);
  expect result == 1, "impl test 18 failed";

  // Impl test 19
  result := NekoFindsGrapes([3], [3, 4, 4, 4, 4]);
  expect result == 1, "impl test 19 failed";

  // Impl test 20
  result := NekoFindsGrapes([2, 4, 6, 1, 3, 5], [8, 10, 7, 9]);
  expect result == 4, "impl test 20 failed";

  print "All tests passed\n";
}