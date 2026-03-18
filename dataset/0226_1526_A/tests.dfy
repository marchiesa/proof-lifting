predicate AllDistinct(a: seq<int>)
{
  forall i, j | 0 <= i < |a| && 0 <= j < |a| && i != j :: a[i] != a[j]
}

predicate IsPermutation(a: seq<int>, b: seq<int>)
{
  multiset(a) == multiset(b)
}

function CircularPrev(i: int, len: int): int
  requires len > 0
  requires 0 <= i < len
{
  if i == 0 then len - 1 else i - 1
}

function CircularNext(i: int, len: int): int
  requires len > 0
  requires 0 <= i < len
{
  if i == len - 1 then 0 else i + 1
}

predicate NoElementIsMeanOfNeighbors(b: seq<int>)
  requires |b| > 0
{
  forall i | 0 <= i < |b| ::
    2 * b[i] != b[CircularPrev(i, |b|)] + b[CircularNext(i, |b|)]
}

method MeanInequality(a: seq<int>, n: int) returns (b: seq<int>)
  requires n >= 1
  requires |a| == 2 * n
  requires AllDistinct(a)
  ensures |b| == |a|
  ensures IsPermutation(a, b)
  ensures NoElementIsMeanOfNeighbors(b)
{
  var arr := new int[|a|];
  var k := 0;
  while k < |a| {
    arr[k] := a[k];
    k := k + 1;
  }

  // Selection sort
  var i := 0;
  while i < arr.Length {
    var minIdx := i;
    var j := i + 1;
    while j < arr.Length {
      if arr[j] < arr[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    var tmp := arr[i];
    arr[i] := arr[minIdx];
    arr[minIdx] := tmp;
    i := i + 1;
  }

  // Swap first and last
  if arr.Length > 0 {
    var tmp := arr[0];
    arr[0] := arr[arr.Length - 1];
    arr[arr.Length - 1] := tmp;
  }

  // Swap adjacent pairs
  i := 1;
  while i < n - 1 {
    var tmp := arr[i * 2];
    arr[i * 2] := arr[i * 2 + 1];
    arr[i * 2 + 1] := tmp;
    i := i + 1;
  }

  // Convert array back to seq
  b := [];
  k := 0;
  while k < arr.Length {
    b := b + [arr[k]];
    k := k + 1;
  }
}

method Main()
{
  // ========== SPEC POSITIVE TESTS ==========
  // Test all three ensures predicates on small (input, correct_output) pairs

  // Spec positive 1 (from test 3: [1,2] -> [2,1])
  expect |[2, 1]| == |[1, 2]|, "spec positive 1a";
  expect IsPermutation([1, 2], [2, 1]), "spec positive 1b";
  expect NoElementIsMeanOfNeighbors([2, 1]), "spec positive 1c";

  // Spec positive 2 (from test 2, scaled: [420,69]->[420,69] => [4,1]->[4,1])
  expect |[4, 1]| == |[4, 1]|, "spec positive 2a";
  expect IsPermutation([4, 1], [4, 1]), "spec positive 2b";
  expect NoElementIsMeanOfNeighbors([4, 1]), "spec positive 2c";

  // Spec positive 3 (from test 4: [1,2,3,4] -> [4,2,3,1])
  expect |[4, 2, 3, 1]| == |[1, 2, 3, 4]|, "spec positive 3a";
  expect IsPermutation([1, 2, 3, 4], [4, 2, 3, 1]), "spec positive 3b";
  expect NoElementIsMeanOfNeighbors([4, 2, 3, 1]), "spec positive 3c";

  // Spec positive 4 (from test 8.1, scaled: [5,8]->[8,5] => [2,5]->[5,2])
  expect |[5, 2]| == |[2, 5]|, "spec positive 4a";
  expect IsPermutation([2, 5], [5, 2]), "spec positive 4b";
  expect NoElementIsMeanOfNeighbors([5, 2]), "spec positive 4c";

  // Spec positive 5 (from test 10.1, scaled: [1,50]->[50,1] => [1,5]->[5,1])
  expect |[5, 1]| == |[1, 5]|, "spec positive 5a";
  expect IsPermutation([1, 5], [5, 1]), "spec positive 5b";
  expect NoElementIsMeanOfNeighbors([5, 1]), "spec positive 5c";

  // Spec positive 6 (from test 10.2, scaled: [25,30]->[30,25] => [2,3]->[3,2])
  expect |[3, 2]| == |[2, 3]|, "spec positive 6a";
  expect IsPermutation([2, 3], [3, 2]), "spec positive 6b";
  expect NoElementIsMeanOfNeighbors([3, 2]), "spec positive 6c";

  // Spec positive 7 (from test 10.3, scaled: [3,7]->[7,3] => [3,5]->[5,3])
  expect |[5, 3]| == |[3, 5]|, "spec positive 7a";
  expect IsPermutation([3, 5], [5, 3]), "spec positive 7b";
  expect NoElementIsMeanOfNeighbors([5, 3]), "spec positive 7c";

  // ========== SPEC NEGATIVE TESTS ==========
  // Test that IsPermutation REJECTS wrong outputs (first element was incremented)

  // Spec negative 1 (from neg 3: [1,2] -> wrong [3,1])
  expect !IsPermutation([1, 2], [3, 1]), "spec negative 1";

  // Spec negative 2 (from neg 2, scaled: [420,69]->[421,69] => [4,1]->[5,1])
  expect !IsPermutation([4, 1], [5, 1]), "spec negative 2";

  // Spec negative 3 (from neg 4: [1,2,3,4] -> wrong [5,2,3,1])
  expect !IsPermutation([1, 2, 3, 4], [5, 2, 3, 1]), "spec negative 3";

  // Spec negative 4 (from neg 6, scaled: [10,20]->[21,10] => [2,3]->[4,2])
  expect !IsPermutation([2, 3], [4, 2]), "spec negative 4";

  // Spec negative 5 (from neg 7, scaled: [1,3,...]->[16,...] => [1,3]->[4,1])
  expect !IsPermutation([1, 3], [4, 1]), "spec negative 5";

  // Spec negative 6 (from neg 8, scaled: [5,8]->[9,5] => [2,4]->[5,2])
  expect !IsPermutation([2, 4], [5, 2]), "spec negative 6";

  // ========== IMPLEMENTATION TESTS ==========

  // Impl test 1.1
  var r1a := MeanInequality([1, 2, 3, 4, 5, 6], 3);
  expect r1a == [6, 2, 4, 3, 5, 1], "impl test 1.1 failed";

  // Impl test 1.2
  var r1b := MeanInequality([123, 456, 789, 10], 2);
  expect r1b == [789, 123, 456, 10], "impl test 1.2 failed";

  // Impl test 1.3
  var r1c := MeanInequality([6, 9], 1);
  expect r1c == [9, 6], "impl test 1.3 failed";

  // Impl test 2
  var r2 := MeanInequality([420, 69], 1);
  expect r2 == [420, 69], "impl test 2 failed";

  // Impl test 3
  var r3 := MeanInequality([1, 2], 1);
  expect r3 == [2, 1], "impl test 3 failed";

  // Impl test 4
  var r4 := MeanInequality([1, 2, 3, 4], 2);
  expect r4 == [4, 2, 3, 1], "impl test 4 failed";

  // Impl test 5
  var r5 := MeanInequality([1, 2, 3, 4, 5, 6], 3);
  expect r5 == [6, 2, 4, 3, 5, 1], "impl test 5 failed";

  // Impl test 6
  var r6 := MeanInequality([10, 20], 1);
  expect r6 == [20, 10], "impl test 6 failed";

  // Impl test 7
  var r7 := MeanInequality([1, 3, 5, 7, 9, 11, 13, 15], 4);
  expect r7 == [15, 3, 7, 5, 11, 9, 13, 1], "impl test 7 failed";

  // Impl test 8.1
  var r8a := MeanInequality([5, 8], 1);
  expect r8a == [8, 5], "impl test 8.1 failed";

  // Impl test 8.2
  var r8b := MeanInequality([10, 20, 30, 40], 2);
  expect r8b == [40, 20, 30, 10], "impl test 8.2 failed";

  // Impl test 9
  var r9 := MeanInequality([2, 4, 6, 8, 10, 12, 14, 16, 18, 20], 5);
  expect r9 == [20, 4, 8, 6, 12, 10, 16, 14, 18, 2], "impl test 9 failed";

  // Impl test 10.1
  var r10a := MeanInequality([1, 50], 1);
  expect r10a == [50, 1], "impl test 10.1 failed";

  // Impl test 10.2
  var r10b := MeanInequality([25, 30], 1);
  expect r10b == [30, 25], "impl test 10.2 failed";

  // Impl test 10.3
  var r10c := MeanInequality([3, 7], 1);
  expect r10c == [7, 3], "impl test 10.3 failed";

  // Impl test 11
  var r11 := MeanInequality([10, 20, 30, 40, 50, 49], 3);
  expect r11 == [50, 20, 40, 30, 49, 10], "impl test 11 failed";

  // Impl test 12
  var r12 := MeanInequality([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50], 25);
  expect r12 == [50, 2, 4, 3, 6, 5, 8, 7, 10, 9, 12, 11, 14, 13, 16, 15, 18, 17, 20, 19, 22, 21, 24, 23, 26, 25, 28, 27, 30, 29, 32, 31, 34, 33, 36, 35, 38, 37, 40, 39, 42, 41, 44, 43, 46, 45, 48, 47, 49, 1], "impl test 12 failed";

  print "All tests passed\n";
}