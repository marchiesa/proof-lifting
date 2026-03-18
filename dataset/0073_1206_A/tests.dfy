predicate InSeq(x: int, s: seq<int>)
{
  exists i | 0 <= i < |s| :: s[i] == x
}

predicate ValidChoice(a: int, b: int, A: seq<int>, B: seq<int>)
{
  InSeq(a, A) && InSeq(b, B) && !InSeq(a + b, A) && !InSeq(a + b, B)
}

method ChooseTwoNumbers(A: seq<int>, B: seq<int>) returns (a: int, b: int)
  requires |A| > 0
  requires |B| > 0
  requires forall i | 0 <= i < |A| :: A[i] > 0
  requires forall i | 0 <= i < |B| :: B[i] > 0
  ensures ValidChoice(a, b, A, B)
{
  var sortedA := A;
  var sortedB := B;

  var i := 0;
  while i < |sortedA|
  {
    var j := i + 1;
    while j < |sortedA|
    {
      if sortedA[j] < sortedA[i]
      {
        var tmp := sortedA[i];
        sortedA := sortedA[i := sortedA[j]];
        sortedA := sortedA[j := tmp];
      }
      j := j + 1;
    }
    i := i + 1;
  }

  i := 0;
  while i < |sortedB|
  {
    var j := i + 1;
    while j < |sortedB|
    {
      if sortedB[j] < sortedB[i]
      {
        var tmp := sortedB[i];
        sortedB := sortedB[i := sortedB[j]];
        sortedB := sortedB[j := tmp];
      }
      j := j + 1;
    }
    i := i + 1;
  }

  a := sortedA[|sortedA| - 1];
  b := sortedB[|sortedB| - 1];
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // Scaled-down equivalents of the 10 positive test pairs (small seqs, values 0-5)

  // Pos 1: mirrors test 1 — single-elem A, two-elem B
  expect ValidChoice(2, 2, [2], [1, 2]), "spec positive 1";

  // Pos 2: mirrors test 2 — pick max from each, sum exceeds all
  expect ValidChoice(3, 5, [3, 2, 2], [1, 5]), "spec positive 2";

  // Pos 3: mirrors test 3 — identical-content seqs reversed
  expect ValidChoice(5, 5, [1, 3, 5], [5, 3, 1]), "spec positive 3";

  // Pos 4: mirrors test 4 — single A, longer B
  expect ValidChoice(1, 3, [1], [1, 2, 3]), "spec positive 4";

  // Pos 5: mirrors test 5 — single-elem A, single-elem B
  expect ValidChoice(4, 3, [4], [3]), "spec positive 5";

  // Pos 6: mirrors test 6 — two-elem A, two-elem B
  expect ValidChoice(4, 5, [2, 4], [5, 3]), "spec positive 6";

  // Pos 7: mirrors test 7 — three-elem A, two-elem B
  expect ValidChoice(5, 4, [3, 5, 1], [4, 2]), "spec positive 7";

  // Pos 8: mirrors test 8 — three-elem A, two-elem B
  expect ValidChoice(4, 5, [4, 1, 3], [2, 5]), "spec positive 8";

  // Pos 9: mirrors test 9 — three-elem A, two-elem B
  expect ValidChoice(5, 4, [5, 2, 1], [3, 4]), "spec positive 9";

  // Pos 10: mirrors test 10 — single-elem both, same value
  expect ValidChoice(3, 3, [3], [3]), "spec positive 10";

  // === SPEC NEGATIVE TESTS ===
  // Wrong output: a incremented by 1 (no longer in A), so ValidChoice must be false

  // Neg 1: wrong a=3 not in [2]
  expect !ValidChoice(3, 2, [2], [1, 2]), "spec negative 1";

  // Neg 2: wrong a=4 not in [3,2,2]
  expect !ValidChoice(4, 5, [3, 2, 2], [1, 5]), "spec negative 2";

  // Neg 3: wrong a=6 not in [1,3,5]
  expect !ValidChoice(6, 5, [1, 3, 5], [5, 3, 1]), "spec negative 3";

  // Neg 4: wrong a=2 not in [1]
  expect !ValidChoice(2, 3, [1], [1, 2, 3]), "spec negative 4";

  // Neg 5: wrong a=5 not in [4]
  expect !ValidChoice(5, 3, [4], [3]), "spec negative 5";

  // Neg 6: wrong a=5 not in [2,4]
  expect !ValidChoice(5, 5, [2, 4], [5, 3]), "spec negative 6";

  // Neg 7: wrong a=6 not in [3,5,1]
  expect !ValidChoice(6, 4, [3, 5, 1], [4, 2]), "spec negative 7";

  // Neg 8: wrong a=5 not in [4,1,3]
  expect !ValidChoice(5, 5, [4, 1, 3], [2, 5]), "spec negative 8";

  // Neg 9: wrong a=6 not in [5,2,1]
  expect !ValidChoice(6, 4, [5, 2, 1], [3, 4]), "spec negative 9";

  // Neg 10: wrong a=4 not in [3]
  expect !ValidChoice(4, 3, [3], [3]), "spec negative 10";

  // === IMPLEMENTATION TESTS ===
  var a1, b1 := ChooseTwoNumbers([20], [10, 20]);
  expect a1 == 20 && b1 == 20, "impl test 1 failed";

  var a2, b2 := ChooseTwoNumbers([3, 2, 2], [1, 5, 7, 7, 9]);
  expect a2 == 3 && b2 == 9, "impl test 2 failed";

  var a3, b3 := ChooseTwoNumbers([1, 3, 5, 7], [7, 5, 3, 1]);
  expect a3 == 7 && b3 == 7, "impl test 3 failed";

  var a4, b4 := ChooseTwoNumbers([1], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
  expect a4 == 1 && b4 == 10, "impl test 4 failed";

  var a5, b5 := ChooseTwoNumbers([148], [40]);
  expect a5 == 148 && b5 == 40, "impl test 5 failed";

  var a6, b6 := ChooseTwoNumbers([77, 112, 81, 91], [183, 174, 187, 111, 121, 21, 129, 28]);
  expect a6 == 112 && b6 == 187, "impl test 6 failed";

  var a7, b7 := ChooseTwoNumbers([80, 141, 15, 177, 191, 182, 115, 183, 36, 3], [129, 114, 183, 94, 169, 16, 18, 104, 49, 146, 68, 157, 33, 38, 10, 77, 112, 47, 73, 37]);
  expect a7 == 191 && b7 == 183, "impl test 7 failed";

  var a8, b8 := ChooseTwoNumbers([199, 34, 116, 194, 65, 130, 88, 7, 29, 130, 11, 142, 186, 98, 182, 87, 170, 4, 37, 17], [116, 2, 185, 117, 66, 158, 78, 120, 196, 175, 101, 117, 52, 27, 155, 153, 96, 200, 81, 38, 36, 89, 154, 8, 77, 7, 31, 163, 174, 189, 126, 155, 111, 115, 199, 2, 25, 5, 150, 5]);
  expect a8 == 199 && b8 == 200, "impl test 8 failed";

  var a9, b9 := ChooseTwoNumbers([197, 90, 23, 11, 63, 198, 24, 132, 68, 58, 195, 100, 101, 120, 96, 77, 132, 155, 62, 197, 170, 117, 189, 160, 194, 106, 172, 124, 180, 75, 124, 51, 51, 93, 186, 93, 79, 111, 161, 67, 84, 183, 150, 125, 25, 46, 106, 29, 170, 175, 4, 122], [95, 28, 20, 190, 75, 89, 193, 152, 53, 79, 100, 3, 154, 42, 67, 5, 137, 60]);
  expect a9 == 198 && b9 == 193, "impl test 9 failed";

  var a10, b10 := ChooseTwoNumbers([101], [101]);
  expect a10 == 101 && b10 == 101, "impl test 10 failed";

  var a11, b11 := ChooseTwoNumbers([1, 4], [5, 1, 1]);
  expect a11 == 4 && b11 == 5, "impl test 11 failed";

  var a12, b12 := ChooseTwoNumbers([1], [2, 1]);
  expect a12 == 1 && b12 == 2, "impl test 12 failed";

  var a13, b13 := ChooseTwoNumbers([1, 2, 3, 4, 5], [1]);
  expect a13 == 5 && b13 == 1, "impl test 13 failed";

  var a14, b14 := ChooseTwoNumbers([200], [200]);
  expect a14 == 200 && b14 == 200, "impl test 14 failed";

  var a15, b15 := ChooseTwoNumbers([1, 2, 3], [1]);
  expect a15 == 3 && b15 == 1, "impl test 15 failed";

  var a16, b16 := ChooseTwoNumbers([1], [1, 2, 1]);
  expect a16 == 1 && b16 == 2, "impl test 16 failed";

  var a17, b17 := ChooseTwoNumbers([1], [3, 2, 1]);
  expect a17 == 1 && b17 == 3, "impl test 17 failed";

  var a18, b18 := ChooseTwoNumbers([1, 2, 3, 4, 5], [7, 1, 2]);
  expect a18 == 5 && b18 == 7, "impl test 18 failed";

  var a19, b19 := ChooseTwoNumbers([1, 2, 3], [2, 3, 4, 1]);
  expect a19 == 3 && b19 == 4, "impl test 19 failed";

  var a20, b20 := ChooseTwoNumbers([1, 2, 3], [1, 1, 4, 1]);
  expect a20 == 3 && b20 == 4, "impl test 20 failed";

  print "All tests passed\n";
}