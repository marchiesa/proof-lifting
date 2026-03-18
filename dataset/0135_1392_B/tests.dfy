function MaxOfSeq(a: seq<int>): int
  requires |a| > 0
  decreases |a|
{
  if |a| == 1 then a[0]
  else
    var rest := MaxOfSeq(a[..|a|-1]);
    if a[|a|-1] > rest then a[|a|-1] else rest
}

function SubtractFromAll(d: int, a: seq<int>): (r: seq<int>)
  decreases |a|
  ensures |r| == |a|
{
  if |a| == 0 then []
  else SubtractFromAll(d, a[..|a|-1]) + [d - a[|a|-1]]
}

function OperationStep(a: seq<int>): (r: seq<int>)
  requires |a| > 0
  ensures |r| == |a|
{
  SubtractFromAll(MaxOfSeq(a), a)
}

function ApplyOperations(a: seq<int>, k: nat): (r: seq<int>)
  requires |a| > 0
  decreases k
  ensures |r| == |a|
{
  if k == 0 then a
  else ApplyOperations(OperationStep(a), k - 1)
}

method OmkarAndInfinityClock(a: seq<int>, k: int) returns (result: seq<int>)
  requires k >= 0
  ensures |a| == 0 ==> result == []
  ensures |a| > 0 ==> result == ApplyOperations(a, k)
{
  var n := |a|;
  if n == 0 {
    result := [];
    return;
  }
  var l := a;
  var kk := k;
  if kk > 4 {
    kk := kk - 2 * ((kk - 5) / 2);
  }
  var i := 0;
  while i < kk
  {
    var d := l[0];
    var j := 1;
    while j < n
    {
      if l[j] > d {
        d := l[j];
      }
      j := j + 1;
    }
    var newL: seq<int> := [];
    j := 0;
    while j < n
    {
      newL := newL + [d - l[j]];
      j := j + 1;
    }
    l := newL;
    i := i + 1;
  }
  result := l;
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // ensures: |a| > 0 ==> result == ApplyOperations(a, k)

  // From Test 1.1: a=[-199, 192], k=1
  expect ApplyOperations([-199, 192], 1) == [391, 0], "spec positive 1";

  // From Test 1.3: a=[69], k=2
  expect ApplyOperations([69], 2) == [0], "spec positive 2";

  // From Test 6: a=[-1], k=1
  expect ApplyOperations([-1], 1) == [0], "spec positive 3";

  // From Test 7: a=[-1000000000, -1000000000], k=1
  expect ApplyOperations([-1000000000, -1000000000], 1) == [0, 0], "spec positive 4";

  // From Test 9: a=[-1, -2, -3], k=1
  expect ApplyOperations([-1, -2, -3], 1) == [0, 1, 2], "spec positive 5";

  // From Test 11: a=[-2, -3], k=1
  expect ApplyOperations([-2, -3], 1) == [0, 1], "spec positive 6";

  // From Test 13: a=[-5, -5], k=1
  expect ApplyOperations([-5, -5], 1) == [0, 0], "spec positive 7";

  // From Test 19: a=[-5, -4], k=1
  expect ApplyOperations([-5, -4], 1) == [1, 0], "spec positive 8";

  // From Test 2.2: a=[266, 176], k=4
  expect ApplyOperations([266, 176], 4) == [90, 0], "spec positive 9";

  // From Test 2.3: a=[134, -190, 202], k=2
  expect ApplyOperations([134, -190, 202], 2) == [324, 0, 392], "spec positive 10";

  // ===== SPEC NEGATIVE TESTS =====
  // ensures: |a| > 0 ==> result == ApplyOperations(a, k)
  // Testing that ApplyOperations does NOT produce the wrong output

  // From Neg 1: a=[-199, 192], k=1, wrong=[392, 0]
  expect ApplyOperations([-199, 192], 1) != [392, 0], "spec negative 1";

  // From Neg 6: a=[-1], k=1, wrong=[1]
  expect ApplyOperations([-1], 1) != [1], "spec negative 2";

  // From Neg 7: a=[-1000000000, -1000000000], k=1, wrong=[1, 0]
  expect ApplyOperations([-1000000000, -1000000000], 1) != [1, 0], "spec negative 3";

  // From Neg 9: a=[-1, -2, -3], k=1, wrong=[1, 1, 2]
  expect ApplyOperations([-1, -2, -3], 1) != [1, 1, 2], "spec negative 4";

  // From Neg 8: a=[-1, -2, -3, -4, -5], k=1, wrong=[1, 1, 2, 3, 4]
  expect ApplyOperations([-1, -2, -3, -4, -5], 1) != [1, 1, 2, 3, 4], "spec negative 5";

  // From Neg 10: a=[-10, -9, -8, -7, -6], k=5, wrong=[5, 3, 2, 1, 0]
  expect ApplyOperations([-10, -9, -8, -7, -6], 5) != [5, 3, 2, 1, 0], "spec negative 6";

  // ===== IMPLEMENTATION TESTS =====
  var r: seq<int>;

  r := OmkarAndInfinityClock([-199, 192], 1);
  expect r == [391, 0], "impl test 1.1 failed";

  r := OmkarAndInfinityClock([5, -1, 4, 2, 0], 19);
  expect r == [0, 6, 1, 3, 5], "impl test 1.2 failed";

  r := OmkarAndInfinityClock([69], 2);
  expect r == [0], "impl test 1.3 failed";

  r := OmkarAndInfinityClock([219, 57, -58, 230, 173, 177], 4);
  expect r == [277, 115, 0, 288, 231, 235], "impl test 2.1 failed";

  r := OmkarAndInfinityClock([266, 176], 4);
  expect r == [90, 0], "impl test 2.2 failed";

  r := OmkarAndInfinityClock([134, -190, 202], 2);
  expect r == [324, 0, 392], "impl test 2.3 failed";

  r := OmkarAndInfinityClock([-1000000000, -1000000000, 1000000000, 0, 1000000000], 69);
  expect r == [2000000000, 2000000000, 0, 1000000000, 0], "impl test 2.4 failed";

  r := OmkarAndInfinityClock([289, -254, 1, -109, -167, 93, 23, -37, -31, -109, 204, 59, 296, 49, 132, 0, -28, 35, -197, -266], 809014);
  expect r == [555, 12, 267, 157, 99, 359, 289, 229, 235, 157, 470, 325, 562, 315, 398, 266, 238, 301, 69, 0], "impl test 3.1 failed";

  r := OmkarAndInfinityClock([113, 218, -292, -298, 179, 258, -257, -20, 296, 76, -145, 93, -282, -261, -159, -45, 255, -107, 171, 63], 458494);
  expect r == [411, 516, 6, 0, 477, 556, 41, 278, 594, 374, 153, 391, 16, 37, 139, 253, 553, 191, 469, 361], "impl test 3.2 failed";

  r := OmkarAndInfinityClock([69, 74, 12, 2, 177, -113, 103, 93, 38, -48, 282, 169, 205, 145], 876161);
  expect r == [213, 208, 270, 280, 105, 395, 179, 189, 244, 330, 0, 113, 77, 137], "impl test 3.3 failed";

  r := OmkarAndInfinityClock([76, 190, -227, -81, -293, 243, -122, -122, 252, 16, -88, 243, -216, -275, -267, 188, 144, -245, -117, -244, -259, 281, -273, -206, 112, -51], 731742);
  expect r == [369, 483, 66, 212, 0, 536, 171, 171, 545, 309, 205, 536, 77, 18, 26, 481, 437, 48, 176, 49, 34, 574, 20, 87, 405, 242], "impl test 3.4 failed";

  r := OmkarAndInfinityClock([42, 133, 231, 128, 19, 181, -137, 193, 136, 75, -203, 55, 37, -155, -219, 182, -178, -280, 2, 132], 327039);
  expect r == [189, 98, 0, 103, 212, 50, 368, 38, 95, 156, 434, 176, 194, 386, 450, 49, 409, 511, 229, 99], "impl test 3.5 failed";

  r := OmkarAndInfinityClock([959414461], 398708496844866113);
  expect r == [0], "impl test 4 failed";

  r := OmkarAndInfinityClock([1000000000, -1000000000, -31], 999);
  expect r == [0, 2000000000, 1000000031], "impl test 5 failed";

  r := OmkarAndInfinityClock([-1], 1);
  expect r == [0], "impl test 6 failed";

  r := OmkarAndInfinityClock([-1000000000, -1000000000], 1);
  expect r == [0, 0], "impl test 7 failed";

  r := OmkarAndInfinityClock([-1, -2, -3, -4, -5], 1);
  expect r == [0, 1, 2, 3, 4], "impl test 8 failed";

  r := OmkarAndInfinityClock([-1, -2, -3], 1);
  expect r == [0, 1, 2], "impl test 9 failed";

  r := OmkarAndInfinityClock([-10, -9, -8, -7, -6], 5);
  expect r == [4, 3, 2, 1, 0], "impl test 10 failed";

  r := OmkarAndInfinityClock([-2, -3], 1);
  expect r == [0, 1], "impl test 11 failed";

  r := OmkarAndInfinityClock([-100, -100, -100], 3);
  expect r == [0, 0, 0], "impl test 12 failed";

  r := OmkarAndInfinityClock([-5, -5], 1);
  expect r == [0, 0], "impl test 13 failed";

  r := OmkarAndInfinityClock([-999999995, -999999996, -999999997, -999999998, -999999999], 5);
  expect r == [0, 1, 2, 3, 4], "impl test 14 failed";

  r := OmkarAndInfinityClock([-1, -2], 1);
  expect r == [0, 1], "impl test 15 failed";

  r := OmkarAndInfinityClock([-9, -8, -7, -6, -5], 1);
  expect r == [4, 3, 2, 1, 0], "impl test 16 failed";

  r := OmkarAndInfinityClock([-199, -191], 1);
  expect r == [8, 0], "impl test 17 failed";

  r := OmkarAndInfinityClock([-3, -4, -5], 1);
  expect r == [0, 1, 2], "impl test 18 failed";

  r := OmkarAndInfinityClock([-5, -4], 1);
  expect r == [1, 0], "impl test 19 failed";

  r := OmkarAndInfinityClock([-1000000000, -1000000000, -1000000000], 1);
  expect r == [0, 0, 0], "impl test 20 failed";

  print "All tests passed\n";
}