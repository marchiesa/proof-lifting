method OmkarAndInfinityClock(a: seq<int>, k: int) returns (result: seq<int>)
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
  // Test 1, case 1
  var r := OmkarAndInfinityClock([-199, 192], 1);
  expect r == [391, 0], "Test 1.1 failed";

  // Test 1, case 2
  r := OmkarAndInfinityClock([5, -1, 4, 2, 0], 19);
  expect r == [0, 6, 1, 3, 5], "Test 1.2 failed";

  // Test 1, case 3
  r := OmkarAndInfinityClock([69], 2);
  expect r == [0], "Test 1.3 failed";

  // Test 2, case 1
  r := OmkarAndInfinityClock([219, 57, -58, 230, 173, 177], 4);
  expect r == [277, 115, 0, 288, 231, 235], "Test 2.1 failed";

  // Test 2, case 2
  r := OmkarAndInfinityClock([266, 176], 4);
  expect r == [90, 0], "Test 2.2 failed";

  // Test 2, case 3
  r := OmkarAndInfinityClock([134, -190, 202], 2);
  expect r == [324, 0, 392], "Test 2.3 failed";

  // Test 2, case 4
  r := OmkarAndInfinityClock([-1000000000, -1000000000, 1000000000, 0, 1000000000], 69);
  expect r == [2000000000, 2000000000, 0, 1000000000, 0], "Test 2.4 failed";

  // Test 3, case 1
  r := OmkarAndInfinityClock([289, -254, 1, -109, -167, 93, 23, -37, -31, -109, 204, 59, 296, 49, 132, 0, -28, 35, -197, -266], 809014);
  expect r == [555, 12, 267, 157, 99, 359, 289, 229, 235, 157, 470, 325, 562, 315, 398, 266, 238, 301, 69, 0], "Test 3.1 failed";

  // Test 3, case 2
  r := OmkarAndInfinityClock([113, 218, -292, -298, 179, 258, -257, -20, 296, 76, -145, 93, -282, -261, -159, -45, 255, -107, 171, 63], 458494);
  expect r == [411, 516, 6, 0, 477, 556, 41, 278, 594, 374, 153, 391, 16, 37, 139, 253, 553, 191, 469, 361], "Test 3.2 failed";

  // Test 3, case 3
  r := OmkarAndInfinityClock([69, 74, 12, 2, 177, -113, 103, 93, 38, -48, 282, 169, 205, 145], 876161);
  expect r == [213, 208, 270, 280, 105, 395, 179, 189, 244, 330, 0, 113, 77, 137], "Test 3.3 failed";

  // Test 3, case 4
  r := OmkarAndInfinityClock([76, 190, -227, -81, -293, 243, -122, -122, 252, 16, -88, 243, -216, -275, -267, 188, 144, -245, -117, -244, -259, 281, -273, -206, 112, -51], 731742);
  expect r == [369, 483, 66, 212, 0, 536, 171, 171, 545, 309, 205, 536, 77, 18, 26, 481, 437, 48, 176, 49, 34, 574, 20, 87, 405, 242], "Test 3.4 failed";

  // Test 3, case 5
  r := OmkarAndInfinityClock([42, 133, 231, 128, 19, 181, -137, 193, 136, 75, -203, 55, 37, -155, -219, 182, -178, -280, 2, 132], 327039);
  expect r == [189, 98, 0, 103, 212, 50, 368, 38, 95, 156, 434, 176, 194, 386, 450, 49, 409, 511, 229, 99], "Test 3.5 failed";

  // Test 4
  r := OmkarAndInfinityClock([959414461], 398708496844866113);
  expect r == [0], "Test 4 failed";

  // Test 5
  r := OmkarAndInfinityClock([1000000000, -1000000000, -31], 999);
  expect r == [0, 2000000000, 1000000031], "Test 5 failed";

  // Test 6
  r := OmkarAndInfinityClock([-1], 1);
  expect r == [0], "Test 6 failed";

  // Test 7
  r := OmkarAndInfinityClock([-1000000000, -1000000000], 1);
  expect r == [0, 0], "Test 7 failed";

  // Test 8
  r := OmkarAndInfinityClock([-1, -2, -3, -4, -5], 1);
  expect r == [0, 1, 2, 3, 4], "Test 8 failed";

  // Test 9
  r := OmkarAndInfinityClock([-1, -2, -3], 1);
  expect r == [0, 1, 2], "Test 9 failed";

  // Test 10
  r := OmkarAndInfinityClock([-10, -9, -8, -7, -6], 5);
  expect r == [4, 3, 2, 1, 0], "Test 10 failed";

  // Test 11
  r := OmkarAndInfinityClock([-2, -3], 1);
  expect r == [0, 1], "Test 11 failed";

  // Test 12
  r := OmkarAndInfinityClock([-100, -100, -100], 3);
  expect r == [0, 0, 0], "Test 12 failed";

  // Test 13
  r := OmkarAndInfinityClock([-5, -5], 1);
  expect r == [0, 0], "Test 13 failed";

  // Test 14
  r := OmkarAndInfinityClock([-999999995, -999999996, -999999997, -999999998, -999999999], 5);
  expect r == [0, 1, 2, 3, 4], "Test 14 failed";

  // Test 15
  r := OmkarAndInfinityClock([-1, -2], 1);
  expect r == [0, 1], "Test 15 failed";

  // Test 16
  r := OmkarAndInfinityClock([-9, -8, -7, -6, -5], 1);
  expect r == [4, 3, 2, 1, 0], "Test 16 failed";

  // Test 17
  r := OmkarAndInfinityClock([-199, -191], 1);
  expect r == [8, 0], "Test 17 failed";

  // Test 18
  r := OmkarAndInfinityClock([-3, -4, -5], 1);
  expect r == [0, 1, 2], "Test 18 failed";

  // Test 19
  r := OmkarAndInfinityClock([-5, -4], 1);
  expect r == [1, 0], "Test 19 failed";

  // Test 20
  r := OmkarAndInfinityClock([-1000000000, -1000000000, -1000000000], 1);
  expect r == [0, 0, 0], "Test 20 failed";

  print "All tests passed\n";
}