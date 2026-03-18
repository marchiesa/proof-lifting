function Max(x: int, y: int): int {
  if x >= y then x else y
}

function MaxPurchases(c: seq<int>, a: seq<int>): int
  decreases |c|
{
  if |c| == 0 || |a| == 0 then 0
  else if a[0] >= c[0] then
    Max(1 + MaxPurchases(c[1..], a[1..]), MaxPurchases(c[1..], a))
  else
    MaxPurchases(c[1..], a)
}

method GameShopping(c: seq<int>, a: seq<int>) returns (count: int)
  ensures count == MaxPurchases(c, a)
  ensures 0 <= count <= |c|
  ensures count <= |a|
{
  count := 0;
  var i := 0;
  var j := 0;
  while i < |c| && j < |a|
  {
    if a[j] >= c[i] {
      count := count + 1;
      j := j + 1;
    }
    i := i + 1;
  }
}

method Main()
{
  // === SPEC POSITIVE TESTS (small inputs, testing MaxPurchases directly) ===
  expect MaxPurchases([], []) == 0, "spec positive 1";
  expect MaxPurchases([2, 1], [1]) == 1, "spec positive 2";
  expect MaxPurchases([3, 1], [2, 4, 2]) == 1, "spec positive 3";
  expect MaxPurchases([4], [1]) == 0, "spec positive 4";
  expect MaxPurchases([1, 1], [2, 1]) == 2, "spec positive 5";
  expect MaxPurchases([5, 5], [1]) == 0, "spec positive 6";
  expect MaxPurchases([1, 2], [5, 5]) == 2, "spec positive 7";
  expect MaxPurchases([1, 1, 1], [5]) == 1, "spec positive 8";
  expect MaxPurchases([5, 1], [5]) == 1, "spec positive 9";
  expect MaxPurchases([1, 1, 1], [2, 1]) == 2, "spec positive 10";

  // === SPEC NEGATIVE TESTS (small inputs, wrong outputs must be rejected) ===
  expect MaxPurchases([2, 1], [1]) != 2, "spec negative 1";
  expect MaxPurchases([5, 5], [1]) != 1, "spec negative 2";
  expect MaxPurchases([1, 2], [5, 5]) != 3, "spec negative 3";
  expect MaxPurchases([1, 1], [5]) != 2, "spec negative 4";
  expect MaxPurchases([5, 1], [5]) != 2, "spec negative 5";
  expect MaxPurchases([5, 5], [5]) != 2, "spec negative 6";
  expect MaxPurchases([3, 1], [2, 4, 2]) != 2, "spec negative 7";
  expect MaxPurchases([4], [1]) != 1, "spec negative 8";
  expect MaxPurchases([1, 1, 1], [2, 1]) != 3, "spec negative 9";
  expect MaxPurchases([1, 1, 1], [5]) != 2, "spec negative 10";

  // === IMPLEMENTATION TESTS (full-size inputs) ===
  var r1 := GameShopping([2, 4, 5, 2, 4], [5, 3, 4, 6]);
  expect r1 == 3, "impl test 1 failed";

  var r2 := GameShopping([20, 40, 50, 20, 40], [19, 20]);
  expect r2 == 0, "impl test 2 failed";

  var r3 := GameShopping([4, 8, 15, 16, 23, 42], [1000, 1000, 1000, 1000]);
  expect r3 == 4, "impl test 3 failed";

  var r4 := GameShopping([1, 1, 1, 1, 1], [5]);
  expect r4 == 1, "impl test 4 failed";

  var r5 := GameShopping([10, 1, 1, 1, 1], [1000]);
  expect r5 == 1, "impl test 5 failed";

  var r6 := GameShopping([100, 100, 100, 100, 100], [100]);
  expect r6 == 1, "impl test 6 failed";

  var r7 := GameShopping([2, 1], [1]);
  expect r7 == 1, "impl test 7 failed";

  var r8 := GameShopping([3, 1], [2, 4, 2]);
  expect r8 == 1, "impl test 8 failed";

  var r9 := GameShopping([4], [1, 4, 3, 3, 2]);
  expect r9 == 0, "impl test 9 failed";

  var r10 := GameShopping([4, 2, 3, 1, 1], [2, 1, 3]);
  expect r10 == 3, "impl test 10 failed";

  var r11 := GameShopping([5, 2, 5], [1, 4, 1, 4, 2]);
  expect r11 == 0, "impl test 11 failed";

  var r12 := GameShopping([9, 7, 10, 2, 1, 1, 1], [8, 9, 6]);
  expect r12 == 3, "impl test 12 failed";

  var r13 := GameShopping([2, 5, 3, 3, 2], [2, 5, 3]);
  expect r13 == 3, "impl test 13 failed";

  print "All tests passed\n";
}