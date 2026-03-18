predicate InRange(k: int, n: int)
{
  0 <= k <= n
}

predicate HasRemainder(k: int, x: int, y: int)
  requires x > 0
{
  k % x == y
}

predicate IsMaxWithRemainder(k: int, x: int, y: int, n: int)
  requires x > 0
{
  InRange(k, n)
  && HasRemainder(k, x, y)
  && (forall k' | 0 <= k' <= n :: HasRemainder(k', x, y) ==> k' <= k)
}

method RequiredRemainder(x: int, y: int, n: int) returns (k: int)
  requires x > 0
  requires 0 <= y < x
  requires y <= n
  ensures IsMaxWithRemainder(k, x, y, n)
{
  var p := n % x;
  if p == y {
    k := n;
  } else if p > y {
    k := n - p + y;
  } else {
    k := n - p - (x - y);
  }
}

method Main()
{
  var result: int;

  // ====== SPEC POSITIVE TESTS ======
  // Small inputs to keep forall quantifier enumeration fast
  expect IsMaxWithRemainder(4, 2, 0, 4), "spec positive 1";   // k=4: 4%2==0, max in 0..4
  expect IsMaxWithRemainder(5, 2, 1, 5), "spec positive 2";   // k=5: 5%2==1, max in 0..5
  expect IsMaxWithRemainder(4, 3, 1, 4), "spec positive 3";   // k=4: 4%3==1, max in 0..4
  expect IsMaxWithRemainder(5, 3, 2, 5), "spec positive 4";   // k=5: 5%3==2, max in 0..5
  expect IsMaxWithRemainder(0, 5, 0, 4), "spec positive 5";   // k=0: 0%5==0, only match in 0..4
  expect IsMaxWithRemainder(3, 3, 0, 5), "spec positive 6";   // k=3: 3%3==0, max in 0..5
  expect IsMaxWithRemainder(2, 2, 0, 3), "spec positive 7";   // k=2: 2%2==0, max in 0..3

  // ====== SPEC NEGATIVE TESTS ======
  // Wrong outputs that the spec must reject
  expect !IsMaxWithRemainder(5, 2, 0, 4), "spec negative 1";  // out of range: 5 > 4
  expect !IsMaxWithRemainder(1, 5, 0, 4), "spec negative 2";  // wrong remainder: 1%5 != 0
  expect !IsMaxWithRemainder(5, 3, 1, 5), "spec negative 3";  // wrong remainder: 5%3 != 1
  expect !IsMaxWithRemainder(3, 3, 2, 4), "spec negative 4";  // wrong remainder: 3%3 != 2
  expect !IsMaxWithRemainder(0, 3, 0, 5), "spec negative 5";  // not max: k'=3 has 3%3==0 and 3>0
  expect !IsMaxWithRemainder(2, 4, 1, 3), "spec negative 6";  // wrong remainder: 2%4 != 1
  expect !IsMaxWithRemainder(4, 3, 0, 5), "spec negative 7";  // wrong remainder: 4%3 != 0

  // ====== IMPLEMENTATION TESTS ======
  // Test 1 cases
  result := RequiredRemainder(7, 5, 12345);
  expect result == 12339, "impl test 1.1 failed";

  result := RequiredRemainder(5, 0, 4);
  expect result == 0, "impl test 1.2 failed";

  result := RequiredRemainder(10, 5, 15);
  expect result == 15, "impl test 1.3 failed";

  result := RequiredRemainder(17, 8, 54321);
  expect result == 54306, "impl test 1.4 failed";

  result := RequiredRemainder(499999993, 9, 1000000000);
  expect result == 999999995, "impl test 1.5 failed";

  result := RequiredRemainder(10, 5, 187);
  expect result == 185, "impl test 1.6 failed";

  result := RequiredRemainder(2, 0, 999999999);
  expect result == 999999998, "impl test 1.7 failed";

  // Test 2
  result := RequiredRemainder(1000000000, 0, 999999999);
  expect result == 0, "impl test 2 failed";

  // Test 3
  result := RequiredRemainder(43284, 1, 33424242);
  expect result == 33415249, "impl test 3 failed";

  // Test 4
  result := RequiredRemainder(31, 2, 104);
  expect result == 95, "impl test 4 failed";

  // Test 5
  result := RequiredRemainder(943643, 1, 23522222);
  expect result == 22647433, "impl test 5 failed";

  // Test 6
  result := RequiredRemainder(4452384, 1, 3573842);
  expect result == 1, "impl test 6 failed";

  // Test 7
  result := RequiredRemainder(33, 6, 100);
  expect result == 72, "impl test 7 failed";

  print "All tests passed\n";
}