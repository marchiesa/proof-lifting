function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

predicate NoLoss(price: int, a: seq<int>)
  requires |a| > 0
{
  price * |a| >= Sum(a)
}

predicate IsMinimalEqualPrice(price: int, a: seq<int>)
  requires |a| > 0
{
  NoLoss(price, a) && !NoLoss(price - 1, a)
}

method EqualizePrice(a: seq<int>) returns (price: int)
  requires |a| > 0
  ensures IsMinimalEqualPrice(price, a)
{
  var s := 0;
  var n := |a|;
  var i := 0;
  while i < n
  {
    s := s + a[i];
    i := i + 1;
  }
  price := (s + n - 1) / n;
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Testing IsMinimalEqualPrice(correct_output, input) == true
  // Scaled to small inputs (length 1-3, values 0-5)

  // From Test 1 case 2: [1,2,2] -> 2 (already small)
  expect IsMinimalEqualPrice(2, [1, 2, 2]), "spec positive 1";

  // From Test 1 case 3: [1,1,1,1]->1 scaled to [1,1,1] -> 1
  expect IsMinimalEqualPrice(1, [1, 1, 1]), "spec positive 2";

  // From Test 2: [777,1]->389 scaled to [5,1] -> 3
  expect IsMinimalEqualPrice(3, [5, 1]), "spec positive 3";

  // From Test 3: [2441139]->2441139 scaled to [5] -> 5
  expect IsMinimalEqualPrice(5, [5]), "spec positive 4";

  // From Test 4 case 2: [1,2,3] -> 2 (already small)
  expect IsMinimalEqualPrice(2, [1, 2, 3]), "spec positive 5";

  // From Test 5: [777,778]->778 scaled to [4,5] -> 5
  expect IsMinimalEqualPrice(5, [4, 5]), "spec positive 6";

  // ===== SPEC NEGATIVE TESTS =====
  // Testing IsMinimalEqualPrice(wrong_output, input) == false
  // Scaled to small inputs with wrong = correct + 1

  // From Neg 1: [1,2,3,4,5] wrong=4 scaled to [1,2] correct=2, wrong=3
  expect !IsMinimalEqualPrice(3, [1, 2]), "spec negative 1";

  // From Neg 2: [777,1] wrong=390 scaled to [5,1] correct=3, wrong=4
  expect !IsMinimalEqualPrice(4, [5, 1]), "spec negative 2";

  // From Neg 3: [2441139] wrong=2441140 scaled to [5] correct=5, wrong=6
  expect !IsMinimalEqualPrice(6, [5]), "spec negative 3";

  // From Neg 4: [1,2,3,4,5] wrong=4 scaled to [1,2,3] correct=2, wrong=3
  expect !IsMinimalEqualPrice(3, [1, 2, 3]), "spec negative 4";

  // From Neg 5: [777,778] wrong=779 scaled to [4,5] correct=5, wrong=6
  expect !IsMinimalEqualPrice(6, [4, 5]), "spec negative 5";

  // ===== IMPLEMENTATION TESTS =====
  // Full-size test pairs

  // Test 1
  var r1 := EqualizePrice([1, 2, 3, 4, 5]);
  expect r1 == 3, "impl test 1.1 failed";
  var r2 := EqualizePrice([1, 2, 2]);
  expect r2 == 2, "impl test 1.2 failed";
  var r3 := EqualizePrice([1, 1, 1, 1]);
  expect r3 == 1, "impl test 1.3 failed";

  // Test 2
  var r4 := EqualizePrice([777, 1]);
  expect r4 == 389, "impl test 2 failed";

  // Test 3
  var r5 := EqualizePrice([2441139]);
  expect r5 == 2441139, "impl test 3 failed";

  // Test 4
  var r6 := EqualizePrice([1, 2, 3, 4, 5]);
  expect r6 == 3, "impl test 4.1 failed";
  var r7 := EqualizePrice([1, 2, 3]);
  expect r7 == 2, "impl test 4.2 failed";
  var r8 := EqualizePrice([777, 778]);
  expect r8 == 778, "impl test 4.3 failed";

  // Test 5
  var r9 := EqualizePrice([777, 778]);
  expect r9 == 778, "impl test 5 failed";

  print "All tests passed\n";
}