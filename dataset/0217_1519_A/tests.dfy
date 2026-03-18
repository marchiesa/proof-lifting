function Abs(x: int): int {
  if x >= 0 then x else -x
}

function Min(a: int, b: int): int {
  if a <= b then a else b
}

predicate ValidPacket(ri: int, bi: int, d: int) {
  ri >= 1 && bi >= 1 && Abs(ri - bi) <= d
}

predicate CanDistributeInN(r: int, b: int, d: int, n: nat)
  decreases n
{
  if n == 0 then
    r == 0 && b == 0
  else if r < n || b < n then
    false
  else if n == 1 then
    ValidPacket(r, b, d)
  else
    exists ri | 1 <= ri <= r - (n - 1) ::
      exists bi | 1 <= bi <= b - (n - 1) ::
        ValidPacket(ri, bi, d) &&
        CanDistributeInN(r - ri, b - bi, d, n - 1)
}

predicate CanDistribute(r: int, b: int, d: int) {
  exists n | 1 <= n <= Min(r, b) :: CanDistributeInN(r, b, d, n)
}

method RedAndBlueBeans(r: int, b: int, d: int) returns (result: bool)
  requires r >= 1 && b >= 1 && d >= 0
  ensures result == CanDistribute(r, b, d)
{
  var rr := r;
  var bb := b;
  if rr > bb {
    var tmp := rr;
    rr := bb;
    bb := tmp;
  }
  result := rr * (d + 1) >= bb;
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Using small inputs to keep bounded quantifier enumeration fast.
  // Top-level predicate: CanDistribute(r, b, d)

  // From Test 1 case 1: (1,1,0) → true
  expect CanDistribute(1, 1, 0) == true, "spec positive 1";

  // From Test 1 case 2: (2,7,3) scaled to (2,3,3) → true
  expect CanDistribute(2, 3, 3) == true, "spec positive 2";

  // From Test 1 case 3: (6,1,4) scaled to (3,1,1) → false
  expect CanDistribute(3, 1, 1) == false, "spec positive 3";

  // From Test 1 case 4: (5,4,0) scaled to (3,2,0) → false
  expect CanDistribute(3, 2, 0) == false, "spec positive 4";

  // From Test 5: (1,1,1) → true
  expect CanDistribute(1, 1, 1) == true, "spec positive 5";

  // From Test 6: (2,1,1) → true
  expect CanDistribute(2, 1, 1) == true, "spec positive 6";

  // From Test 7: (150,150,150) scaled to (3,3,3) → true
  expect CanDistribute(3, 3, 3) == true, "spec positive 7";

  // From Test 2: (1,1000000000,1000000000) scaled to (1,3,3) → true
  expect CanDistribute(1, 3, 3) == true, "spec positive 8";

  // From Test 3/4: (1000000000,1,1000000000) scaled to (3,1,3) → true
  expect CanDistribute(3, 1, 3) == true, "spec positive 9";

  // ===== SPEC NEGATIVE TESTS =====
  // Verify that wrong outputs are rejected by the spec predicate.

  // From Neg 5: (1,1,1) correct=true, wrong=false
  expect CanDistribute(1, 1, 1) != false, "spec negative 1";

  // From Neg 6: (2,1,1) correct=true, wrong=false
  expect CanDistribute(2, 1, 1) != false, "spec negative 2";

  // From Neg 7: (150,150,150) scaled to (3,3,3), correct=true, wrong=false
  expect CanDistribute(3, 3, 3) != false, "spec negative 3";

  // From Neg 1: (5,4,0) scaled to (3,2,0), correct=false, wrong=true
  expect CanDistribute(3, 2, 0) != true, "spec negative 4";

  // From Neg 2: (1,1000000000,1000000000) scaled to (1,3,3), correct=true, wrong=false
  expect CanDistribute(1, 3, 3) != false, "spec negative 5";

  // From Neg 3: (1000000000,1,1000000000) scaled to (3,1,3), correct=true, wrong=false
  expect CanDistribute(3, 1, 3) != false, "spec negative 6";

  // From Neg 4: analog scaled to (3,1,1), correct=false, wrong=true
  expect CanDistribute(3, 1, 1) != true, "spec negative 7";

  // ===== IMPLEMENTATION TESTS =====
  var result: bool;

  // Test 1
  result := RedAndBlueBeans(1, 1, 0);
  expect result == true, "impl test 1.1: (1,1,0) expected YES";

  result := RedAndBlueBeans(2, 7, 3);
  expect result == true, "impl test 1.2: (2,7,3) expected YES";

  result := RedAndBlueBeans(6, 1, 4);
  expect result == false, "impl test 1.3: (6,1,4) expected NO";

  result := RedAndBlueBeans(5, 4, 0);
  expect result == false, "impl test 1.4: (5,4,0) expected NO";

  // Test 2
  result := RedAndBlueBeans(1, 1000000000, 1000000000);
  expect result == true, "impl test 2: (1,1000000000,1000000000) expected YES";

  // Test 3/4
  result := RedAndBlueBeans(1000000000, 1, 1000000000);
  expect result == true, "impl test 3/4: (1000000000,1,1000000000) expected YES";

  // Test 5
  result := RedAndBlueBeans(1, 1, 1);
  expect result == true, "impl test 5: (1,1,1) expected YES";

  // Test 6
  result := RedAndBlueBeans(2, 1, 1);
  expect result == true, "impl test 6: (2,1,1) expected YES";

  // Test 7
  result := RedAndBlueBeans(150, 150, 150);
  expect result == true, "impl test 7: (150,150,150) expected YES";

  print "All tests passed\n";
}