predicate IsBinaryString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

function Pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

function TargetChar(plan: nat, i: nat): char
{
  if (plan / Pow2(i)) % 2 == 0 then '0' else '1'
}

function CharCost(orig: char, target: char, c0: int, c1: int, h: int): int
{
  var buyCost := if target == '0' then c0 else c1;
  var flipCost := if orig != target then h else 0;
  buyCost + flipCost
}

function PlanCost(s: string, plan: nat, c0: int, c1: int, h: int): int
  decreases |s|
{
  if |s| == 0 then 0
  else PlanCost(s[..|s|-1], plan, c0, c1, h) +
       CharCost(s[|s|-1], TargetChar(plan, |s|-1), c0, c1, h)
}

predicate IsMinCost(s: string, c0: int, c1: int, h: int, cost: int)
{
  (exists plan: nat | plan < Pow2(|s|) :: PlanCost(s, plan, c0, c1, h) == cost)
  &&
  (forall plan: nat | plan < Pow2(|s|) :: PlanCost(s, plan, c0, c1, h) >= cost)
}

method BuyTheString(s: string, c0: int, c1: int, h: int) returns (cost: int)
  requires IsBinaryString(s)
  ensures IsMinCost(s, c0, c1, h, cost)
{
  var ec1 := if c1 < h + c0 then c1 else h + c0;
  var ec0 := if c0 < h + ec1 then c0 else h + ec1;
  var count0 := 0;
  var count1 := 0;
  var i := 0;
  while i < |s|
  {
    if s[i] == '0' {
      count0 := count0 + 1;
    } else {
      count1 := count1 + 1;
    }
    i := i + 1;
  }
  cost := count0 * ec0 + count1 * ec1;
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Testing IsMinCost with correct outputs (small inputs, length 1-3)

  // From Test 4: "0", c0=1, c1=1, h=1 -> 1
  expect IsMinCost("0", 1, 1, 1, 1), "spec positive 1";
  // From Test 5: "1", c0=1, c1=1, h=1 -> 1
  expect IsMinCost("1", 1, 1, 1, 1), "spec positive 2";
  // From Test 8: "01", c0=1, c1=1, h=1 -> 2
  expect IsMinCost("01", 1, 1, 1, 2), "spec positive 3";
  // From Test 1: "100", c0=1, c1=1, h=1 -> 3
  expect IsMinCost("100", 1, 1, 1, 3), "spec positive 4";
  // From Test 8: "010", c0=1, c1=1, h=1 -> 3
  expect IsMinCost("010", 1, 1, 1, 3), "spec positive 5";
  // From Test 2: "0", c0=10, c1=1, h=1000 -> 10
  expect IsMinCost("0", 10, 1, 1000, 10), "spec positive 6";
  // From Test 2: "1", c0=1, c1=10, h=2 -> 3
  expect IsMinCost("1", 1, 10, 2, 3), "spec positive 7";
  // From Test 3: "101", c0=3, c1=7, h=2 -> 13
  expect IsMinCost("101", 3, 7, 2, 13), "spec positive 8";
  // From Test 3: "11", c0=5, c1=5, h=1 -> 10
  expect IsMinCost("11", 5, 5, 1, 10), "spec positive 9";
  // From Test 6: "010", c0=10, c1=10, h=1 -> 30
  expect IsMinCost("010", 10, 10, 1, 30), "spec positive 10";
  // From Test 2: "11", c0=1000, c1=500, h=1000 -> 1000
  expect IsMinCost("11", 1000, 500, 1000, 1000), "spec positive 11";
  // From Test 2: "101", c0=500, c1=500, h=1 -> 1500
  expect IsMinCost("101", 500, 500, 1, 1500), "spec positive 12";
  // From Test 12: "0", c0=2, c1=3, h=4 -> 2
  expect IsMinCost("0", 2, 3, 4, 2), "spec positive 13";
  // From Test 12: "1", c0=3, c1=2, h=4 -> 2
  expect IsMinCost("1", 3, 2, 4, 2), "spec positive 14";

  // ===== SPEC NEGATIVE TESTS =====
  // Testing IsMinCost with WRONG outputs (small inputs, length 1-3)

  // From Neg 4: "0", c0=1, c1=1, h=1, wrong=2
  expect !IsMinCost("0", 1, 1, 1, 2), "spec negative 1";
  // From Neg 5: "1", c0=1, c1=1, h=1, wrong=2
  expect !IsMinCost("1", 1, 1, 1, 2), "spec negative 2";
  // From Neg 1: "100", c0=1, c1=1, h=1, wrong=4
  expect !IsMinCost("100", 1, 1, 1, 4), "spec negative 3";
  // From Neg 3: "101", c0=3, c1=7, h=2, wrong=14
  expect !IsMinCost("101", 3, 7, 2, 14), "spec negative 4";
  // From Neg 6: "010", c0=10, c1=10, h=1, wrong=31
  expect !IsMinCost("010", 10, 10, 1, 31), "spec negative 5";
  // Scaled from Neg 2: "10", c0=3, c1=1, h=1, wrong=4 (correct=3)
  expect !IsMinCost("10", 3, 1, 1, 4), "spec negative 6";
  // Scaled from Neg 7: "01", c0=50, c1=50, h=50, wrong=101 (correct=100)
  expect !IsMinCost("01", 50, 50, 50, 101), "spec negative 7";
  // Scaled from Neg 9: "11", c0=3, c1=8, h=2, wrong=11 (correct=10)
  expect !IsMinCost("11", 3, 8, 2, 11), "spec negative 8";
  // Scaled from Neg 10: "11", c0=1, c1=50, h=3, wrong=9 (correct=8)
  expect !IsMinCost("11", 1, 50, 3, 9), "spec negative 9";
  // From Neg 8: "0", c0=1, c1=1, h=1, wrong=2 (same input as neg 1, from different test pair)
  expect !IsMinCost("0", 1, 1, 1, 2), "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====
  var r: int;

  // Test 1
  r := BuyTheString("100", 1, 1, 1);
  expect r == 3, "impl test 1.1";
  r := BuyTheString("01010", 10, 100, 1);
  expect r == 52, "impl test 1.2";
  r := BuyTheString("11111", 10, 1, 1);
  expect r == 5, "impl test 1.3";
  r := BuyTheString("11111", 1, 10, 1);
  expect r == 10, "impl test 1.4";
  r := BuyTheString("101110110101", 2, 1, 10);
  expect r == 16, "impl test 1.5";
  r := BuyTheString("00", 100, 1, 10);
  expect r == 22, "impl test 1.6";

  // Test 2
  r := BuyTheString("1000000110", 3, 1, 1);
  expect r == 17, "impl test 2.1";
  r := BuyTheString("0", 10, 1, 1000);
  expect r == 10, "impl test 2.2";
  r := BuyTheString("1", 1, 10, 2);
  expect r == 3, "impl test 2.3";
  r := BuyTheString("1001", 4, 4, 1);
  expect r == 16, "impl test 2.4";
  r := BuyTheString("1", 1, 1, 1);
  expect r == 1, "impl test 2.5";
  r := BuyTheString("11", 1000, 500, 1000);
  expect r == 1000, "impl test 2.6";
  r := BuyTheString("101", 500, 500, 1);
  expect r == 1500, "impl test 2.7";

  // Test 3
  r := BuyTheString("101", 3, 7, 2);
  expect r == 13, "impl test 3.1";
  r := BuyTheString("0000", 10, 1, 5);
  expect r == 24, "impl test 3.2";
  r := BuyTheString("11", 5, 5, 1);
  expect r == 10, "impl test 3.3";

  // Test 4
  r := BuyTheString("0", 1, 1, 1);
  expect r == 1, "impl test 4.1";

  // Test 5
  r := BuyTheString("1", 1, 1, 1);
  expect r == 1, "impl test 5.1";

  // Test 6
  r := BuyTheString("010", 10, 10, 1);
  expect r == 30, "impl test 6.1";
  r := BuyTheString("110100", 2, 3, 4);
  expect r == 15, "impl test 6.2";

  // Test 7
  r := BuyTheString("0101010101", 50, 50, 50);
  expect r == 500, "impl test 7.1";

  // Test 8
  r := BuyTheString("0", 1, 1, 1);
  expect r == 1, "impl test 8.1";
  r := BuyTheString("1", 1, 1, 1);
  expect r == 1, "impl test 8.2";
  r := BuyTheString("01", 1, 1, 1);
  expect r == 2, "impl test 8.3";
  r := BuyTheString("010", 1, 1, 1);
  expect r == 3, "impl test 8.4";

  // Test 9
  r := BuyTheString("1100101", 3, 8, 2);
  expect r == 29, "impl test 9.1";

  // Test 10
  r := BuyTheString("1111", 1, 50, 3);
  expect r == 16, "impl test 10.1";
  r := BuyTheString("0000", 50, 1, 3);
  expect r == 16, "impl test 10.2";

  // Test 11
  r := BuyTheString("00001111", 5, 5, 10);
  expect r == 40, "impl test 11.1";

  // Test 12
  r := BuyTheString("0", 1, 1, 1);
  expect r == 1, "impl test 12.1";
  r := BuyTheString("1", 1, 1, 1);
  expect r == 1, "impl test 12.2";
  r := BuyTheString("0", 2, 3, 4);
  expect r == 2, "impl test 12.3";
  r := BuyTheString("1", 3, 2, 4);
  expect r == 2, "impl test 12.4";
  r := BuyTheString("01", 5, 5, 5);
  expect r == 10, "impl test 12.5";
  r := BuyTheString("11", 1, 50, 1);
  expect r == 4, "impl test 12.6";
  r := BuyTheString("000", 50, 1, 50);
  expect r == 150, "impl test 12.7";
  r := BuyTheString("111", 1, 50, 1);
  expect r == 6, "impl test 12.8";
  r := BuyTheString("0101", 10, 10, 1);
  expect r == 40, "impl test 12.9";
  r := BuyTheString("10101", 7, 3, 2);
  expect r == 19, "impl test 12.10";

  print "All tests passed\n";
}