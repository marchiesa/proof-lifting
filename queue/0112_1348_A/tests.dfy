// --- Specification functions ---

function Pow2Func(k: int): int
  requires k >= 0
  decreases k
{
  if k == 0 then 1 else 2 * Pow2Func(k - 1)
}

function BitIsSet(mask: int, pos: int): bool
  requires mask >= 0 && pos >= 0
{
  (mask / Pow2Func(pos)) % 2 == 1
}

function CountSetBits(mask: int, bits: int): int
  requires mask >= 0 && bits >= 0
  decreases bits
{
  if bits == 0 then 0
  else CountSetBits(mask, bits - 1) + (if BitIsSet(mask, bits - 1) then 1 else 0)
}

predicate IsValidSplit(mask: int, n: int)
  requires mask >= 0 && n >= 0
{
  mask < Pow2Func(n) && CountSetBits(mask, n) == n / 2
}

function PileWeight(mask: int, n: int): int
  requires mask >= 0 && n >= 0
  decreases n
{
  if n == 0 then 0
  else PileWeight(mask, n - 1) + (if BitIsSet(mask, n - 1) then Pow2Func(n) else 0)
}

function AbsDiff(a: int, b: int): int
{
  if a >= b then a - b else b - a
}

function SplitDifference(mask: int, n: int): int
  requires mask >= 0 && n >= 0
{
  var pileA := PileWeight(mask, n);
  var total := Pow2Func(n + 1) - 2;
  AbsDiff(pileA, total - pileA)
}

// Combined ensures predicate for spec testing
predicate PhoenixSpec(n: int, diff: int)
  requires n >= 2 && n % 2 == 0
{
  diff >= 0 &&
  (exists mask | 0 <= mask < Pow2Func(n) :: IsValidSplit(mask, n) && diff == SplitDifference(mask, n)) &&
  (forall mask | 0 <= mask < Pow2Func(n) :: IsValidSplit(mask, n) ==> diff <= SplitDifference(mask, n))
}

// --- Implementation ---

method Pow2(exp: int) returns (result: int)
  requires exp >= 0
  ensures result == Pow2Func(exp)
{
  result := 1;
  var i := 0;
  while i < exp
  {
    result := result * 2;
    i := i + 1;
  }
}

method PhoenixAndBalance(n: int) returns (diff: int)
  requires n >= 2 && n % 2 == 0
  ensures diff >= 0
  ensures exists mask | 0 <= mask < Pow2Func(n) ::
            IsValidSplit(mask, n) && diff == SplitDifference(mask, n)
  ensures forall mask | 0 <= mask < Pow2Func(n) ::
            IsValidSplit(mask, n) ==> diff <= SplitDifference(mask, n)
{
  var totalVal := Pow2(n + 1);
  totalVal := totalVal - 2;
  var halfPow := Pow2(n / 2);
  var nPow := Pow2(n);
  var left := halfPow - 2 + nPow;
  var right := totalVal - left;
  diff := left - right;
}

// --- Tests ---

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Small n values where bounded quantifier enumeration is feasible

  // From Test 1/3: n=2, correct diff=2
  expect PhoenixSpec(2, 2), "spec positive 1";

  // From Test 1: n=4, correct diff=6
  expect PhoenixSpec(4, 6), "spec positive 2";

  // From Test 2: n=6, correct diff=14
  expect PhoenixSpec(6, 14), "spec positive 3";

  // From Test 2: n=8, correct diff=30
  expect PhoenixSpec(8, 30), "spec positive 4";

  // From Test 2/5: n=10, correct diff=62
  expect PhoenixSpec(10, 62), "spec positive 5";

  // ===== SPEC NEGATIVE TESTS =====
  // Small n values; scaled down from large inputs where needed

  // Negative 1: n=2, wrong=3 (correct=2)
  expect !PhoenixSpec(2, 3), "spec negative 1";

  // Negative 2: n=2, wrong=3 (first entry wrong; correct=2)
  expect !PhoenixSpec(2, 3), "spec negative 2";

  // Negative 3: n=2, wrong=3 (correct=2)
  expect !PhoenixSpec(2, 3), "spec negative 3";

  // Negative 4: n=30 too large; scaled to n=6, wrong=15 (off-by-one, like 65535 vs 65534)
  expect !PhoenixSpec(6, 15), "spec negative 4";

  // Negative 5: n=4, wrong=7 (correct=6)
  expect !PhoenixSpec(4, 7), "spec negative 5";

  // ===== IMPLEMENTATION TESTS =====

  // Test 1: T=2
  var inputs1 := [2, 4];
  var expected1 := [2, 6];
  var i := 0;
  while i < |inputs1|
  {
    var result := PhoenixAndBalance(inputs1[i]);
    expect result == expected1[i], "impl test 1 failed";
    i := i + 1;
  }

  // Test 2: T=100
  var inputs2 := [2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,30,30,30,20,30,30,18,14,16,30,24,30,30,10,20,30,10,2,18,30,30,12,24,30,24,18,28,30,16,30,30,30,30,22,26,30,30,30,10,14,6,18,30,16,30,30,4,30,20,30,30,30,30,30,24,30,30,12,30,30,30,26,30,14,30,30,30,14,30,30,30,30,30,30,30,12,30,14,14,2,30,30,30,30,30];
  var expected2 := [2,6,14,30,62,126,254,510,1022,2046,4094,8190,16382,32766,65534,65534,65534,65534,2046,65534,65534,1022,254,510,65534,8190,65534,65534,62,2046,65534,62,2,1022,65534,65534,126,8190,65534,8190,1022,32766,65534,510,65534,65534,65534,65534,4094,16382,65534,65534,65534,62,254,14,1022,65534,510,65534,65534,6,65534,2046,65534,65534,65534,65534,65534,8190,65534,65534,126,65534,65534,65534,16382,65534,254,65534,65534,65534,254,65534,65534,65534,65534,65534,65534,65534,126,65534,254,254,2,65534,65534,65534,65534,65534];
  i := 0;
  while i < |inputs2|
  {
    var result := PhoenixAndBalance(inputs2[i]);
    expect result == expected2[i], "impl test 2 failed";
    i := i + 1;
  }

  // Test 3: T=1
  var result3 := PhoenixAndBalance(2);
  expect result3 == 2, "impl test 3 failed";

  // Test 4: T=100
  var inputs4 := [30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30];
  var expected4 := [65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534,65534];
  i := 0;
  while i < |inputs4|
  {
    var result := PhoenixAndBalance(inputs4[i]);
    expect result == expected4[i], "impl test 4 failed";
    i := i + 1;
  }

  // Test 5: T=100
  var inputs5 := [4,10,12,20,14,12,14,18,14,14,20,20,14,18,24,22,24,14,26,24,24,18,16,2,28,12,10,6,26,2,10,16,16,18,2,20,30,6,12,30,14,6,8,26,12,10,12,20,14,10,12,24,4,8,12,8,20,8,10,30,12,10,12,24,20,2,4,16,22,14,8,18,14,2,4,4,26,6,30,24,28,20,8,16,8,4,18,30,6,22,22,24,30,4,24,10,14,24,6,30];
  var expected5 := [6,62,126,2046,254,126,254,1022,254,254,2046,2046,254,1022,8190,4094,8190,254,16382,8190,8190,1022,510,2,32766,126,62,14,16382,2,62,510,510,1022,2,2046,65534,14,126,65534,254,14,30,16382,126,62,126,2046,254,62,126,8190,6,30,126,30,2046,30,62,65534,126,62,126,8190,2046,2,6,510,4094,254,30,1022,254,2,6,6,16382,14,65534,8190,32766,2046,30,510,30,6,1022,65534,14,4094,4094,8190,65534,6,8190,62,254,8190,14,65534];
  i := 0;
  while i < |inputs5|
  {
    var result := PhoenixAndBalance(inputs5[i]);
    expect result == expected5[i], "impl test 5 failed";
    i := i + 1;
  }

  print "All tests passed\n";
}