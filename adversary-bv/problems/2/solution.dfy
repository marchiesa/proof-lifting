// Problem 2: Power of 2 check - SOLUTION

ghost function Shift1Left(k: int): bv8
  requires 0 <= k < 8
{
  (1 as bv8) << (k as bv8)
}

ghost predicate IsPowerOf2Spec(x: bv8)
{
  exists k: int {:trigger Shift1Left(k)} :: 0 <= k < 8 && x == Shift1Left(k)
}

ghost predicate IsPowerOf2Bit(x: bv8)
{
  x != 0 && x & (x - 1) == 0
}

// Forward direction: bit trick implies existential spec.
// Must enumerate all 8 possible single-bit values and provide explicit witnesses.
lemma Pow2Forward(x: bv8)
  requires IsPowerOf2Bit(x)
  ensures IsPowerOf2Spec(x)
{
  // x has exactly one bit set. The only such bv8 values are 1,2,4,8,16,32,64,128.
  // For each, we provide an explicit witness k and assert Shift1Left(k) to trigger
  // the existential quantifier.
  if x == 1      { assert Shift1Left(0) == 1;   assert 0 <= 0 < 8 && x == Shift1Left(0); }
  else if x == 2 { assert Shift1Left(1) == 2;   assert 0 <= 1 < 8 && x == Shift1Left(1); }
  else if x == 4 { assert Shift1Left(2) == 4;   assert 0 <= 2 < 8 && x == Shift1Left(2); }
  else if x == 8 { assert Shift1Left(3) == 8;   assert 0 <= 3 < 8 && x == Shift1Left(3); }
  else if x == 16 { assert Shift1Left(4) == 16; assert 0 <= 4 < 8 && x == Shift1Left(4); }
  else if x == 32 { assert Shift1Left(5) == 32; assert 0 <= 5 < 8 && x == Shift1Left(5); }
  else if x == 64 { assert Shift1Left(6) == 64; assert 0 <= 6 < 8 && x == Shift1Left(6); }
  else {
    assert x == 128;
    assert Shift1Left(7) == 128;
    assert 0 <= 7 < 8 && x == Shift1Left(7);
  }
}

// Backward direction: existential spec implies bit trick.
// Z3 can verify each case once we eliminate the existential.
lemma Pow2Backward(x: bv8)
  requires IsPowerOf2Spec(x)
  ensures IsPowerOf2Bit(x)
{
  var k: int :| 0 <= k < 8 && x == Shift1Left(k);
  // Z3's bitvector solver can verify x & (x-1) == 0 for each concrete shift amount
}

method CheckPowerOf2(x: bv8) returns (result: bool)
  ensures result <==> IsPowerOf2Spec(x)
{
  result := x != 0 && x & (x - 1) == 0;
  if result {
    Pow2Forward(x);
  } else {
    // If spec holds but bit trick doesn't, derive contradiction
    if IsPowerOf2Spec(x) {
      Pow2Backward(x);
      assert false;
    }
  }
}
