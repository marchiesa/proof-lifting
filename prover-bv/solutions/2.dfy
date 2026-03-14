// Problem 2: Power of 2 check

ghost function Shift1Left(k: int): bv8
  requires 0 <= k < 8
{
  (1 as bv8) << (k as bv8)
}

ghost predicate IsPowerOf2Spec(x: bv8)
{
  exists k: int {:trigger Shift1Left(k)} :: 0 <= k < 8 && x == Shift1Left(k)
}

// Lemma: if x is a power of 2, then x & (x-1) == 0.
// We enumerate all 8 possible power-of-2 values.
lemma PowerOf2ImpliesBitTrick(x: bv8)
  requires IsPowerOf2Spec(x)
  ensures x != 0
  ensures x & (x - 1) == 0
{
  var k: int :| 0 <= k < 8 && x == Shift1Left(k);
  // Enumerate all cases
  assert k == 0 || k == 1 || k == 2 || k == 3 || k == 4 || k == 5 || k == 6 || k == 7;
}

// Lemma: if x != 0 && x & (x-1) == 0, then x is a power of 2.
// We prove by enumerating which single bit must be set.
lemma BitTrickImpliesPowerOf2(x: bv8)
  requires x != 0 && x & (x - 1) == 0
  ensures IsPowerOf2Spec(x)
{
  // Enumerate all bv8 values that satisfy x & (x-1) == 0 and x != 0.
  // These are exactly the powers of 2: 1, 2, 4, 8, 16, 32, 64, 128.
  if x == 1 { assert x == Shift1Left(0); }
  else if x == 2 { assert x == Shift1Left(1); }
  else if x == 4 { assert x == Shift1Left(2); }
  else if x == 8 { assert x == Shift1Left(3); }
  else if x == 16 { assert x == Shift1Left(4); }
  else if x == 32 { assert x == Shift1Left(5); }
  else if x == 64 { assert x == Shift1Left(6); }
  else if x == 128 { assert x == Shift1Left(7); }
  else {
    // Any other non-zero value with x & (x-1) == 0 is impossible.
    // Z3 can verify this for bv8 by exhaustion.
    assert false;
  }
}

method CheckPowerOf2(x: bv8) returns (result: bool)
  ensures result <==> IsPowerOf2Spec(x)
{
  result := x != 0 && x & (x - 1) == 0;
  if result {
    BitTrickImpliesPowerOf2(x);
  } else if x != 0 {
    // x != 0 but x & (x-1) != 0, need to show it's not a power of 2
    if IsPowerOf2Spec(x) {
      PowerOf2ImpliesBitTrick(x);
      assert false; // contradiction
    }
  }
}
