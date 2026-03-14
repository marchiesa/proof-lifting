// Problem 3: Bit reversal - SOLUTION

function GetBit(x: bv8, i: int): bv8
  requires 0 <= i < 8
{
  (x >> (i as bv8)) & 1
}

// Key insight: define a "partial reverse" ghost function that builds the
// reversed value bit by bit, matching the loop's computation exactly.
// Because bv8 has only 8 bits, we can enumerate all 9 cases (0..8 bits processed).
// Z3 can then verify each step and the final postcondition via bitvector reasoning.
ghost function PartialRev(x: bv8, j: int): bv8
  requires 0 <= j <= 8
{
  if j == 0 then 0
  else if j == 1 then GetBit(x, 0)
  else if j == 2 then (GetBit(x, 0) << 1) | GetBit(x, 1)
  else if j == 3 then (GetBit(x, 0) << 2) | (GetBit(x, 1) << 1) | GetBit(x, 2)
  else if j == 4 then (GetBit(x, 0) << 3) | (GetBit(x, 1) << 2) | (GetBit(x, 2) << 1) | GetBit(x, 3)
  else if j == 5 then (GetBit(x, 0) << 4) | (GetBit(x, 1) << 3) | (GetBit(x, 2) << 2) | (GetBit(x, 3) << 1) | GetBit(x, 4)
  else if j == 6 then (GetBit(x, 0) << 5) | (GetBit(x, 1) << 4) | (GetBit(x, 2) << 3) | (GetBit(x, 3) << 2) | (GetBit(x, 4) << 1) | GetBit(x, 5)
  else if j == 7 then (GetBit(x, 0) << 6) | (GetBit(x, 1) << 5) | (GetBit(x, 2) << 4) | (GetBit(x, 3) << 3) | (GetBit(x, 4) << 2) | (GetBit(x, 5) << 1) | GetBit(x, 6)
  else (GetBit(x, 0) << 7) | (GetBit(x, 1) << 6) | (GetBit(x, 2) << 5) | (GetBit(x, 3) << 4) | (GetBit(x, 4) << 3) | (GetBit(x, 5) << 2) | (GetBit(x, 6) << 1) | GetBit(x, 7)
}

// Lemma: each loop iteration advances the partial reverse by one step.
// The loop body does r := (r << 1) | (tmp & 1) where tmp = x >> j,
// so tmp & 1 == GetBit(x, j). Shifting r left by 1 and OR-ing matches
// the PartialRev definition.
lemma PartialRevStep(x: bv8, j: int, r: bv8)
  requires 0 <= j < 8
  requires r == PartialRev(x, j)
  ensures (r << 1) | GetBit(x, j) == PartialRev(x, j + 1)
{
}

method BitReverse(x: bv8) returns (r: bv8)
  ensures forall i: int :: 0 <= i < 8 ==> GetBit(r, i) == GetBit(x, 7 - i)
{
  r := 0;
  var tmp := x;
  var j: int := 0;
  while j < 8
    invariant 0 <= j <= 8
    invariant tmp == x >> (j as bv8)
    invariant r == PartialRev(x, j)
    decreases 8 - j
  {
    PartialRevStep(x, j, r);
    r := (r << 1) | (tmp & 1);
    assert tmp & 1 == GetBit(x, j);
    tmp := tmp >> 1;
    j := j + 1;
  }
  // After loop: r == PartialRev(x, 8)
  // Z3 can verify that PartialRev(x, 8) satisfies the bit-reversal property
}
