// Problem 4: Count leading zeros - SOLUTION

ghost function ClzSpec(x: bv8, pos: int): int
  requires 0 <= pos <= 8
  decreases pos
{
  if pos == 0 then 0
  else if (x >> ((pos - 1) as bv8)) & 1 == 1 then 0
  else 1 + ClzSpec(x, pos - 1)
}

ghost function Clz(x: bv8): int
{
  ClzSpec(x, 8)
}

// Helper function to provide a trigger for quantifiers over bit positions.
// Without this, Z3 cannot instantiate quantifiers involving bitvector shifts.
function GetBitAt(x: bv8, i: int): bv8
  requires 0 <= i < 8
{
  (x >> (i as bv8)) & 1
}

// Key lemma: if k consecutive bits from position (pos-k) to (pos-1) are zero,
// then ClzSpec(x, pos) == k + ClzSpec(x, pos - k).
// This lets us "fast forward" the recursive spec past all the zeros we've seen.
lemma ClzSkip(x: bv8, pos: int, k: int)
  requires 0 <= k <= pos <= 8
  requires forall i {:trigger GetBitAt(x, i)} :: pos - k <= i < pos ==> GetBitAt(x, i) == 0
  ensures ClzSpec(x, pos) == k + ClzSpec(x, pos - k)
  decreases k
{
  if k == 0 {
  } else {
    // The topmost bit in range (pos-1) is zero by the precondition
    assert GetBitAt(x, pos - 1) == 0;
    assert (x >> ((pos - 1) as bv8)) & 1 == 0;
    // So ClzSpec(x, pos) == 1 + ClzSpec(x, pos - 1)
    // Recurse to skip the remaining k-1 zero bits
    ClzSkip(x, pos - 1, k - 1);
  }
}

// Lemma: if the bit at position pos-1 is 1, the leading zero count stops.
lemma ClzHit(x: bv8, pos: int)
  requires 0 < pos <= 8
  requires (x >> ((pos - 1) as bv8)) & 1 == 1
  ensures ClzSpec(x, pos) == 0
{
}

method CountLeadingZeros(x: bv8) returns (count: int)
  ensures count == Clz(x)
{
  count := 0;
  var pos := 7;
  while pos >= 0 && (x >> (pos as bv8)) & 1 == 0
    invariant -1 <= pos <= 7
    invariant count == 7 - pos
    invariant forall i {:trigger GetBitAt(x, i)} :: pos < i <= 7 ==> GetBitAt(x, i) == 0
    decreases pos + 1
  {
    // Record that the current bit is zero (needed for the invariant)
    assert GetBitAt(x, pos) == 0;
    count := count + 1;
    pos := pos - 1;
  }
  // After the loop: either all bits are zero (pos == -1) or bit pos is 1
  if pos >= 0 {
    // Found a 1-bit at position pos. Skip over the (7 - pos) zeros above it.
    ClzSkip(x, 8, 7 - pos);
    // ClzSpec(x, 8) == (7 - pos) + ClzSpec(x, pos + 1)
    ClzHit(x, pos + 1);
    // ClzSpec(x, pos + 1) == 0, so Clz(x) == 7 - pos == count
  } else {
    // All 8 bits are zero
    ClzSkip(x, 8, 8);
    // ClzSpec(x, 8) == 8 + ClzSpec(x, 0) == 8 + 0 == 8 == count
  }
}
