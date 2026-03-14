// Problem 4: Count leading zeros

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

// Lemma: ClzSpec unfolds correctly for the loop pattern.
// The loop scans from pos=7 down. After scanning positions 7..pos+1 and
// finding all zeros, ClzSpec(x, 8) == (7-pos) + ClzSpec(x, pos+1).
// But actually we need to relate the loop's count to ClzSpec directly.

// Key insight: when we've scanned positions 7 down to pos+1 and found all zeros,
// the count so far is (7 - pos), and ClzSpec(x, 8) equals count + ClzSpec(x, pos+1).
// But actually ClzSpec naturally unrolls from the top, so let's think about it differently.

// ClzSpec(x, 8) unrolls as:
//   if bit 7 is 1, then 0
//   else 1 + ClzSpec(x, 7)
//     if bit 6 is 1, then 0
//     else 1 + ClzSpec(x, 6)
//       ...

// The loop goes pos = 7, 6, 5, ... and counts zeros from top.
// After the loop processes down to pos (and pos has a 1-bit or pos < 0),
// count = 8 - (pos + 1) = 7 - pos.
// The loop invariant should be:
//   count + ClzSpec(x, pos + 1) == ClzSpec(x, 8)
// Wait, let's think more carefully.
// When pos = 7 (start, before first iteration): count = 0
//   We need 0 + ClzSpec(x, 8) == ClzSpec(x, 8) -- trivially true.
// If bit 7 is 0, we enter the loop: count becomes 1, pos becomes 6.
//   We need 1 + ClzSpec(x, 7) == ClzSpec(x, 8)
//   ClzSpec(x, 8) = 1 + ClzSpec(x, 7) because bit 7 is 0. Good.
// If bit 6 is also 0: count becomes 2, pos becomes 5.
//   We need 2 + ClzSpec(x, 6) == ClzSpec(x, 8)
// Etc.

// But the loop condition is: pos >= 0 && bit at pos is 0.
// When the loop exits because bit at pos is 1:
//   count + ClzSpec(x, pos+1) == Clz(x)
//   ClzSpec(x, pos+1): bit at pos is 1, so ClzSpec(x, pos+1) = 0.
//   So count == Clz(x).
// When the loop exits because pos < 0 (pos == -1):
//   count + ClzSpec(x, 0) == Clz(x)
//   ClzSpec(x, 0) = 0, so count == Clz(x).

// Lemma to help with the unrolling
lemma {:fuel ClzSpec, 2} ClzUnroll(x: bv8, pos: int)
  requires 0 <= pos <= 7
  requires (x >> (pos as bv8)) & 1 == 0
  ensures ClzSpec(x, pos + 1) == 1 + ClzSpec(x, pos)
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
    invariant count + ClzSpec(x, pos + 1) == Clz(x)
    decreases pos + 1
  {
    ClzUnroll(x, pos);
    count := count + 1;
    pos := pos - 1;
  }
  // At exit: either pos < 0 (so ClzSpec(x, 0) = 0, count = 8)
  // or bit at pos is 1 (so ClzSpec(x, pos+1) = 0)
}
