// Problem 4: Count leading zeros
//
// Count the number of leading (most significant) zero bits in a bv8.
// The implementation scans from the MSB downward. The spec uses a
// recursive ghost function that counts from the top bit.
//
// Z3 struggles because:
// - The loop scans bits from position 7 down to 0
// - The recursive spec ClzSpec processes bits from top to bottom
// - Relating the loop's partial scan to the recursive spec requires
//   a lemma that "skips" over known-zero bits
// - Quantifiers over bit positions combined with bitvector shift
//   operations create trigger-matching difficulties

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

// TASK: Add loop invariants and any necessary lemmas to make this verify.
method CountLeadingZeros(x: bv8) returns (count: int)
  ensures count == Clz(x)
{
  count := 0;
  var pos := 7;
  while pos >= 0 && (x >> (pos as bv8)) & 1 == 0
    decreases pos + 1
  {
    count := count + 1;
    pos := pos - 1;
  }
}
