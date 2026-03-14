// Problem 3: Bit reversal
//
// Reverse the bits of a bv8: bit 0 goes to bit 7, bit 1 to bit 6, etc.
// The standard loop shifts in bits from the LSB of the input to the
// LSB of the output, building the reversed value one bit at a time.
//
// Z3 struggles because:
// - The postcondition is a universal quantifier over bit positions
// - Each loop iteration changes the relationship between r's bits and x's bits
// - Z3 must reason about how (r << 1) | b affects ALL bit positions of r,
//   not just the LSB -- this requires bitvector shift reasoning combined
//   with quantifier instantiation
// - The loop invariant must track which bits of r have been set and to what

function GetBit(x: bv8, i: int): bv8
  requires 0 <= i < 8
{
  (x >> (i as bv8)) & 1
}

// TASK: Add loop invariants and any necessary ghost functions/lemmas
// to make this method verify.
method BitReverse(x: bv8) returns (r: bv8)
  ensures forall i: int :: 0 <= i < 8 ==> GetBit(r, i) == GetBit(x, 7 - i)
{
  r := 0;
  var tmp := x;
  var j: int := 0;
  while j < 8
    decreases 8 - j
  {
    r := (r << 1) | (tmp & 1);
    tmp := tmp >> 1;
    j := j + 1;
  }
}
