// Problem 1: Popcount (count set bits)
//
// Implement a method that counts the number of 1-bits in a bv8 value.
// The specification uses a recursive ghost function, but the implementation
// uses the standard bit-manipulation trick: x &= (x - 1) clears the
// lowest set bit.
//
// Z3's bitvector solver struggles because:
// - The recursive ghost function PopcountSpec operates bit-by-bit from LSB
// - The loop invariant must relate an intermediate bv8 value to partial popcount
// - Bridging the bitvector domain and natural number counting is hard
// - Without a lemma proving x & (x-1) reduces popcount by 1, Z3 cannot
//   connect the bit-clearing trick to the recursive spec

ghost function PopcountSpec(x: bv8): nat
{
  if x == 0 then 0
  else (if x & 1 == 1 then 1 else 0) + PopcountSpec(x >> 1)
}

// TASK: Add loop invariants and any necessary lemmas to make this verify.
method Popcount(x: bv8) returns (count: nat)
  ensures count == PopcountSpec(x)
{
  var tmp: bv8 := x;
  count := 0;
  while tmp != 0
    decreases tmp as int
  {
    tmp := tmp & (tmp - 1); // clears lowest set bit
    count := count + 1;
  }
}
