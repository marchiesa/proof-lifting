// Problem 1: Popcount (count set bits) - SOLUTION

ghost function PopcountSpec(x: bv8): nat
{
  if x == 0 then 0
  else (if x & 1 == 1 then 1 else 0) + PopcountSpec(x >> 1)
}

// Key lemma: clearing the lowest set bit via x & (x-1) reduces popcount by 1.
// Proof by case split on LSB and structural recursion on the bitvector value.
lemma ClearLowestBitReducesPopcount(x: bv8)
  requires x != 0
  ensures PopcountSpec(x & (x - 1)) == PopcountSpec(x) - 1
  decreases x as int
{
  if x & 1 == 1 {
    // LSB is 1: x-1 flips only the LSB, so x & (x-1) clears it.
    // PopcountSpec(x) = 1 + PopcountSpec(x >> 1)
    // PopcountSpec(x & (x-1)) = 0 + PopcountSpec((x & (x-1)) >> 1)
    //                         = PopcountSpec(x >> 1)
    var cleared := x & (x - 1);
    assert cleared == x - 1;
    assert cleared & 1 == 0;
    assert cleared >> 1 == x >> 1;
  } else {
    // LSB is 0: the lowest set bit is in a higher position.
    // We recurse on the upper bits (x >> 1).
    // Key insight: when LSB is 0, clearing the lowest set bit
    // commutes with right-shift:
    //   (x & (x-1)) >> 1 == (x >> 1) & ((x >> 1) - 1)
    assert x >> 1 != 0;
    ClearLowestBitReducesPopcount(x >> 1);
    assert (x & (x - 1)) >> 1 == (x >> 1) & ((x >> 1) - 1);
  }
}

method Popcount(x: bv8) returns (count: nat)
  ensures count == PopcountSpec(x)
{
  var tmp: bv8 := x;
  count := 0;
  while tmp != 0
    invariant count + PopcountSpec(tmp) == PopcountSpec(x)
    decreases tmp as int
  {
    ClearLowestBitReducesPopcount(tmp);
    tmp := tmp & (tmp - 1);
    count := count + 1;
  }
}
