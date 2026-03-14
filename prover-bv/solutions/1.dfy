// Problem 1: Popcount (count set bits)

ghost function PopcountSpec(x: bv8): nat
{
  if x == 0 then 0
  else (if x & 1 == 1 then 1 else 0) + PopcountSpec(x >> 1)
}

// Key lemma: clearing the lowest set bit decreases popcount by 1.
// We prove both parts: PopcountSpec(x) > 0 and the decrement property.
// For bv8, we use high fuel to let Z3 fully unroll the recursive definition.
lemma {:fuel PopcountSpec, 9} PopcountClearLowest(x: bv8)
  requires x != 0
  ensures PopcountSpec(x) > 0
  ensures PopcountSpec(x & (x - 1)) == PopcountSpec(x) - 1
{
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
    PopcountClearLowest(tmp);
    tmp := tmp & (tmp - 1);
    count := count + 1;
  }
}
