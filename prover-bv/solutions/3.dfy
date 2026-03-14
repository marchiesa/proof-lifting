// Problem 3: Bit reversal

function GetBit(x: bv8, i: int): bv8
  requires 0 <= i < 8
{
  (x >> (i as bv8)) & 1
}

// Ghost function to compute the expected reversed value after j iterations
ghost function PartialReverse(x: bv8, j: int): bv8
  requires 0 <= j <= 8
{
  if j == 0 then 0
  else (PartialReverse(x, j - 1) << 1) | GetBit(x, j - 1)
}

// Lemma: PartialReverse correctly reverses the first j bits
lemma {:fuel PartialReverse, 9} {:fuel GetBit, 9} PartialReverseCorrect(x: bv8, j: int)
  requires 0 <= j <= 8
  ensures forall i: int :: 0 <= i < j ==> GetBit(PartialReverse(x, j), j - 1 - i) == GetBit(x, i)
  ensures forall i: int :: j <= i < 8 ==> GetBit(PartialReverse(x, j), i) == 0
{
}

// Lemma: the loop body maintains the invariant
lemma {:fuel PartialReverse, 9} {:fuel GetBit, 9} PartialReverseStep(x: bv8, j: int, r: bv8, tmp: bv8)
  requires 0 <= j < 8
  requires r == PartialReverse(x, j)
  requires tmp == x >> (j as bv8)
  ensures (r << 1) | (tmp & 1) == PartialReverse(x, j + 1)
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
    invariant r == PartialReverse(x, j)
    decreases 8 - j
  {
    PartialReverseStep(x, j, r, tmp);
    r := (r << 1) | (tmp & 1);
    tmp := tmp >> 1;
    j := j + 1;
  }
  PartialReverseCorrect(x, 8);
}
