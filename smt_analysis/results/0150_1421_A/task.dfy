// --- Specification: model the problem's structure ---

// Bitwise XOR for non-negative integers
ghost function BitwiseXor(a: int, b: int): int
  requires a >= 0 && b >= 0
  decreases a + b
{
  if a == 0 && b == 0 then 0
  else (if a % 2 != b % 2 then 1 else 0) + 2 * BitwiseXor(a / 2, b / 2)
}

// The objective function from the problem: (a XOR x) + (b XOR x)
ghost function XorwiceObjective(a: int, b: int, x: int): int
  requires a >= 0 && b >= 0 && x >= 0
{
  BitwiseXor(a, x) + BitwiseXor(b, x)
}

// The result is the smallest possible value of the objective over all x.
ghost predicate IsMinimumXorwice(a: int, b: int, result: int)
  requires a >= 0 && b >= 0
{
  (exists x: nat :: result == XorwiceObjective(a, b, x))
  &&
  (forall x: nat :: result <= XorwiceObjective(a, b, x))
}

// --- Method with specification ---

method XORwice(a: int, b: int) returns (result: int)
  requires a >= 0 && b >= 0
  ensures IsMinimumXorwice(a, b, result)
{
  var x := a;
  var y := b;
  if x < y {
    x := b;
    y := a;
  }
  // Compute z = x AND y (bitwise)
  var z := 0;
  var tX := x;
  var tY := y;
  var bit := 1;
  while tX > 0 || tY > 0
    decreases tX + tY
  {
    if tX % 2 == 1 && tY % 2 == 1 {
      z := z + bit;
    }
    tX := tX / 2;
    tY := tY / 2;
    bit := bit * 2;
  }
  // Compute (x ^ z) + (y ^ z)
  var axz := 0;
  tX := x;
  var tZ := z;
  bit := 1;
  while tX > 0 || tZ > 0
    decreases tX + tZ
  {
    if tX % 2 != tZ % 2 {
      axz := axz + bit;
    }
    tX := tX / 2;
    tZ := tZ / 2;
    bit := bit * 2;
  }
  var bxz := 0;
  tY := y;
  tZ := z;
  bit := 1;
  while tY > 0 || tZ > 0
    decreases tY + tZ
  {
    if tY % 2 != tZ % 2 {
      bxz := bxz + bit;
    }
    tY := tY / 2;
    tZ := tZ / 2;
    bit := bit * 2;
  }
  result := axz + bxz;
}