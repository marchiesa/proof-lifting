// Problem 2: Power of 2 check
//
// Check whether a bv8 is a power of 2 using the classic bit trick:
//   x != 0 && x & (x-1) == 0
// The spec says there exists k such that x == 1 << k.
//
// Z3 struggles because:
// - The existential quantifier over bit positions needs a witness
// - Connecting the algebraic bit trick (x & (x-1) == 0) to the
//   existential "there's a k such that x == 1 << k" requires
//   enumerating all 8 possible bit positions
// - The reverse direction (existential => bit trick) needs
//   case analysis on k to show each power satisfies the trick
// - Without triggers, Z3 cannot instantiate the quantifier

ghost function Shift1Left(k: int): bv8
  requires 0 <= k < 8
{
  (1 as bv8) << (k as bv8)
}

ghost predicate IsPowerOf2Spec(x: bv8)
{
  exists k: int {:trigger Shift1Left(k)} :: 0 <= k < 8 && x == Shift1Left(k)
}

// TASK: Add lemmas to make this method verify.
// Hint: you need to prove both directions of the equivalence.
method CheckPowerOf2(x: bv8) returns (result: bool)
  ensures result <==> IsPowerOf2Spec(x)
{
  result := x != 0 && x & (x - 1) == 0;
}
