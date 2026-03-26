// After swapping c[i] with a[i] (swapWithA=true) or b[i] (swapWithA=false),
// the resulting value at position i in string a
ghost function SwapResultA(a_i: char, c_i: char, swapWithA: bool): char
{
  if swapWithA then c_i else a_i
}

// The resulting value at position i in string b
ghost function SwapResultB(b_i: char, c_i: char, swapWithA: bool): char
{
  if swapWithA then b_i else c_i
}

// A swap direction is valid at position i if the resulting a[i] equals the resulting b[i]
ghost predicate ValidSwapChoice(a_i: char, b_i: char, c_i: char, swapWithA: bool)
{
  SwapResultA(a_i, c_i, swapWithA) == SwapResultB(b_i, c_i, swapWithA)
}

// There exists a valid swap direction at position i.
// Named predicate to give Z3 a clean trigger (avoids forall-exists nesting in invariants).
ghost predicate HasSwap(a_i: char, b_i: char, c_i: char)
{
  exists swapWithA: bool :: ValidSwapChoice(a_i, b_i, c_i, swapWithA)
}

// The problem is solvable iff for every position there exists a swap direction
// (swap c[i] with a[i], or swap c[i] with b[i]) such that after all swaps, a == b.
// Since each position's swap is independent, this decomposes per position.
ghost predicate CanMakeEqual(a: string, b: string, c: string)
  requires |a| == |b| == |c|
{
  forall i | 0 <= i < |a| :: HasSwap(a[i], b[i], c[i])
}

method ThreeStrings(a: string, b: string, c: string) returns (result: bool)
  requires |a| == |b| == |c|
  ensures result == CanMakeEqual(a, b, c)
{
  var i := 0;
  while i < |a|
  {
    if a[i] != c[i] && b[i] != c[i] {
      return false;
    }
    i := i + 1;
  }
  return true;
}