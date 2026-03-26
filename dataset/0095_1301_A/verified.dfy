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

// The problem is solvable iff for every position there exists a swap direction
// (swap c[i] with a[i], or swap c[i] with b[i]) such that after all swaps, a == b.
// Since each position's swap is independent, this decomposes per position.
ghost predicate CanMakeEqual(a: string, b: string, c: string)
  requires |a| == |b| == |c|
{
  forall i | 0 <= i < |a| ::
    HasSwap(a[i], b[i], c[i])
  // exists swapWithA: bool :: ValidSwapChoice(a[i], b[i], c[i], swapWithA) // This formulation is much harder to verify
}

ghost predicate HasSwap(a: char, b: char, c: char)
{
  exists swapWithA: bool :: ValidSwapChoice(a, b, c, swapWithA)
}

method ThreeStrings(a: string, b: string, c: string) returns (result: bool)
  requires |a| == |b| == |c|
  ensures result == CanMakeEqual(a, b, c)
{
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall j | 0 <= j < i ::
                ValidSwapChoice(a[j], b[j], c[j], true) || ValidSwapChoice(a[j], b[j], c[j], false)
  {
    if a[i] != c[i] && b[i] != c[i] {
      return false;
    }
    // This block is for Readability, the SMT solver manages it all by itself.
    if a[i] == c[i] {
      assert ValidSwapChoice(a[i], b[i], c[i], false);
    } else {
      assert b[i] == c[i];
      assert ValidSwapChoice(a[i], b[i], c[i], true);
    }
    i := i + 1;
  }
  return true;
}