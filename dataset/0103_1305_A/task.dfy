// ---------------------------------------------------------------------------
// Specification predicates and functions
// ---------------------------------------------------------------------------

ghost predicate IsSorted(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] <= s[j]
}

ghost predicate PairwiseDistinct(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] != s[j]
}

ghost predicate IsPermutation(a: seq<int>, b: seq<int>)
{
  multiset(a) == multiset(b)
}

ghost function Sums(x: seq<int>, y: seq<int>): seq<int>
  requires |x| == |y|
  decreases |x|
{
  if |x| == 0 then []
  else Sums(x[..|x|-1], y[..|y|-1]) + [x[|x|-1] + y[|y|-1]]
}

// ---------------------------------------------------------------------------
// Methods with specification
// ---------------------------------------------------------------------------

method Insert(sorted: seq<int>, val: int) returns (result: seq<int>)
  requires IsSorted(sorted)
  ensures IsSorted(result)
  ensures IsPermutation(result, sorted + [val])
{
  var i := 0;
  while i < |sorted| && sorted[i] < val
  {
    i := i + 1;
  }
  result := sorted[..i] + [val] + sorted[i..];
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures IsSorted(sorted)
  ensures IsPermutation(sorted, s)
{
  sorted := [];
  var i := 0;
  while i < |s|
  {
    sorted := Insert(sorted, s[i]);
    i := i + 1;
  }
}

// Specification of the problem:
//   Given two length-n sequences with pairwise-distinct elements,
//   produce permutations x of a and y of b such that the elementwise
//   sums x[i] + y[i] are pairwise distinct.
method KuroniAndTheGifts(a: seq<int>, b: seq<int>) returns (x: seq<int>, y: seq<int>)
  requires |a| == |b|
  requires PairwiseDistinct(a)
  requires PairwiseDistinct(b)
  ensures |x| == |a|
  ensures |y| == |a|
  ensures IsPermutation(x, a)
  ensures IsPermutation(y, b)
  ensures PairwiseDistinct(Sums(x, y))
{
  x := SortSeq(a);
  y := SortSeq(b);
}