ghost function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0
  else Sum(a[..|a|-1]) + a[|a|-1]
}

ghost function Product(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 1
  else Product(a[..|a|-1]) * a[|a|-1]
}

// Can exactly `budget` non-negative increments be distributed across `a`
// so that no element becomes zero (i.e., product of result is non-zero)?
ghost predicate CanDistribute(a: seq<int>, budget: nat)
  decreases |a|
{
  if |a| == 0 then
    budget == 0
  else
    exists d | 0 <= d <= budget ::
      a[|a|-1] + d != 0 &&
      CanDistribute(a[..|a|-1], budget - d)
}

// Can `budget` add-1 steps make both sum and product non-zero?
// Sum after modification is always Sum(a) + budget (independent of distribution).
// Product is non-zero iff CanDistribute finds a valid distribution avoiding zeros.
ghost predicate Feasible(a: seq<int>, budget: nat)
{
  Sum(a) + budget != 0 &&
  CanDistribute(a, budget)
}

method NonZero(a: seq<int>) returns (steps: int)
  requires |a| > 0
  ensures steps >= 0
  ensures Feasible(a, steps as nat)
  ensures forall k | 0 <= k < steps :: !Feasible(a, k as nat)
{
  var s := 0;
  var z := 0;
  var i := 0;
  while i < |a|
  {
    s := s + a[i];
    if a[i] == 0 {
      z := z + 1;
    }
    i := i + 1;
  }
  if s + z == 0 {
    return z + 1;
  } else {
    return z;
  }
}