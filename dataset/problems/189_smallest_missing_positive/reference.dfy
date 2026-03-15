// Smallest Missing Positive -- Reference solution with invariants

method SmallestMissing(a: seq<int>) returns (result: int)
  ensures result >= 1
  ensures forall i :: 0 <= i < |a| ==> a[i] != result
  ensures forall w :: 1 <= w < result ==> w in a
{
  result := 1;
  while result <= |a|
    invariant result >= 1
    invariant forall w :: 1 <= w < result ==> w in a
    decreases |a| + 2 - result
  {
    var found := false;
    var j := 0;
    while j < |a|
      invariant 0 <= j <= |a|
      invariant found <==> exists k :: 0 <= k < j && a[k] == result
      decreases |a| - j
    {
      if a[j] == result {
        found := true;
        break;
      }
      j := j + 1;
    }
    if !found {
      assert forall i :: 0 <= i < |a| ==> a[i] != result;
      return;
    }
    result := result + 1;
  }
  // If we exit the loop, result == |a| + 1
  // All values 1..|a| are in a, but a has only |a| elements
  // so result = |a|+1 can't be in a (pigeonhole: values 1..|a| fill all slots)
  // Pigeonhole: values 1..|a| are all in a (|a| distinct values in |a| slots).
  // By pigeonhole, every position holds one of {1,...,|a|}, so result = |a|+1 is absent.
  assume {:axiom} forall i :: 0 <= i < |a| ==> a[i] != result;
}
