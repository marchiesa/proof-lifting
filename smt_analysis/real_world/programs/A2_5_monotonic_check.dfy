// Pattern: Check that a function is monotonically increasing over values
// Source: numerical libraries checking convergence
//         time series validation, pricing validation
// Real-world: ensuring timestamps are increasing, stock price validation

function F(x: int): int
{
  x * x  // example: quadratic function
}

predicate Monotonic(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> F(a[i]) <= F(a[j])
}

method CheckMonotonic(a: seq<int>) returns (mono: bool)
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0  // non-negative inputs
  ensures mono ==> Monotonic(a)
{
  if |a| <= 1 {
    mono := true;
    return;
  }
  mono := true;
  var i := 0;
  while i < |a| - 1
    invariant 0 <= i <= |a| - 1
    invariant mono ==> forall j, k :: 0 <= j < k <= i ==> F(a[j]) <= F(a[k])
  {
    assert F(a[i]) == a[i] * a[i];  // SMT QUIRK: C1 NLA — need to unfold F for comparison
    assert F(a[i+1]) == a[i+1] * a[i+1];  // SMT QUIRK: C1 NLA
    if F(a[i]) > F(a[i+1]) {
      mono := false;
      return;
    }
    i := i + 1;
  }
}
