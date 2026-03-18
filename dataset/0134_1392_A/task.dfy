ghost predicate CanReduce(a: seq<int>, steps: nat)
  decreases steps
{
  if steps == 0 then
    true
  else if |a| < 2 then
    false
  else
    exists i | 0 <= i < |a| - 1 ::
      a[i] != a[i+1] && CanReduce(a[..i] + [a[i] + a[i+1]] + a[i+2..], steps - 1)
}

method OmkarAndPassword(a: seq<int>) returns (result: int)
  requires |a| >= 1
  ensures 1 <= result <= |a|
  ensures CanReduce(a, |a| - result)
  ensures result == 1 || !CanReduce(a, |a| - result + 1)
{
  var lo := a[0];
  var hi := a[0];
  var i := 1;
  while i < |a|
  {
    if a[i] < lo { lo := a[i]; }
    if a[i] > hi { hi := a[i]; }
    i := i + 1;
  }
  if lo == hi {
    return |a|;
  } else {
    return 1;
  }
}