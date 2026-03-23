// Pattern: Validate that all elements satisfy a property
// Source: acceptable/validate (validate JSON payload fields)
//         icontract/_kwargs_from_call (check function arguments)
// Real-world: input validation, config checking, data quality

predicate InRange(x: int, lo: int, hi: int)
{
  lo <= x <= hi
}

predicate AllInRange(a: seq<int>, lo: int, hi: int)
{
  forall i :: 0 <= i < |a| ==> InRange(a[i], lo, hi)
}

method ValidateRange(a: seq<int>, lo: int, hi: int) returns (valid: bool)
  requires lo <= hi
  ensures valid <==> AllInRange(a, lo, hi)
{
  valid := true;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant valid <==> AllInRange(a[..i], lo, hi)
  {
    assert InRange(a[i], lo, hi) <==> (lo <= a[i] <= hi);  // SMT QUIRK: A2 predicate instantiation
    if !InRange(a[i], lo, hi) {
      valid := false;
      assert !AllInRange(a[..i+1], lo, hi);  // SMT QUIRK: A2 predicate propagation
      return;
    }
    assert a[..i+1] == a[..i] + [a[i]];  // SMT QUIRK: B1 sequence extensionality
    i := i + 1;
  }
  assert a[..|a|] == a;  // SMT QUIRK: B1 take-full
}
