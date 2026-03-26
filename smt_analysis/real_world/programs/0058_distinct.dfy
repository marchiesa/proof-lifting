// Source: gamechanger/schemer/distinct
// URL: https://github.com/gamechanger/schemer/blob/1d1dd7da433d3b84ce5a80ded5a84ab4a65825ee/schemer/validators.py#L169-L178
// Original: Validates all items in a list are distinct (no duplicates)
// Gist: for i, item in enumerate(value): if item in value[i+1:]: return error

predicate AllDistinct(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

predicate InSeq(x: int, s: seq<int>)
{
  exists i :: 0 <= i < |s| && s[i] == x
}

method Distinct(value: seq<int>) returns (isDistinct: bool)
  ensures isDistinct <==> AllDistinct(value)
{
  isDistinct := true;
  var i := 0;
  while i < |value|
    invariant 0 <= i <= |value|
    invariant isDistinct <==> AllDistinct(value[..i])
  {
    // Check: is value[i] already in the prefix value[..i]?
    if InSeq(value[i], value[..i]) {
      assert value[..i+1] == value[..i] + [value[i]];
      isDistinct := false;
      assert !AllDistinct(value[..i+1]);
      return;
    }
    assert value[..i+1] == value[..i] + [value[i]];
    i := i + 1;
  }
  assert value[..|value|] == value;
}
