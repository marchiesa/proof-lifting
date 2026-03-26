// Source: frostming/atoml/contains_list
// URL: https://github.com/frostming/atoml/blob/85414ef77777366887a819a05b496d5279296cd2/atoml/decoder.py#L28-L35
// Original: Check if longer list starts with shorter list
// Gist: for a, b in zip(shorter, longer): if a != b: return False

predicate IsPrefix(prefix: seq<int>, full: seq<int>)
{
  |prefix| <= |full| && prefix == full[..|prefix|]
}

method ContainsList(longer: seq<int>, shorter: seq<int>) returns (result: bool)
  ensures result <==> (|longer| > |shorter| && IsPrefix(shorter, longer))
{
  if |longer| <= |shorter| {
    result := false;
    return;
  }
  result := true;
  var i := 0;
  while i < |shorter|
    invariant 0 <= i <= |shorter|
    invariant result <==> IsPrefix(shorter[..i], longer)
  {
    assert shorter[..i+1] == shorter[..i] + [shorter[i]];
    if shorter[i] != longer[i] {
      result := false;
      assert !IsPrefix(shorter, longer);
      return;
    }
    i := i + 1;
  }
  assert shorter[..|shorter|] == shorter;
}
