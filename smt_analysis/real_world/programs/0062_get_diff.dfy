// Source: mozilla-services/amo2kinto/get_diff
// URL: https://github.com/mozilla-services/amo2kinto/blob/1ec40647e77cf89badbea4a58d328243daed49a9/amo2kinto/synchronize.py#L16-L45
// Original: Get diff between two record lists: find items in source but not in dest
// Gist: to_create = [s for s in source if s not in dest]

predicate InSeq(x: int, s: seq<int>)
{
  exists i :: 0 <= i < |s| && s[i] == x
}

ghost predicate AllFromSource(result: seq<int>, source: seq<int>)
{
  forall k :: 0 <= k < |result| ==> InSeq(result[k], source)
}

ghost predicate NoneInDest(result: seq<int>, dest: seq<int>)
{
  forall k :: 0 <= k < |result| ==> !InSeq(result[k], dest)
}

method GetToCreate(source: seq<int>, dest: seq<int>) returns (toCreate: seq<int>)
  ensures AllFromSource(toCreate, source)
  ensures NoneInDest(toCreate, dest)
{
  toCreate := [];
  var i := 0;
  while i < |source|
    invariant 0 <= i <= |source|
    invariant AllFromSource(toCreate, source)
    invariant NoneInDest(toCreate, dest)
  {
    var found := false;
    var j := 0;
    while j < |dest|
      invariant 0 <= j <= |dest|
      invariant !found ==> forall k :: 0 <= k < j ==> dest[k] != source[i]
    {
      if dest[j] == source[i] {
        found := true;
        break;
      }
      j := j + 1;
    }
    if !found {
      assert !InSeq(source[i], dest);
      assert InSeq(source[i], source);
      assert AllFromSource(toCreate, source);
      toCreate := toCreate + [source[i]];
    }
    i := i + 1;
  }
}
