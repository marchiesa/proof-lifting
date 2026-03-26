// Auxiliary predicate describing when the string `pattern` occurs
// inside `text` starting exactly at position `pos`
predicate OccursAt(text: string, pattern: string, pos: int)
  reads {}
{
  0 <= pos &&
  pos + |pattern| <= |text| &&
  text[pos .. pos + |pattern|] == pattern
}

// All postconditions for `strStr` collected in a single predicate
predicate strStrPost(haystack: string, needle: string, result: int)
  reads {}
{
  ( (forall k:int :: 0 <= k <= |haystack| - |needle| ==> !OccursAt(haystack, needle, k))
      ==> result == -1)
  &&
  ( (exists k:int :: 0 <= k <= |haystack| - |needle| && OccursAt(haystack, needle, k))
      ==> 0 <= result <= |haystack| - |needle|
          && OccursAt(haystack, needle, result)
          && (forall k:int :: 0 <= k < result ==> !OccursAt(haystack, needle, k)))
}

method strStr(haystack: string, needle: string) returns (result: int)
  requires |haystack| >= 1
  requires |needle| >= 1
  ensures  strStrPost(haystack, needle, result)
{
    if needle == "" {
        return 0;
    }

    var i := 0;
    while i <= |haystack| - |needle|
      invariant 0 <= i
      invariant forall k :: 0 <= k < i ==> !OccursAt(haystack, needle, k)
    {
        var j := 0;
        var found := true;

        while j < |needle| && found
          invariant 0 <= j <= |needle|
          invariant found ==> haystack[i .. i + j] == needle[0 .. j]
          invariant !found ==> !OccursAt(haystack, needle, i)
        {
            if i + j >= |haystack| || haystack[i + j] != needle[j] {
                found := false;
            }
            j := j + 1;
        }

        if found {
            assert j == |needle|;
            assert haystack[i .. i + |needle|] == needle[0 .. |needle|];
            assert haystack[i .. i + |needle|] == needle;
            assert OccursAt(haystack, needle, i);
            return i;
        }

        i := i + 1;
    }

    return -1;
}
