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
  // Case 1: no occurrence of `needle` in `haystack`
  ( (forall k:int :: 0 <= k <= |haystack| - |needle| ==> !OccursAt(haystack, needle, k))
      ==> result == -1)

  &&

  // Case 2: at least one occurrence exists – `result` is the first such index
  ( (exists k:int :: 0 <= k <= |haystack| - |needle| && OccursAt(haystack, needle, k))
      ==> 0 <= result <= |haystack| - |needle|
          && OccursAt(haystack, needle, result)
          && (forall k:int :: 0 <= k < result ==> !OccursAt(haystack, needle, k)))
}

// method to be verified
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
    {
        var j := 0;
        var found := true;
        
        while j < |needle| && found
        {
            if i + j >= |haystack| || haystack[i + j] != needle[j] {
                found := false;
            }
            j := j + 1;
        }
        
        if found {
            return i;
        }
        
        i := i + 1;
    }
    
    return -1;
}

method Main()
{
    var result;

    result := strStr(haystack:="sadbutsad", needle:="sad");
    if result != 0
    {
        print("Test failed: with input (\"haystack\":=\"sadbutsad\", \"needle\":=\"sad\") got: ");
        print(result);
        print(" instead of \"0\")\n");
    }

    result := strStr(haystack:="leetcode", needle:="leeto");
    if result != -1
    {
        print("Test failed: with input (\"haystack\":=\"leetcode\", \"needle\":=\"leeto\") got: ");
        print(result);
        print(" instead of \"-1\")\n");
    }

    result := strStr(haystack:="a", needle:="a");
    if result != 0
    {
        print("Test failed: with input (\"haystack\":=\"a\", \"needle\":=\"a\") got: ");
        print(result);
        print(" instead of \"0\")\n");
    }

    result := strStr(haystack:="mississippi", needle:="issip");
    if result != 4
    {
        print("Test failed: with input (\"haystack\":=\"mississippi\", \"needle\":=\"issip\") got: ");
        print(result);
        print(" instead of \"4\")\n");
    }

    result := strStr(haystack:="aaaaa", needle:="bba");
    if result != -1
    {
        print("Test failed: with input (\"haystack\":=\"aaaaa\", \"needle\":=\"bba\") got: ");
        print(result);
        print(" instead of \"-1\")\n");
    }

}
