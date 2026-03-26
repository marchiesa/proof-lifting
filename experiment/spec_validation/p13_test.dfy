predicate IsPrefix(p: string, s: string)
{
  |p| <= |s| && p == s[..|p|]
}

predicate IsCommonPrefix(p: string, strs: seq<string>)
{
  forall i :: 0 <= i < |strs| ==> IsPrefix(p, strs[i])
}

predicate LongestCommonPrefixPost(strs: seq<string>, result: string)
{
  // result is a common prefix of all strings
  IsCommonPrefix(result, strs) &&
  // result has maximal length among all common prefixes
  // We only need to check prefixes of the first string
  forall i :: 0 <= i < |strs| && 0 <= i <= |strs[i]| ==>
    IsCommonPrefix(strs[i][..i], strs) ==> |strs[i][..i]| <= |result|
}

// method to be verified
method LongestCommonPrefix(strs: seq<string>) returns (result: string)
  requires |strs| >= 1  // at least one string in the sequence
  requires forall i :: 0 <= i < |strs| ==> |strs[i]| <= 200  // length constraint
  ensures LongestCommonPrefixPost(strs, result)
{
    var firstStr := strs[0];
    var i := 0;

    while i < |firstStr|
    {
        var j := 1;
        while j < |strs|
        {
            if i >= |strs[j]| || strs[j][i] != firstStr[i] {
                return firstStr[..i];
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    return firstStr;
}

method Main()
{
    var result;

    result := LongestCommonPrefix(strs:=['flower', 'flow', 'flight']);
    if result != "fl"
    {
        print("Test failed: with input (\"strs\":=['flower', 'flow', 'flight']) got: ");
        print(result);
        print(" instead of \"fl\")\n");
    }

    result := LongestCommonPrefix(strs:=['dog', 'racecar', 'car']);
    if result != ""
    {
        print("Test failed: with input (\"strs\":=['dog', 'racecar', 'car']) got: ");
        print(result);
        print(" instead of \"\")\n");
    }

    result := LongestCommonPrefix(strs:=['a']);
    if result != "a"
    {
        print("Test failed: with input (\"strs\":=['a']) got: ");
        print(result);
        print(" instead of \"a\")\n");
    }

    result := LongestCommonPrefix(strs:=['aa', 'aa']);
    if result != "aa"
    {
        print("Test failed: with input (\"strs\":=['aa', 'aa']) got: ");
        print(result);
        print(" instead of \"aa\")\n");
    }

    result := LongestCommonPrefix(strs:=['abc', 'ab', 'abcd']);
    if result != "ab"
    {
        print("Test failed: with input (\"strs\":=['abc', 'ab', 'abcd']) got: ");
        print(result);
        print(" instead of \"ab\")\n");
    }

    result := LongestCommonPrefix(strs:=['', 'b']);
    if result != ""
    {
        print("Test failed: with input (\"strs\":=['', 'b']) got: ");
        print(result);
        print(" instead of \"\")\n");
    }

    result := LongestCommonPrefix(strs:=['prefix', 'prefix', 'prefix']);
    if result != "prefix"
    {
        print("Test failed: with input (\"strs\":=['prefix', 'prefix', 'prefix']) got: ");
        print(result);
        print(" instead of \"prefix\")\n");
    }

    result := LongestCommonPrefix(strs:=['a', 'b', 'c']);
    if result != ""
    {
        print("Test failed: with input (\"strs\":=['a', 'b', 'c']) got: ");
        print(result);
        print(" instead of \"\")\n");
    }

}
