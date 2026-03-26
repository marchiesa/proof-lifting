predicate IsUniqueSubstring(s: seq<char>, start: int, end: int)
requires |s| > 0
{
    0 <= start < |s| && start <= end <= |s| &&
    forall k1, k2 :: start <= k1 < end && start <= k2 < end && s[k1] == s[k2] ==> k1 == k2
}

predicate LengthOfLongestSubstringPost(s: seq<char>, maxLength: int)
{
    // Non-negativity and bounded by the whole string
    0 <= maxLength <= |s|

    // There exists a unique-character substring whose length equals maxLength
    &&
    exists start, end :: 
        0 <= start < |s| && start <= end <= |s| && 
        end - start == maxLength && 
        IsUniqueSubstring(s, start, end)

    // No unique-character substring is longer than maxLength
    &&
    forall start, end :: 
        0 <= start < |s| && start <= end <= |s| && 
        IsUniqueSubstring(s, start, end) ==>
        end - start <= maxLength
}

// method to be verified
method LengthOfLongestSubstring(s: seq<char>) returns (maxLength: int)
    ensures LengthOfLongestSubstringPost(s, maxLength)
{
    var left := 0;
    var right := 0;
    maxLength := 0;
    var characters := {};

    while right < |s|
    {
        if s[right] !in characters
        {
            characters := characters + {s[right]};
            maxLength := if right - left + 1 > maxLength then right - left + 1 else maxLength;
            right := right + 1;
        }
        else
        {
            characters := characters - {s[left]};
            left := left + 1;
        }
    }
    
    return maxLength;
}

method Main()
{
    var result;

    result := LengthOfLongestSubstring(s:="");
    if result != 0
    {
        print("Test failed: with input (\"s\":=\"\") got: ");
        print(result);
        print(" instead of \"0\")\n");
    }

    result := LengthOfLongestSubstring(s:="a");
    if result != 1
    {
        print("Test failed: with input (\"s\":=\"a\") got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := LengthOfLongestSubstring(s:="abcabcbb");
    if result != 3
    {
        print("Test failed: with input (\"s\":=\"abcabcbb\") got: ");
        print(result);
        print(" instead of \"3\")\n");
    }

    result := LengthOfLongestSubstring(s:="bbbbb");
    if result != 1
    {
        print("Test failed: with input (\"s\":=\"bbbbb\") got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := LengthOfLongestSubstring(s:="pwwkew");
    if result != 3
    {
        print("Test failed: with input (\"s\":=\"pwwkew\") got: ");
        print(result);
        print(" instead of \"3\")\n");
    }

    result := LengthOfLongestSubstring(s:="dvdf");
    if result != 3
    {
        print("Test failed: with input (\"s\":=\"dvdf\") got: ");
        print(result);
        print(" instead of \"3\")\n");
    }

    result := LengthOfLongestSubstring(s:="aab");
    if result != 2
    {
        print("Test failed: with input (\"s\":=\"aab\") got: ");
        print(result);
        print(" instead of \"2\")\n");
    }

    result := LengthOfLongestSubstring(s:="abba");
    if result != 2
    {
        print("Test failed: with input (\"s\":=\"abba\") got: ");
        print(result);
        print(" instead of \"2\")\n");
    }

    result := LengthOfLongestSubstring(s:="tmmzuxt");
    if result != 5
    {
        print("Test failed: with input (\"s\":=\"tmmzuxt\") got: ");
        print(result);
        print(" instead of \"5\")\n");
    }

    result := LengthOfLongestSubstring(s:="hello world");
    if result != 6
    {
        print("Test failed: with input (\"s\":=\"hello world\") got: ");
        print(result);
        print(" instead of \"6\")\n");
    }

    result := LengthOfLongestSubstring(s:="123456789");
    if result != 9
    {
        print("Test failed: with input (\"s\":=123456789) got: ");
        print(result);
        print(" instead of \"9\")\n");
    }

    result := LengthOfLongestSubstring(s:="   ");
    if result != 1
    {
        print("Test failed: with input (\"s\":=\"   \") got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := LengthOfLongestSubstring(s:="aaaaaa");
    if result != 1
    {
        print("Test failed: with input (\"s\":=\"aaaaaa\") got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := LengthOfLongestSubstring(s:="abcdefg");
    if result != 7
    {
        print("Test failed: with input (\"s\":=\"abcdefg\") got: ");
        print(result);
        print(" instead of \"7\")\n");
    }

    result := LengthOfLongestSubstring(s:="!@#$%^&*()");
    if result != 10
    {
        print("Test failed: with input (\"s\":=\"!@#$%^&*()\") got: ");
        print(result);
        print(" instead of \"10\")\n");
    }

}
