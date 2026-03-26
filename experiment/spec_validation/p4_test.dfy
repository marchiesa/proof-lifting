predicate IsPalindrome(word: seq<char>)
{
  forall i :: 0 <= i < |word| ==> word[i] == word[|word| - 1 - i]
}

predicate SubstringAt(text: seq<char>, sub: seq<char>, start: int)
{
  0 <= start && 
  start + |sub| <= |text| &&
  sub == text[start .. start + |sub|]
}

predicate IsSubstring(text: seq<char>, sub: seq<char>)
{
  exists start :: 0 <= start <= |text| - |sub| && SubstringAt(text, sub, start)
}

predicate PalindromicSubstringAt(s: seq<char>, start: int, len: int)
{
  0 <= start < |s| && 
  0 <= len <= |s| && 
  start + len <= |s| &&
  IsPalindrome(s[start..start+len])
}

predicate longest_palindromic_substringPost(s: seq<char>, result: seq<char>)
{
  |result| >= 1                            // the returned substring is non-empty
  && IsSubstring(s, result)               // it is a contiguous substring of the input
  && IsPalindrome(result)                 // the substring itself is a palindrome
  && (forall start, len :: 
      0 <= start < |s| && 0 <= len <= |s| &&
      PalindromicSubstringAt(s, start, len) ==> len <= |result|)  // no palindromic substring is longer
}

// method to be verified
method longest_palindromic_substring(s: seq<char>) returns (result: seq<char>)
  requires |s| >= 1                       // input string must be non-empty
  ensures  longest_palindromic_substringPost(s, result)
{
    var n := |s|;
    if n == 0 {
        return [];
    }

    var start := 0;
    var maxLength := 1;
    var i := 0;

    while i < n
    {
        var l := i;
        var r := i;

        // Expand for identical characters
        while r < n - 1 && s[r] == s[r + 1]
        {
            r := r + 1;
        }
        i := r;

        // Expand around center
        while l > 0 && r < n - 1 && s[l - 1] == s[r + 1]
        {
            l := l - 1;
            r := r + 1;
        }

        var length := r - l + 1;
        if length > maxLength
        {
            start := l;
            maxLength := length;
        }

        i := i + 1;
    }

    // Create result sequence
    result := s[start..start + maxLength];
}

method Main()
{
    var result;

    result := longest_palindromic_substring(s:="babad");
    if result != "bab"
    {
        print("Test failed: with input (\"s\":=\"babad\") got: ");
        print(result);
        print(" instead of \"bab\")\n");
    }

    result := longest_palindromic_substring(s:="cbbd");
    if result != "bb"
    {
        print("Test failed: with input (\"s\":=\"cbbd\") got: ");
        print(result);
        print(" instead of \"bb\")\n");
    }

    result := longest_palindromic_substring(s:="a");
    if result != "a"
    {
        print("Test failed: with input (\"s\":=\"a\") got: ");
        print(result);
        print(" instead of \"a\")\n");
    }

    result := longest_palindromic_substring(s:="aa");
    if result != "aa"
    {
        print("Test failed: with input (\"s\":=\"aa\") got: ");
        print(result);
        print(" instead of \"aa\")\n");
    }

    result := longest_palindromic_substring(s:="racecar");
    if result != "racecar"
    {
        print("Test failed: with input (\"s\":=\"racecar\") got: ");
        print(result);
        print(" instead of \"racecar\")\n");
    }

    result := longest_palindromic_substring(s:="abcdefg");
    if result != "a"
    {
        print("Test failed: with input (\"s\":=\"abcdefg\") got: ");
        print(result);
        print(" instead of \"a\")\n");
    }

    result := longest_palindromic_substring(s:="aacabdkacaa");
    if result != "aca"
    {
        print("Test failed: with input (\"s\":=\"aacabdkacaa\") got: ");
        print(result);
        print(" instead of \"aca\")\n");
    }

    result := longest_palindromic_substring(s:="bbbbbb");
    if result != "bbbbbb"
    {
        print("Test failed: with input (\"s\":=\"bbbbbb\") got: ");
        print(result);
        print(" instead of \"bbbbbb\")\n");
    }

    result := longest_palindromic_substring(s:="abcba");
    if result != "abcba"
    {
        print("Test failed: with input (\"s\":=\"abcba\") got: ");
        print(result);
        print(" instead of \"abcba\")\n");
    }

}
