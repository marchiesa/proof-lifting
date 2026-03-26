// Auxiliary predicate to check if a position is the start of a word
ghost predicate isWordStart(str: string, i: int)
{
  0 <= i < |str| && 
  str[i] != ' ' && 
  (i == 0 || (i > 0 && str[i-1] == ' '))
}

// Auxiliary predicate to check if a position is the end of a word
ghost predicate isWordEnd(str: string, j: int)
{
  0 <= j <= |str| &&
  (j == |str| || str[j] == ' ')
}

// Auxiliary predicate expressing that `len` equals the size of the last word of `str`
ghost predicate lengthOfLastWordPost(str: string, len: int)
{
  // The last word starts at some position after the last space (or at 0)
  // and continues until we hit another space or the end of the string
  exists i,j {:trigger isWordStart(str, i), isWordEnd(str, j)} :: 
    0 <= i <= j <= |str| &&  // positions are within bounds
    isWordStart(str, i) &&   // i marks start of word
    isWordEnd(str, j) &&     // j marks end of word
    (forall k :: i <= k < j ==> str[k] != ' ') &&  // no spaces between i and j
    (forall k :: j < k < |str| ==> str[k] == ' ') &&  // only spaces after j
    j - i == len  // length of the word
}

// method to be verified
method lengthOfLastWord(s: string) returns (length: int)
  requires |s| >= 1                                      // the string is non-empty
  requires exists i :: 0 <= i < |s| && s[i] != ' '      // at least one word exists
  ensures  lengthOfLastWordPost(s, length)
{
    var tail := |s| - 1;
    length := 0;
    
    while tail >= 0 && s[tail] == ' '
    {
        tail := tail - 1;
    }
    
    while tail >= 0 && s[tail] != ' '
    {
        length := length + 1;
        tail := tail - 1;
    }
    
    return length;
}

method Main()
{
    var result;

    result := lengthOfLastWord(s:="Hello World ");
    if result != 5
    {
        print("Test failed: with input (\"s\":=\"Hello World \") got: ");
        print(result);
        print(" instead of \"5\")\n");
    }

    result := lengthOfLastWord(s:="   fly me   to   the moon   ");
    if result != 4
    {
        print("Test failed: with input (\"s\":=\"   fly me   to   the moon   \") got: ");
        print(result);
        print(" instead of \"4\")\n");
    }

    result := lengthOfLastWord(s:="luffy is still joyboy");
    if result != 6
    {
        print("Test failed: with input (\"s\":=\"luffy is still joyboy\") got: ");
        print(result);
        print(" instead of \"6\")\n");
    }

    result := lengthOfLastWord(s:="a");
    if result != 1
    {
        print("Test failed: with input (\"s\":=\"a\") got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := lengthOfLastWord(s:=" a");
    if result != 1
    {
        print("Test failed: with input (\"s\":=\" a\") got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := lengthOfLastWord(s:="a ");
    if result != 1
    {
        print("Test failed: with input (\"s\":=\"a \") got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := lengthOfLastWord(s:="  a  ");
    if result != 1
    {
        print("Test failed: with input (\"s\":=\"  a  \") got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := lengthOfLastWord(s:="word");
    if result != 4
    {
        print("Test failed: with input (\"s\":=\"word\") got: ");
        print(result);
        print(" instead of \"4\")\n");
    }

    result := lengthOfLastWord(s:=" word ");
    if result != 4
    {
        print("Test failed: with input (\"s\":=\" word \") got: ");
        print(result);
        print(" instead of \"4\")\n");
    }

    result := lengthOfLastWord(s:="multiple words here");
    if result != 4
    {
        print("Test failed: with input (\"s\":=\"multiple words here\") got: ");
        print(result);
        print(" instead of \"4\")\n");
    }

    result := lengthOfLastWord(s:="   multiple    words    with    spaces   ");
    if result != 6
    {
        print("Test failed: with input (\"s\":=\"   multiple    words    with    spaces   \") got: ");
        print(result);
        print(" instead of \"6\")\n");
    }

}
