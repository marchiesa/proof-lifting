predicate scramble(a: seq<char>, b: seq<char>)
  decreases |a|
{
  |a| == |b| &&
  (
    if |a| == 1 then
      a == b
    else
      exists split: int ::
        1 <= split < |a| &&
        (
          (scramble(a[..split], b[..split]) &&
           scramble(a[split..], b[split..])) ||
          (scramble(a[..split], b[|b|-split..]) &&
           scramble(a[split..], b[..|b|-split]))
        )
  )
}

predicate isScramblePost(s1: seq<char>, s2: seq<char>, result: bool)
{
  result <==> scramble(s1, s2)
}

method {:axiom} SortString(s: seq<char>) returns (sorted: seq<char>)
  ensures multiset(sorted) == multiset(s)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]


// method to be verified
method isScramble(s1: seq<char>, s2: seq<char>) returns (result: bool)
  requires |s1| == |s2| && |s1| >= 1
  ensures isScramblePost(s1, s2, result)
  decreases |s1|
{
    if s1 == s2 {
        return true;
    }
    
    // Check if sorted strings are equal
    var chars1 := SortString(s1[..]);
    var chars2 := SortString(s2[..]);
    if chars1 != chars2 {
        return false;
    }
    
    var n := |s1|;
    var i := 1;
    while i < n
    {
        var s1Left := s1[..i];
        var s1Right := s1[i..];
        var s2Left := s2[..i];
        var s2Right := s2[i..];
        var s2LeftAlt := s2[n-i..];
        var s2RightAlt := s2[..n-i];
        
        var case1 := isScramble(s1Left, s2Left);
        if case1 {
            var case2 := isScramble(s1Right, s2Right);
            if case2 {
                return true;
            }
        }
        
        var case3 := isScramble(s1Left, s2LeftAlt);
        if case3 {
            var case4 := isScramble(s1Right, s2RightAlt);
            if case4 {
                return true;
            }
        }
        
        i := i + 1;
    }
    
    return false;
}

method Main()
{
    var result;

    result := isScramble(s1:="a", s2:="a");
    if result != True
    {
        print("Test failed: with input (\"s1\":=\"a\", \"s2\":=\"a\") got: ");
        print(result);
        print(" instead of \"True\")\n");
    }

    result := isScramble(s1:="great", s2:="rgeat");
    if result != True
    {
        print("Test failed: with input (\"s1\":=\"great\", \"s2\":=\"rgeat\") got: ");
        print(result);
        print(" instead of \"True\")\n");
    }

    result := isScramble(s1:="abcde", s2:="caebd");
    if result != False
    {
        print("Test failed: with input (\"s1\":=\"abcde\", \"s2\":=\"caebd\") got: ");
        print(result);
        print(" instead of \"False\")\n");
    }

    result := isScramble(s1:="abc", s2:="bca");
    if result != True
    {
        print("Test failed: with input (\"s1\":=\"abc\", \"s2\":=\"bca\") got: ");
        print(result);
        print(" instead of \"True\")\n");
    }

    result := isScramble(s1:="abcdefghijklmnopqrstuvwxyz", s2:="zyxwvutsrqponmlkjihgfedcba");
    if result != True
    {
        print("Test failed: with input (\"s1\":=\"abcdefghijklmnopqrstuvwxyz\", \"s2\":=\"zyxwvutsrqponmlkjihgfedcba\") got: ");
        print(result);
        print(" instead of \"True\")\n");
    }

    result := isScramble(s1:="aaaaaaaaaa", s2:="aaaaaaaaaa");
    if result != True
    {
        print("Test failed: with input (\"s1\":=\"aaaaaaaaaa\", \"s2\":=\"aaaaaaaaaa\") got: ");
        print(result);
        print(" instead of \"True\")\n");
    }

    result := isScramble(s1:="abab", s2:="baba");
    if result != True
    {
        print("Test failed: with input (\"s1\":=\"abab\", \"s2\":=\"baba\") got: ");
        print(result);
        print(" instead of \"True\")\n");
    }

    result := isScramble(s1:="hello", s2:="olleh");
    if result != True
    {
        print("Test failed: with input (\"s1\":=\"hello\", \"s2\":=\"olleh\") got: ");
        print(result);
        print(" instead of \"True\")\n");
    }

}
