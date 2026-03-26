predicate WellFormedPattern(p: string)
{
  // Every '*' must have exactly one preceding character that is not '*'
  (forall k:int :: 
       0 <= k < |p| ==>
         (p[k] != '*') || (0 < k && p[k-1] != '*'))
}

function CharMatches(ch: char, pat: char): bool
{
  pat == '.' || ch == pat
}

function MatchesRec(s: string, p: string, sIdx: int, pIdx: int): bool
  requires 0 <= sIdx <= |s|
  requires 0 <= pIdx <= |p|
  decreases |s| - sIdx, |p| - pIdx
{
  if pIdx == |p| then
    sIdx == |s|
  else
    var firstMatch := sIdx < |s| && CharMatches(s[sIdx], p[pIdx]); 
    if pIdx + 1 < |p| && p[pIdx + 1] == '*' then
      // Either skip the 'x*' pattern or consume one matching character
      MatchesRec(s, p, sIdx, pIdx + 2) || (firstMatch && MatchesRec(s, p, sIdx + 1, pIdx))
    else
      // Simple character (or '.') match
      firstMatch && MatchesRec(s, p, sIdx + 1, pIdx + 1)
}

function Matches(s: string, p: string): bool
{
  MatchesRec(s, p, 0, 0)
}

predicate IsMatchPost(s: string, p: string, result: bool)
{
  result == Matches(s, p)
}

// method to be verified
method IsMatch(s: string, p: string) returns (result: bool)
  requires |s| > 0
  requires |p| > 0
  requires WellFormedPattern(p)
  ensures  IsMatchPost(s, p, result)
{
    var m, n := |s|, |p|;
    var dp := new bool[m + 1, n + 1];
    
    // Initialize dp[0,0]
    dp[0,0] := true;
    
    // Fill first row
    var j := 1;
    while j < n + 1
    {
        if j >= 2 && p[j-1] == '*' && dp[0,j-2]
        {
            dp[0,j] := true;
        }
        j := j + 1;
    }
    
    // Fill dp table
    var i := 1;
    while i < m + 1
    {
        j := 1;
        while j < n + 1
        {
            if p[j-1] == s[i-1] || p[j-1] == '.'
            {
                dp[i,j] := dp[i-1,j-1];
            }
            else if p[j-1] == '*'
            {
                dp[i,j] := dp[i,j-2] || (dp[i-1,j] && (s[i-1] == p[j-2] || p[j-2] == '.'));
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := dp[m,n];
}

method Main()
{
    var result;

    result := IsMatch(s:="aa", p:="a");
    if result != False
    {
        print("Test failed: with input (\"s\":=\"aa\", \"p\":=\"a\") got: ");
        print(result);
        print(" instead of \"False\")\n");
    }

    result := IsMatch(s:="aa", p:="a*");
    if result != True
    {
        print("Test failed: with input (\"s\":=\"aa\", \"p\":=\"a*\") got: ");
        print(result);
        print(" instead of \"True\")\n");
    }

    result := IsMatch(s:="ab", p:=".*");
    if result != True
    {
        print("Test failed: with input (\"s\":=\"ab\", \"p\":=\".*\") got: ");
        print(result);
        print(" instead of \"True\")\n");
    }

    result := IsMatch(s:="aab", p:="c*a*b");
    if result != True
    {
        print("Test failed: with input (\"s\":=\"aab\", \"p\":=\"c*a*b\") got: ");
        print(result);
        print(" instead of \"True\")\n");
    }

    result := IsMatch(s:="mississippi", p:="mis*is*p*.");
    if result != False
    {
        print("Test failed: with input (\"s\":=\"mississippi\", \"p\":=\"mis*is*p*.\") got: ");
        print(result);
        print(" instead of \"False\")\n");
    }

    result := IsMatch(s:="aaa", p:="a*a");
    if result != True
    {
        print("Test failed: with input (\"s\":=\"aaa\", \"p\":=\"a*a\") got: ");
        print(result);
        print(" instead of \"True\")\n");
    }

    result := IsMatch(s:="aaa", p:="ab*a*c*a");
    if result != True
    {
        print("Test failed: with input (\"s\":=\"aaa\", \"p\":=\"ab*a*c*a\") got: ");
        print(result);
        print(" instead of \"True\")\n");
    }

    result := IsMatch(s:="a", p:=".*");
    if result != True
    {
        print("Test failed: with input (\"s\":=\"a\", \"p\":=\".*\") got: ");
        print(result);
        print(" instead of \"True\")\n");
    }

    result := IsMatch(s:="abcde", p:=".*");
    if result != True
    {
        print("Test failed: with input (\"s\":=\"abcde\", \"p\":=\".*\") got: ");
        print(result);
        print(" instead of \"True\")\n");
    }

}
