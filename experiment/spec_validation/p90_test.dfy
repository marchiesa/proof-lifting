predicate ValidDigitString(s: string)
  reads {}
{
  forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function decodeCount(s: string): nat
  decreases |s|
{
  if |s| == 0 then 1
  else if s[0] == '0' then 0
  else
    decodeCount(s[1..]) +
    (if |s| >= 2 &&
        ((s[0] == '1') ||
         (s[0] == '2' && '0' <= s[1] <= '6'))
     then decodeCount(s[2..]) else 0)
}

predicate numDecodingsPost(s: string, result: int)
  reads {}
{
  result == decodeCount(s)
}

// method to be verified
method numDecodings(s: string) returns (result: int)
  requires |s| >= 1 && |s| <= 100
  requires ValidDigitString(s)
  ensures numDecodingsPost(s, result)
{
    var n := |s|;
    var dp := new int[n + 1];
    
    // Initialize base cases
    dp[0] := 1;
    if n > 0 {
        if s[0] != '0' {
            dp[1] := 1;
        } else {
            dp[1] := 0;
        }
    }
    
    // Fill dp array
    var i := 2;
    while i <= n {
        var oneDigit := (s[i-1] as int) - ('0' as int);
        var twoDigits := ((s[i-2] as int) - ('0' as int)) * 10 + ((s[i-1] as int) - ('0' as int));
        
        if oneDigit >= 1 {
            dp[i] := dp[i] + dp[i-1];
        }
        if twoDigits >= 10 && twoDigits <= 26 {
            dp[i] := dp[i] + dp[i-2];
        }
        
        i := i + 1;
    }
    
    result := dp[n];
}

method Main()
{
    var result;

    result := numDecodings(s:="12");
    if result != 2
    {
        print("Test failed: with input (\"s\":=12) got: ");
        print(result);
        print(" instead of \"2\")\n");
    }

    result := numDecodings(s:="226");
    if result != 3
    {
        print("Test failed: with input (\"s\":=226) got: ");
        print(result);
        print(" instead of \"3\")\n");
    }

    result := numDecodings(s:="06");
    if result != 0
    {
        print("Test failed: with input (\"s\":=6) got: ");
        print(result);
        print(" instead of \"0\")\n");
    }

    result := numDecodings(s:="1");
    if result != 1
    {
        print("Test failed: with input (\"s\":=1) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := numDecodings(s:="2");
    if result != 1
    {
        print("Test failed: with input (\"s\":=2) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := numDecodings(s:="10");
    if result != 1
    {
        print("Test failed: with input (\"s\":=10) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := numDecodings(s:="27");
    if result != 1
    {
        print("Test failed: with input (\"s\":=27) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

    result := numDecodings(s:="100");
    if result != 0
    {
        print("Test failed: with input (\"s\":=100) got: ");
        print(result);
        print(" instead of \"0\")\n");
    }

    result := numDecodings(s:="111");
    if result != 3
    {
        print("Test failed: with input (\"s\":=111) got: ");
        print(result);
        print(" instead of \"3\")\n");
    }

    result := numDecodings(s:="26");
    if result != 2
    {
        print("Test failed: with input (\"s\":=26) got: ");
        print(result);
        print(" instead of \"2\")\n");
    }

    result := numDecodings(s:="0");
    if result != 0
    {
        print("Test failed: with input (\"s\":=0) got: ");
        print(result);
        print(" instead of \"0\")\n");
    }

    result := numDecodings(s:="1111");
    if result != 5
    {
        print("Test failed: with input (\"s\":=1111) got: ");
        print(result);
        print(" instead of \"5\")\n");
    }

    result := numDecodings(s:="2611");
    if result != 4
    {
        print("Test failed: with input (\"s\":=2611) got: ");
        print(result);
        print(" instead of \"4\")\n");
    }

    result := numDecodings(s:="9999");
    if result != 1
    {
        print("Test failed: with input (\"s\":=9999) got: ");
        print(result);
        print(" instead of \"1\")\n");
    }

}
