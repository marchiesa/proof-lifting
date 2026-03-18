// The target string we want to obtain by removing at most one contiguous substring.
const TARGET: string := "2020"

// Models the problem directly: can we choose cut points 0 <= i <= j <= |s|
// such that removing the substring s[i..j] yields "2020"?
// s[..i] + s[j..] is what remains after the removal.
// When i == j, nothing is removed (the zero-operation case).
ghost predicate CanObtain2020(s: string)
{
  exists i | 0 <= i <= |s| ::
    exists j | i <= j <= |s| ::
      s[..i] + s[j..] == TARGET
}

method LastYearSubstring(s: string) returns (result: bool)
  ensures result == CanObtain2020(s)
{
  var n := |s|;
  if n < 4 {
    result := false;
    return;
  }
  var c1 := s[0..4] == "2020";
  var c2 := s[n-4..n] == "2020";
  var c3 := s[0] == '2' && s[n-3..n] == "020";
  var c4 := s[0..2] == "20" && s[n-2..n] == "20";
  var c5 := s[0..3] == "202" && s[n-1] == '0';
  result := c1 || c2 || c3 || c4 || c5;
}