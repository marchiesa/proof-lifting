// Recursive function for sum
function Sum(s: seq<int>): int
{
  if |s| == 0 then 0
  else Sum(s[..|s|-1]) + s[|s|-1]
}

// Iterative method that computes the sum
method ComputeSum2(s: seq<int>) returns (sum: int)
  ensures sum == Sum(s)
{
  sum := 0;
  var i := 0;

  while i < |s|
    invariant 0 <= i <= |s|
    invariant sum == Sum(s[..i])
  {
    assert s[..i+1][..i] == s[..i];  // Help Z3
    sum := sum + s[i];
    i := i + 1;
  }

  assert s[..|s|] == s;  // Help Z3
}
