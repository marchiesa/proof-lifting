// Task: Add loop invariants to make this program verify.
// Do NOT modify the code logic, method signature, or specification.

function Sum(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + Sum(s[1..])
}

method SumArray(s: seq<int>) returns (r: int)
  ensures r == Sum(s)
{
  r := 0;
  var i := 0;
  while i < |s|
  {
    r := r + s[i];
    i := i + 1;
  }
}
