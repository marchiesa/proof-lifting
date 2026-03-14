// House Robber (DP, max non-adjacent sum)
// Task: Add loop invariants so that Dafny can verify this program.

function Max(a: int, b: int): int { if a >= b then a else b }

// Optimal robbery for houses 0..n-1 with no two adjacent
function Rob(a: seq<int>, n: int): int
  requires 0 <= n <= |a|
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  decreases n
{
  if n == 0 then 0
  else if n == 1 then a[0]
  else Max(Rob(a, n - 1), Rob(a, n - 2) + a[n - 1])
}

method HouseRobber(a: seq<int>) returns (result: int)
  requires |a| > 0
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures result == Rob(a, |a|)
{
  if |a| == 1 {
    return a[0];
  }
  var prev2 := 0;
  var prev1 := a[0];
  var i := 2;
  while i <= |a|
  {
    var curr := Max(prev1, prev2 + a[i - 1]);
    prev2 := prev1;
    prev1 := curr;
    i := i + 1;
  }
  result := prev1;
}
