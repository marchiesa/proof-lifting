// Trapping Rain Water
// Task: Add loop invariants so that Dafny can verify this program.

function Max(a: int, b: int): int { if a >= b then a else b }
function Min(a: int, b: int): int { if a <= b then a else b }

function PrefixMax(a: seq<int>, n: int): int
  requires 0 < n <= |a|
  decreases n
{
  if n == 1 then a[0]
  else Max(PrefixMax(a, n - 1), a[n - 1])
}

function SuffixMax(a: seq<int>, n: int): int
  requires 0 <= n < |a|
  decreases |a| - n
{
  if n == |a| - 1 then a[n]
  else Max(a[n], SuffixMax(a, n + 1))
}

// Compute prefix max array
method ComputePrefixMax(a: seq<int>) returns (pm: seq<int>)
  requires |a| > 0
  ensures |pm| == |a|
  ensures pm[0] == a[0]
  ensures forall i :: 0 < i < |a| ==> pm[i] == Max(pm[i-1], a[i])
  ensures forall i :: 0 < i < |a| ==> pm[i] == PrefixMax(a, i + 1)
{
  pm := [a[0]];
  var i := 1;
  while i < |a|
  {
    pm := pm + [Max(pm[i-1], a[i])];
    i := i + 1;
  }
}

// Compute suffix max array
method ComputeSuffixMax(a: seq<int>) returns (sm: seq<int>)
  requires |a| > 0
  ensures |sm| == |a|
  ensures sm[|a|-1] == a[|a|-1]
  ensures forall i :: 0 <= i < |a| - 1 ==> sm[i] == Max(a[i], sm[i+1])
  ensures forall i :: 0 <= i < |a| - 1 ==> sm[i] == SuffixMax(a, i)
{
  sm := seq(|a|, k => 0);
  sm := sm[|a|-1 := a[|a|-1]];
  var i := |a| - 2;
  while i >= 0
  {
    sm := sm[i := Max(a[i], sm[i+1])];
    i := i - 1;
  }
}

method TrapRainWater(a: seq<int>) returns (water: int)
  requires |a| >= 2
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures water >= 0
{
  if |a| <= 2 {
    return 0;
  }
  var pm := ComputePrefixMax(a);
  var sm := ComputeSuffixMax(a);
  water := 0;
  var i := 1;
  while i < |a| - 1
  {
    var level := Min(pm[i-1], sm[i+1]);
    if level > a[i] {
      water := water + level - a[i];
    }
    i := i + 1;
  }
}
