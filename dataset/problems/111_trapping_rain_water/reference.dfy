// Trapping Rain Water -- Reference solution with invariants

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
    invariant 1 <= i <= |a|
    invariant |pm| == i
    invariant pm[0] == a[0]
    invariant forall k :: 0 < k < i ==> pm[k] == Max(pm[k-1], a[k])
    invariant forall k :: 0 < k < i ==> pm[k] == PrefixMax(a, k + 1)
    decreases |a| - i
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
    invariant -1 <= i <= |a| - 2
    invariant |sm| == |a|
    invariant sm[|a|-1] == a[|a|-1]
    invariant forall k :: i < k < |a| - 1 ==> sm[k] == Max(a[k], sm[k+1])
    invariant forall k :: i < k < |a| - 1 ==> sm[k] == SuffixMax(a, k)
    invariant i < |a| - 2 ==> sm[i+1] == SuffixMax(a, i+1)
    decreases i + 1
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
    invariant 1 <= i <= |a| - 1
    invariant water >= 0
    decreases |a| - 1 - i
  {
    var level := Min(pm[i-1], sm[i+1]);
    if level > a[i] {
      water := water + level - a[i];
    }
    i := i + 1;
  }
}
