// Longest Bitonic Subsequence (LIS + LDS)
// Task: Add loop invariants so that Dafny can verify this program.

function Max(a: int, b: int): int { if a >= b then a else b }

// LIS ending at index i
function LISAt(a: seq<int>, i: int): int
  requires 0 <= i < |a|
  decreases i
{
  if i == 0 then 1
  else
    var prev := LISAtMax(a, i, 0);
    prev + 1
}

function LISAtMax(a: seq<int>, i: int, j: int): int
  requires 0 <= j <= i < |a|
  decreases i - j
{
  if j == i then 0
  else
    var rest := LISAtMax(a, i, j + 1);
    if a[j] < a[i] then Max(LISAt(a, j), rest)
    else rest
}

// LDS starting at index i (longest decreasing subsequence)
function LDSAt(a: seq<int>, i: int): int
  requires 0 <= i < |a|
  decreases |a| - i - 1
{
  if i == |a| - 1 then 1
  else
    var next := LDSAtMax(a, i, i + 1);
    next + 1
}

function LDSAtMax(a: seq<int>, i: int, j: int): int
  requires 0 <= i < j <= |a|
  decreases |a| - j
{
  if j == |a| then 0
  else
    var rest := LDSAtMax(a, i, j + 1);
    if a[j] < a[i] then Max(LDSAt(a, j), rest)
    else rest
}

method LongestBitonicSubseq(a: seq<int>) returns (result: int)
  requires |a| > 0
  ensures result >= 1
{
  // Compute LIS for each position
  var lis := new int[|a|];
  var i := 0;
  while i < |a|
  {
    lis[i] := 1;
    var j := 0;
    while j < i
    {
      if a[j] < a[i] && lis[j] + 1 > lis[i] {
        lis[i] := lis[j] + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }

  // Compute LDS for each position
  var lds := new int[|a|];
  i := |a| - 1;
  while i >= 0
  {
    lds[i] := 1;
    var j := |a| - 1;
    while j > i
    {
      if a[j] < a[i] && lds[j] + 1 > lds[i] {
        lds[i] := lds[j] + 1;
      }
      j := j - 1;
    }
    i := i - 1;
  }

  // Result is max(lis[i] + lds[i] - 1) for all i
  result := 1;
  i := 0;
  while i < |a|
  {
    result := Max(result, lis[i] + lds[i] - 1);
    i := i + 1;
  }
}
