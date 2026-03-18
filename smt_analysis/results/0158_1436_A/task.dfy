// --- Specification: permutation enumeration via factoradic decoding ---

ghost function Factorial(n: nat): nat
  decreases n
{
  if n == 0 then 1 else n * Factorial(n - 1)
}

ghost function Iota(n: nat): seq<int>
  decreases n
{
  if n == 0 then [] else Iota(n - 1) + [n - 1]
}

ghost function RemoveAt(s: seq<int>, idx: nat): seq<int>
  requires idx < |s|
{
  s[..idx] + s[idx + 1..]
}

ghost function DecodePerm(k: nat, available: seq<int>): seq<int>
  decreases |available|
{
  if |available| == 0 then []
  else
    var idx := k % |available|;
    [available[idx]] + DecodePerm(k / |available|, RemoveAt(available, idx))
}

ghost function PermFromIndex(k: nat, n: nat): seq<int>
{
  DecodePerm(k, Iota(n))
}

ghost function ApplyPerm(a: seq<int>, perm: seq<int>): seq<int>
  requires forall i | 0 <= i < |perm| :: 0 <= perm[i] < |a|
  decreases |perm|
{
  if |perm| == 0 then []
  else [a[perm[0]]] + ApplyPerm(a, perm[1..])
}

// --- Specification: the double sum from the problem statement ---
// Computes sum_{k=0}^{|a|-1} a[k] / (pos + k), where pos is the
// 1-based absolute position of a[0] in the original array.

ghost function WeightedSum(a: seq<int>, pos: nat): real
  requires pos >= 1
  decreases |a|
{
  if |a| == 0 then 0.0
  else (a[0] as real) / (pos as real) + WeightedSum(a[1..], pos + 1)
}

// Computes sum_{i=1}^{n} sum_{j=i}^{n} b_j / j   (1-indexed per problem)
// = sum_{i=0}^{|a|-1} sum_{j=i}^{|a|-1} a[j]/(j+1)   (0-indexed)

ghost function DoubleSumFrom(a: seq<int>, pos: nat): real
  requires pos >= 1
  decreases |a|
{
  if |a| == 0 then 0.0
  else WeightedSum(a, pos) + DoubleSumFrom(a[1..], pos + 1)
}

ghost function DoubleSum(a: seq<int>): real
{
  DoubleSumFrom(a, 1)
}

// --- Specification: the reorder predicate ---

ghost predicate HasReorderingAt(a: seq<int>, k: nat, m: int)
{
  k < Factorial(|a|) &&
  var perm := PermFromIndex(k, |a|);
  |perm| == |a| &&
  (forall i | 0 <= i < |perm| :: 0 <= perm[i] < |a|) &&
  DoubleSum(ApplyPerm(a, perm)) == m as real
}

// There exists some permutation of a whose double sum equals m.
ghost predicate CanReorderToSum(a: seq<int>, m: int)
{
  exists k: nat :: HasReorderingAt(a, k, m)
}

// --- Method with specification ---

method Reorder(a: seq<int>, m: int) returns (result: bool)
  ensures result == CanReorderToSum(a, m)
{
  var s := 0;
  for i := 0 to |a| {
    s := s + a[i];
  }
  result := m == s;
}