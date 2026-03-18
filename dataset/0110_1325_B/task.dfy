// Concatenate n copies of sequence a
ghost function Repeat(a: seq<int>, n: nat): seq<int>
  decreases n
{
  if n == 0 then [] else a + Repeat(a, n - 1)
}

// Does b contain a strictly increasing subsequence of length k
// where every element is strictly greater than minVal?
ghost predicate HasIncSubseqFrom(b: seq<int>, k: nat, minVal: int)
  decreases |b|
{
  if k == 0 then true
  else if |b| < k then false
  else
    (b[0] > minVal && HasIncSubseqFrom(b[1..], k - 1, b[0]))
    ||
    HasIncSubseqFrom(b[1..], k, minVal)
}

// Does b contain a strictly increasing subsequence of length k?
ghost predicate HasIncSubseq(b: seq<int>, k: nat)
  decreases |b|
{
  if k == 0 then true
  else if |b| < k then false
  else
    HasIncSubseqFrom(b[1..], k - 1, b[0])
    ||
    HasIncSubseq(b[1..], k)
}

// Largest k in [0..maxK] such that b has an increasing subsequence of length k
ghost function LISSearch(b: seq<int>, maxK: nat): nat
  decreases maxK
{
  if maxK == 0 then 0
  else if HasIncSubseq(b, maxK) then maxK
  else LISSearch(b, maxK - 1)
}

// Length of the longest strictly increasing subsequence of b
ghost function LISLength(b: seq<int>): nat
{
  LISSearch(b, |b|)
}

method CopyCopyCopyCopyCopy(a: seq<int>) returns (result: int)
  ensures result == LISLength(Repeat(a, |a|))
{
  var n := |a|;
  if n == 0 {
    return 0;
  }
  var arr := new int[n];
  var i := 0;
  while i < n
  {
    arr[i] := a[i];
    i := i + 1;
  }
  // Insertion sort
  var j := 1;
  while j < n
  {
    var key := arr[j];
    var k := j - 1;
    while k >= 0 && arr[k] > key
    {
      arr[k + 1] := arr[k];
      k := k - 1;
    }
    arr[k + 1] := key;
    j := j + 1;
  }
  // Count distinct by subtracting consecutive duplicates
  var ans := n;
  var m := 0;
  while m < n - 1
  {
    if arr[m + 1] == arr[m] {
      ans := ans - 1;
    }
    m := m + 1;
  }
  return ans;
}