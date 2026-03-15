// Traveling Salesman Problem (Bitmask DP) -- Reference solution with invariants

function Min(a: int, b: int): int { if a <= b then a else b }

method GetBit(mask: int, pos: int) returns (isSet: bool)
  requires mask >= 0 && pos >= 0
{
  var m := mask;
  var b := 0;
  while b < pos
    invariant 0 <= b <= pos
    invariant m >= 0
    decreases pos - b
  {
    m := m / 2;
    b := b + 1;
  }
  isSet := (m % 2) == 1;
}

method Pow2(k: int) returns (r: int)
  requires k >= 0
  ensures r >= 1
{
  r := 1;
  var b := 0;
  while b < k
    invariant 0 <= b <= k
    invariant r >= 1
    decreases k - b
  {
    r := r * 2;
    b := b + 1;
  }
}

method TspBitmask(dist: array2<int>, n: int) returns (result: int)
  requires n >= 2
  requires dist.Length0 == n && dist.Length1 == n
  requires forall i, j :: 0 <= i < n && 0 <= j < n ==> dist[i, j] >= 0
  ensures result >= 0
{
  var numMasks := 1;
  var p := 0;
  while p < n
    invariant 0 <= p <= n
    invariant numMasks >= 1
    invariant p >= 1 ==> numMasks >= 2
    decreases n - p
  {
    numMasks := numMasks * 2;
    p := p + 1;
  }

  var INF := 1000000000;
  var dp := new int[numMasks * n];

  var idx := 0;
  while idx < numMasks * n
    invariant 0 <= idx <= numMasks * n
    invariant forall k :: 0 <= k < idx ==> dp[k] >= 0
    decreases numMasks * n - idx
  {
    dp[idx] := INF;
    idx := idx + 1;
  }

  assert numMasks >= 2;
  assert n >= 2;
  assert n < numMasks * n;
  dp[1 * n + 0] := 0;

  var mask := 1;
  while mask < numMasks
    invariant 1 <= mask <= numMasks
    invariant forall k :: 0 <= k < numMasks * n ==> dp[k] >= 0
    decreases numMasks - mask
  {
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant forall k :: 0 <= k < numMasks * n ==> dp[k] >= 0
      decreases n - i
    {
      if dp[mask * n + i] < INF {
        var j := 0;
        while j < n
          invariant 0 <= j <= n
          invariant forall k :: 0 <= k < numMasks * n ==> dp[k] >= 0
          decreases n - j
        {
          var isSet := GetBit(mask, j);
          if !isSet {
            var bit := Pow2(j);
            var newMask := mask + bit;
            if newMask < numMasks {
              var newCost := dp[mask * n + i] + dist[i, j];
              if newCost < dp[newMask * n + j] {
                dp[newMask * n + j] := newCost;
              }
            }
          }
          j := j + 1;
        }
      }
      i := i + 1;
    }
    mask := mask + 1;
  }

  var fullMask := numMasks - 1;
  result := INF;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result >= 0
    decreases n - i
  {
    var cost := dp[fullMask * n + i] + dist[i, 0];
    if cost < result {
      result := cost;
    }
    i := i + 1;
  }
  if result >= INF { result := 0; }
}
