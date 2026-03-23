// Pattern: Find first element >= threshold (lower bound search)
// Source: various config/threshold lookup utilities
// Real-world: rate limiting thresholds, pricing tiers, log level filtering

method FindFirstGE(a: seq<int>, threshold: int) returns (idx: int)
  requires forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]  // sorted
  ensures 0 <= idx <= |a|
  ensures forall i :: 0 <= i < idx ==> a[i] < threshold
  ensures idx < |a| ==> a[idx] >= threshold
{
  idx := 0;
  while idx < |a| && a[idx] < threshold
    invariant 0 <= idx <= |a|
    invariant forall i :: 0 <= i < idx ==> a[i] < threshold
  {
    idx := idx + 1;
  }
}
