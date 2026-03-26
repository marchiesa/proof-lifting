method M(s: seq<int>) requires |s| > 2
{
  var lo := 0;
  var hi := |s| - 1;
  var mid := (lo + hi) / 2;
  var left := mid - lo;
  assert left == mid - lo;
  assert left >= 0;
}
