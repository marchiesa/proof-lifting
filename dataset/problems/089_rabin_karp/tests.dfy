// Rabin-Karp -- Test cases

method {:axiom} RabinKarp(text: seq<int>, pattern: seq<int>, base: int, modulus: int) returns (positions: seq<int>)
  requires |pattern| > 0
  requires |pattern| <= |text|
  requires base > 0 && modulus > 1
  ensures forall k :: 0 <= k < |positions| ==> 0 <= positions[k] <= |text| - |pattern|

method TestSimple()
{
  var p := RabinKarp([1, 2, 3, 2, 3], [2, 3], 31, 1000000007);
  assert forall k :: 0 <= k < |p| ==> 0 <= p[k] <= 3;
}
