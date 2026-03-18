// The frog's position after k jumps, defined directly from the problem statement:
//   Start at position 0. Before each jump, count prior jumps:
//     even count  → jump right by a  (position += a)
//     odd  count  → jump left  by b  (position -= b)
ghost function FrogPosition(a: int, b: int, k: nat): real
  decreases k
{
  if k == 0 then 0.0
  else if (k - 1) % 2 == 0 then
    FrogPosition(a, b, k - 1) + a as real
  else
    FrogPosition(a, b, k - 1) - b as real
}

method FrogJumping(queries: seq<(int, int, int)>) returns (results: seq<real>)
  requires forall i | 0 <= i < |queries| :: queries[i].2 >= 0
  ensures |results| == |queries|
  ensures forall i | 0 <= i < |queries| ::
    results[i] == FrogPosition(queries[i].0, queries[i].1, queries[i].2)
{
  results := [];
  var i := 0;
  while i < |queries|
  {
    var (a, b, k) := queries[i];
    var f: real := k as real / 2.0;
    var ans: real := a as real * f - b as real * f;
    if k % 2 == 1 {
      ans := ans + a as real;
    }
    results := results + [ans];
    i := i + 1;
  }
}