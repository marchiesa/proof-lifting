// --- Specification: models the problem statement directly ---

ghost function Gcd(a: int, b: int): int
  requires a > 0 && b > 0
  decreases a + b
{
  if a == b then a
  else if a > b then Gcd(a - b, b)
  else Gcd(a, b - a)
}

ghost predicate WouldIndulge(a: int, b: int)
  requires a > 0 && b > 0
{
  Gcd(a, b) == 1 || a % b == 0 || b % a == 0
}

ghost predicate ValidSeating(chairs: seq<int>, n: int)
{
  // Exactly n chairs selected
  |chairs| == n
  // Each chair in range [1, 4n]
  && (forall i | 0 <= i < n :: 1 <= chairs[i] <= 4 * n)
  // All chairs are distinct (two kids can't sit on the same chair)
  && (forall i, j | 0 <= i < n && 0 <= j < n && i != j :: chairs[i] != chairs[j])
  // No pair of kids would indulge
  && (forall i, j | 0 <= i < n && 0 <= j < n && i < j :: !WouldIndulge(chairs[i], chairs[j]))
}

// --- Implementation (body unchanged) ---

method KidsSeating(n: int) returns (chairs: seq<int>)
  requires n >= 0
  ensures ValidSeating(chairs, n)
{
  chairs := [];
  var i := 0;
  while i < n
  {
    chairs := chairs + [2 * i + 2 * n + 2];
    i := i + 1;
  }
}

method ExpectedChairs(n: int) returns (expected: seq<int>)
{
  expected := [];
  var start := 2 * (n + 1);
  var i := 0;
  while i < n
  {
    expected := expected + [start + 2 * i];
    i := i + 1;
  }
}