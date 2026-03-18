// --- Specification: models the problem's structure directly ---

// d is a positive divisor of n
ghost predicate Divides(d: int, n: int)
{
  d > 0 && n % d == 0
}

// g is the greatest common divisor of a and b
ghost predicate IsGcd(g: int, a: int, b: int)
{
  g > 0 && a > 0 && b > 0 &&
  Divides(g, a) && Divides(g, b) &&
  forall d | 1 <= d <= a :: (Divides(d, a) && Divides(d, b)) ==> d <= g
}

// Pouring e liters of essence and w liters of water yields exactly k% essence
ghost predicate IsValidPotion(e: int, w: int, k: int)
{
  e >= 0 && w >= 0 && e + w > 0 && e * 100 == k * (e + w)
}

// There exists a way to pour exactly 'steps' total liters achieving k% essence
ghost predicate AchievableInSteps(steps: int, k: int)
{
  steps >= 0 &&
  exists e | 0 <= e <= steps :: IsValidPotion(e, steps - e, k)
}

// 'steps' is the minimum number of pours to achieve exactly k% essence
ghost predicate IsMinSteps(steps: int, k: int)
{
  steps >= 1 &&
  AchievableInSteps(steps, k) &&
  forall s | 1 <= s < steps :: !AchievableInSteps(s, k)
}

// --- Methods with specifications ---

method Gcd(a: int, b: int) returns (r: int)
  requires a > 0 && b > 0
  ensures IsGcd(r, a, b)
{
  var x := a;
  var y := b;
  while y != 0
  {
    var tmp := y;
    y := x % y;
    x := tmp;
  }
  r := x;
}

method PotionMaking(k: int) returns (steps: int)
  requires 1 <= k <= 100
  ensures IsMinSteps(steps, k)
{
  var g := Gcd(k, 100);
  steps := 100 / g;
}