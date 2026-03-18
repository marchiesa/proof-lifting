ghost predicate Feasible(n: int, k: int, l: int, c: int, d: int, p: int, nl: int, np: int, t: int)
{
  t >= 0 &&
  n * t * nl <= k * l &&
  n * t <= c * d &&
  n * t * np <= p
}

method SoftDrinking(n: int, k: int, l: int, c: int, d: int, p: int, nl: int, np: int) returns (toasts: int)
  requires n >= 1
  requires k >= 0 && l >= 0
  requires c >= 0 && d >= 0
  requires p >= 0
  requires nl >= 1
  requires np >= 1
  ensures Feasible(n, k, l, c, d, p, nl, np, toasts)
  ensures !Feasible(n, k, l, c, d, p, nl, np, toasts + 1)
{
  var totalDrink := k * l;
  var drinksPossible := totalDrink / nl;
  var limePieces := c * d;
  if limePieces < drinksPossible {
    drinksPossible := limePieces;
  }
  var saltServings := p / np;
  if saltServings < drinksPossible {
    drinksPossible := saltServings;
  }
  toasts := drinksPossible / n;
}