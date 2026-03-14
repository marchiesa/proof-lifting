// Fast Exponentiation (Exponentiation by Squaring) -- Reference solution with invariants

function Power(base: int, exp: nat): int
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
}

lemma PowerMultiplicative(base: int, e1: nat, e2: nat)
  ensures Power(base, e1 + e2) == Power(base, e1) * Power(base, e2)
{
  if e1 == 0 {
  } else {
    PowerMultiplicative(base, e1 - 1, e2);
  }
}

lemma PowerSquare(base: int, exp: nat)
  requires exp > 0
  ensures Power(base * base, exp / 2) * (if exp % 2 == 1 then base else 1) == Power(base, exp)
{
  if exp == 1 {
    assert Power(base * base, 0) == 1;
    assert Power(base, 1) == base * Power(base, 0) == base;
  } else if exp % 2 == 0 {
    var half := exp / 2;
    assert exp == 2 * half;
    PowerSquareEven(base, half);
  } else {
    var half := exp / 2;
    assert exp == 2 * half + 1;
    PowerSquareOdd(base, half);
  }
}

lemma PowerSquareEven(base: int, half: nat)
  requires half > 0
  ensures Power(base * base, half) == Power(base, 2 * half)
{
  if half == 1 {
    calc {
      Power(base * base, 1);
      == (base * base) * Power(base * base, 0);
      == base * base;
      == base * (base * Power(base, 0));
      == base * Power(base, 1);
      == Power(base, 2);
    }
  } else {
    PowerSquareEven(base, half - 1);
    calc {
      Power(base * base, half);
      == (base * base) * Power(base * base, half - 1);
      == (base * base) * Power(base, 2 * (half - 1));
      == (base * base) * Power(base, 2 * half - 2);
    }
    calc {
      Power(base, 2 * half);
      == base * Power(base, 2 * half - 1);
      == base * (base * Power(base, 2 * half - 2));
      == (base * base) * Power(base, 2 * half - 2);
    }
  }
}

lemma PowerSquareOdd(base: int, half: nat)
  ensures Power(base * base, half) * base == Power(base, 2 * half + 1)
{
  if half == 0 {
    assert Power(base * base, 0) * base == base;
    assert Power(base, 1) == base * Power(base, 0) == base;
  } else {
    PowerSquareOdd(base, half - 1);
    PowerSquareEven(base, half);
    calc {
      Power(base * base, half) * base;
      == Power(base, 2 * half) * base;
    }
    PowerMultiplicative(base, 2 * half, 1);
    assert Power(base, 2 * half) * base == Power(base, 2 * half) * Power(base, 1)
      == Power(base, 2 * half + 1);
  }
}

method FastPow(base: int, exp: nat) returns (result: int)
  ensures result == Power(base, exp)
{
  result := 1;
  var b := base;
  var e := exp;
  while e > 0
    invariant e >= 0
    invariant result * Power(b, e) == Power(base, exp)
    decreases e
  {
    if e % 2 == 1 {
      PowerSquare(b, e);
      result := result * b;
      e := e - 1;
    } else {
      // e is even
    }
    if e > 0 {
      PowerSquareEven(b, e / 2);
      b := b * b;
      e := e / 2;
    }
  }
}
