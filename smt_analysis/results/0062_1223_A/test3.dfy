ghost predicate IsValidCME(a: int, b: int, c: int)
{
  a >= 1 && b >= 1 && c >= 1 && a + b == c
}

ghost predicate CanFormCMEWithMatches(total: int)
{
  exists a | 1 <= a <= total / 2 - 1 ::
    var b := total / 2 - a;
    IsValidCME(a, b, a + b) && a + b + (a + b) == total
}

lemma CannotFormOdd(total: int)
  requires total % 2 == 1
  ensures !CanFormCMEWithMatches(total)
{
  forall a | 1 <= a <= total / 2 - 1
    ensures !(var b := total / 2 - a; IsValidCME(a, b, a + b) && a + b + (a + b) == total)
  {
    assert total / 2 + total / 2 == total - 1;
  }
}

lemma CannotFormSmall(total: int)
  requires total < 4
  ensures !CanFormCMEWithMatches(total)
{
  assert total / 2 - 1 < 1;
}

// Test 1: Does calling CannotFormOdd prove the postcondition?
lemma TestSingle(n: int)
  requires n % 2 == 1
  ensures !CanFormCMEWithMatches(n)
{
  CannotFormOdd(n);
}

// Test 2: Minimal forall with the predicate
lemma TestForallMinimal()
  ensures forall e | 0 <= e < 1 :: !CanFormCMEWithMatches(3 + e)
{
  forall e | 0 <= e < 1
    ensures !CanFormCMEWithMatches(3 + e)
  {
    assert e == 0;
    assert 3 + e == 3;
    CannotFormSmall(3 + e);
  }
}

// Test 3: General forall
lemma TestForallGeneral(n: int, extra: int)
  requires n >= 4
  requires extra == 1
  requires n % 2 == 1
  ensures forall e | 0 <= e < extra :: !CanFormCMEWithMatches(n + e)
{
  forall e | 0 <= e < extra
    ensures !CanFormCMEWithMatches(n + e)
  {
    assert e == 0;
    assert (n + e) % 2 == 1;
    CannotFormOdd(n + e);
  }
}
