// Test: can Dafny prove triggerless existentials?

// Test 1: Simple triggerless existential
ghost predicate P1()
{
  exists x | 1 <= x <= 10 :: x + x == 4
}

lemma Test1()
  ensures P1()
{
  assert 2 + 2 == 4;
}

// Test 2: With var binding (like our problem)
ghost predicate P2(total: int)
{
  exists a | 1 <= a <= total / 2 - 1 ::
    var b := total / 2 - a;
    a >= 1 && b >= 1 && a + b + (a + b) == total
}

lemma Test2()
  ensures P2(4)
{
  assert 1 >= 1;
  assert 1 >= 1;
  assert 1 + 1 + (1 + 1) == 4;
}

// Test 3: Using assert exists by
lemma Test3()
  ensures P2(4)
{
  assert P2(4) by {
    assert 1 >= 1;
    assert (4 / 2 - 1) >= 1;
    assert 1 + 1 + (1 + 1) == 4;
  }
}

// Test 4: Using assert with the body directly
lemma Test4()
  ensures P2(4)
{
  assert var b := 4 / 2 - 1; 1 >= 1 && b >= 1 && 1 + b + (1 + b) == 4;
}

// Test 5: General version
lemma Test5(total: int)
  requires total >= 4 && total % 2 == 0
  ensures P2(total)
{
  assert total == 2 * (total / 2);
  assert var b := total / 2 - 1; 1 >= 1 && b >= 1 && 1 + b + (1 + b) == total;
}

// Test 6: The actual predicate from our problem
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

lemma Test6a()
  ensures CanFormCMEWithMatches(4)
{
  assert var b := 4 / 2 - 1; IsValidCME(1, b, 1 + b) && 1 + b + (1 + b) == 4;
}

lemma Test6b(total: int)
  requires total >= 4 && total % 2 == 0
  ensures CanFormCMEWithMatches(total)
{
  assert total == 2 * (total / 2);
  assert total / 2 >= 2;
  assert var b := total / 2 - 1; IsValidCME(1, b, 1 + b) && 1 + b + (1 + b) == total;
}

// Test 7: Using assert ... by
lemma Test7(total: int)
  requires total >= 4 && total % 2 == 0
  ensures CanFormCMEWithMatches(total)
{
  assert CanFormCMEWithMatches(total) by {
    assert total == 2 * (total / 2);
    assert total / 2 >= 2;
    assert var b := total / 2 - 1; IsValidCME(1, b, 1 + b) && 1 + b + (1 + b) == total;
  }
}
