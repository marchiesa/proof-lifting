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

// Test A: direct substitution without var
ghost predicate CanFormDirect(total: int)
{
  exists a | 1 <= a <= total / 2 - 1 ::
    IsValidCME(a, total / 2 - a, total / 2) && total / 2 + total / 2 == total
}

lemma ProveDirect(total: int)
  requires total >= 4
  requires total % 2 == 0
  ensures CanFormDirect(total)
{
  assert IsValidCME(1, total / 2 - 1, total / 2);
  assert total / 2 + total / 2 == total;
}

// Test B: ExistsIntro as axiom, then use it
lemma {:axiom} ExistsIntro(total: int, a: int)
  requires 1 <= a <= total / 2 - 1
  requires var b := total / 2 - a;
    IsValidCME(a, b, a + b) && a + b + (a + b) == total
  ensures CanFormCMEWithMatches(total)

lemma CanFormWitnessViaAxiom(total: int)
  requires total >= 4
  requires total % 2 == 0
  ensures CanFormCMEWithMatches(total)
{
  assert total / 2 + total / 2 == total;
  assert total / 2 - 1 >= 1;
  assert IsValidCME(1, total / 2 - 1, total / 2);
  assert 1 + (total / 2 - 1) + (1 + (total / 2 - 1)) == total;
  ExistsIntro(total, 1);
}

// Test C: direct equiv
lemma DirectEquiv(total: int)
  ensures CanFormDirect(total) == CanFormCMEWithMatches(total)
{
}
