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

// Can we prove ExistsIntro without axiom?
lemma ExistsIntro(total: int, a: int)
  requires 1 <= a <= total / 2 - 1
  requires var b := total / 2 - a;
    IsValidCME(a, b, a + b) && a + b + (a + b) == total
  ensures CanFormCMEWithMatches(total)
{}
