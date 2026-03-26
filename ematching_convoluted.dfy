// The human encodes the math ONCE in a lemma.
// Then any caller just invokes the lemma to get the witness.

lemma quadraticHasNegative(a: int, b: int)
  requires b - a > 2
  ensures (a + 1 - a) * (a + 1 - b) < 0  // i.e., the value at a+1 is negative
{
  // Z3 checks: 1 * (a+1-b) < 0 since b > a+2. Trivial.
}

lemma quadratic_uses_lemma(s: seq<int>, a: int, b: int)
  requires 0 < a < b
  requires b - a > 2
  requires |s| > a + b
  requires forall i :: 0 <= i < |s| ==> s[i] == (i - a) * (i - b)
  ensures exists i :: 0 <= i < |s| && s[i] < 0
{
  quadraticHasNegative(a, b);
  // The lemma's postcondition puts the FACT into the context,
  // but does it create s[a+1] as a ground term? Let's see...
  assert s[a + 1] < 0;
}

// But the real question: can a LOOP find the witness automatically?
// Yes — a ghost method can search:

ghost method searchNegative(s: seq<int>, lo: int, hi: int) returns (idx: int)
  requires 0 <= lo < hi <= |s|
  requires exists i :: lo <= i < hi && s[i] < 0
  ensures lo <= idx < hi && s[idx] < 0
  decreases hi - lo
{
  if s[lo] < 0 {
    return lo;
  } else {
    // the witness must be in [lo+1, hi)
    idx := searchNegative(s, lo + 1, hi);
  }
}

lemma quadratic_uses_search(s: seq<int>, a: int, b: int)
  requires 0 < a < b
  requires b - a > 2
  requires |s| > a + b
  requires forall i :: 0 <= i < |s| ==> s[i] == (i - a) * (i - b)
  ensures exists i :: 0 <= i < |s| && s[i] < 0
{
  // We still need to establish the precondition of searchNegative:
  // "exists i :: 0 <= i < |s| && s[i] < 0" — but that's what we're proving!
  // Circular. The search doesn't help.
  assert s[a + 1] < 0;  // still need the manual witness
}
