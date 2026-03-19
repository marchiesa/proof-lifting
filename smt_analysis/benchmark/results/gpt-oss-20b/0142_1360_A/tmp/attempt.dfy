method MinimalSquare(a: int, b: int) returns (area: int)
  requires 1 <= a && 1 <= b
  ensures exists s :: 1 <= s && area == s * s && IsMinimalSide(a, b, s)
{
  var lo := if a < b then a else b;
  var hi := if a < b then b else a;
  var val := if 2 * lo > hi then 2 * lo else hi;

  // val = max(2*lo, hi) where lo = min(a,b), hi = max(a,b)
  assert val >= 1;
  assert lo <= hi;

  // Show CanFitInSquare(a, b, val)
  if a <= b {
    // lo == a, hi == b, val == max(2*a, b)
    assert 2 * a <= val && b <= val;
    assert FitsSideBySide(a, b, a, b, val);
  } else {
    // lo == b, hi == a, val == max(2*b, a)
    assert 2 * b <= val && a <= val;
    assert FitsSideBySide(b, a, b, a, val);
  }
  assert CanFitInSquare(a, b, val);

  // Key inequality: val <= a + b
  // Because 2*lo = 2*min(a,b) <= min(a,b) + max(a,b) = a+b
  // and hi = max(a,b) <= a+b
  assert val <= a + b;

  // Show minimality: no smaller square works
  forall s' :: 1 <= s' < val
    ensures !CanFitInSquare(a, b, s')
  {
    // s' < val <= a+b, so mixed-orientation configs fail
    assert !(a + b <= s');

    if a <= b {
      // val = max(2*a, b). Since a <= b: 2*b >= 2*a and 2*b >= b, so 2*b >= val
      assert 2 * b >= val;
      // Disjunct 1: FitsSideBySide(a,b,a,b,s') needs 2*a <= s' && b <= s'
      // s' < max(2*a, b) means !(2*a <= s' && b <= s')
      assert !(2 * a <= s' && b <= s');
      // Disjunct 2: FitsStacked(a,b,a,b,s') needs a <= s' && 2*b <= s'
      // s' < 2*b, so fails
      assert !(a <= s' && 2 * b <= s');
      // Disjunct 7: FitsSideBySide(b,a,b,a,s') needs 2*b <= s' && a <= s'
      // s' < 2*b, so fails
      assert !(2 * b <= s' && a <= s');
      // Disjunct 8: FitsStacked(b,a,b,a,s') needs b <= s' && 2*a <= s'
      // Same as disjunct 1 requirement: max(2*a, b) > s'
      assert !(b <= s' && 2 * a <= s');
    } else {
      // val = max(2*b, a). Since a > b: 2*a > 2*b and 2*a >= a, so 2*a >= val
      assert 2 * a >= val;
      assert !(2 * a <= s' && b <= s');
      assert !(a <= s' && 2 * b <= s');
      assert !(2 * b <= s' && a <= s');
      assert !(b <= s' && 2 * a <= s');
    }
  }

  area := val * val;
}