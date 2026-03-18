// A valid assignment: enough pens for all lectures, enough pencils for all
// practical classes, and they fit in the pencilcase.
ghost predicate ValidAssignment(x: int, y: int, a: int, b: int, c: int, d: int, k: int)
{
  x >= 0 && y >= 0 && x * c >= a && y * d >= b && x + y <= k
}

// The problem is feasible iff some valid assignment of pens and pencils exists.
ghost predicate Feasible(a: int, b: int, c: int, d: int, k: int)
{
  exists x :: exists y :: ValidAssignment(x, y, a, b, c, d, k)
}


lemma CeilDivLower(a: int, c: int)
  requires a >= 1 && c >= 1
  ensures ((a + c - 1) / c) * c >= a
  ensures (a + c - 1) / c >= 0


{
  var q := (a + c - 1) / c;
  if x < q {
    var r := (a + c - 1) % c;
    assert q * c + r == a + c - 1;
    assert q * c == a + c - 1 - r;
    assert (q - 1) * c == q * c - c;
    assert (q - 1) * c == a - 1 - r;
    assert (q - 1) * c <= a - 1;
    // Inlined from MulLe(x, q - 1, c)


  assert q * (c) + r == (a) + (c) - 1;
  assert r >= 0;
  // q * (c) = (a) + (c) - 1 - r >= (a) + (c) - 1 - ((c) - 1) = (a)
  assert ((a + c - 1) / c) * c >= a;
  assert (a + c - 1) / c >= 0;
  // Inlined from CeilDivLower(b, d)
  var q := ((b) + (d) - 1) / (d);
  var r := ((b) + (d) - 1) % (d);
  assert q * (d) + r == (b) + (d) - 1;
  assert r >= 0;
  // q * (d) = (b) + (d) - 1 - r >= (b) + (d) - 1 - ((d) - 1) = (b)
  assert ((b + d - 1) / d) * d >= b;
  assert (b + d - 1) / d >= 0;

  if pens + pencils <= k {
    assert ValidAssignment(pens, pencils, a, b, c, d, k);
    return pens, pencils;
  } else {
    assert forall x0, y0 :: !ValidAssignment(x0, y0, a, b, c, d, k) by {
      forall x0, y0
        ensures !ValidAssignment(x0, y0, a, b, c, d, k)
      {
        if x0 >= 0 && y0 >= 0 && x0 * c >= a && y0 * d >= b {
          // Inlined from CeilDivMinimal(a, c, x0)
          var q := ((a) + (c) - 1) / (c);
          if (x0) < q {
          var r := ((a) + (c) - 1) % (c);
          assert q * (c) + r == (a) + (c) - 1;
          assert q * (c) == (a) + (c) - 1 - r;
          assert (q - 1) * (c) == q * (c) - (c);
          assert (q - 1) * (c) == (a) - 1 - r;
          assert (q - 1) * (c) <= (a) - 1;
          MulLe((x0), q - 1, (c));
          assert (x0) * (c) <= (q - 1) * (c);
          assert (x0) * (c) <= (a) - 1;
          assert false;
          }
          assert x0 >= (a + c - 1) / c;
          // Inlined from CeilDivMinimal(b, d, y0)
          var q := ((b) + (d) - 1) / (d);
          if (y0) < q {
          var r := ((b) + (d) - 1) % (d);
          assert q * (d) + r == (b) + (d) - 1;
          assert q * (d) == (b) + (d) - 1 - r;
          assert (q - 1) * (d) == q * (d) - (d);
          assert (q - 1) * (d) == (b) - 1 - r;
          assert (q - 1) * (d) <= (b) - 1;
          MulLe((y0), q - 1, (d));
          assert (y0) * (d) <= (q - 1) * (d);
          assert (y0) * (d) <= (b) - 1;
          assert false;
          }
          assert y0 >= (b + d - 1) / d;
          assert x0 >= pens;
          assert y0 >= pencils;
          assert x0 + y0 >= pens + pencils > k;
        }
      }
    }
    assert !Feasible(a, b, c, d, k);
    return -1, 0;
  }
}
