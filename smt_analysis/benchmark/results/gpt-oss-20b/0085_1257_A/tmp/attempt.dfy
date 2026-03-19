ghost function Abs(x: int): int
{
  if x >= 0 then x else -x
}

ghost predicate OrderFlipped(a: int, b: int, pa: int, pb: int)
{
  (a < b && pa > pb) || (a > b && pa < pb)
}

ghost function SwapCost(a: int, b: int, pa: int, pb: int): int
{
  Abs(a - pa) + Abs(b - pb) - (if OrderFlipped(a, b, pa, pb) then 1 else 0)
}

ghost predicate IsAchievable(n: int, x: int, a: int, b: int, d: int)
  requires n >= 2 && 1 <= a <= n && 1 <= b <= n && a != b && x >= 0
{
  exists pa: int, pb: int | 1 <= pa <= n && 1 <= pb <= n ::
    pa != pb && Abs(pa - pb) == d && SwapCost(a, b, pa, pb) <= x
}

ghost predicate IsMaxDistance(n: int, x: int, a: int, b: int, d: int)
  requires n >= 2 && 1 <= a <= n && 1 <= b <= n && a != b && x >= 0
{
  IsAchievable(n, x, a, b, d) &&
  forall pa: int, pb: int | 1 <= pa <= n && 1 <= pb <= n ::
    (pa != pb && SwapCost(a, b, pa, pb) <= x) ==> Abs(pa - pb) <= d
}

method TwoRivalStudents(n: int, x: int, a: int, b: int) returns (distance: int)
  requires n >= 2 && 1 <= a <= n && 1 <= b <= n && a != b && x >= 0
  ensures IsMaxDistance(n, x, a, b, distance)
{
  var la := a;
  var lb := b;
  var rx := x;
  if la > lb {
    var tmp := la;
    la := lb;
    lb := tmp;
  }

  ghost var oa := la;
  ghost var ob := lb;

  var da := if la - 1 < rx then la - 1 else rx;
  la := la - da;
  rx := rx - da;
  var db := if n - lb < rx then n - lb else rx;
  lb := lb + db;
  distance := lb - la;

  assert 1 <= la <= n && 1 <= lb <= n && la < lb;
  assert da >= 0 && db >= 0 && da + db <= x;
  assert distance == ob - oa + da + db;

  if a < b {
    assert oa == a && ob == b;
    assert la == a - da && lb == b + db;
    assert a - la == da;
    assert Abs(a - la) == da;
    assert lb - b == db;
    assert Abs(b - lb) == db;
    assert !OrderFlipped(a, b, la, lb);
    assert la != lb;
    assert Abs(la - lb) == distance;
  } else {
    assert a > b;
    assert oa == b && ob == a;
    assert lb == a + db && la == b - da;
    assert a - lb == -db;
    assert Abs(a - lb) == db;
    assert b - la == da;
    assert Abs(b - la) == da;
    assert !OrderFlipped(a, b, lb, la);
    assert lb != la;
    assert Abs(lb - la) == distance;
  }
  assert IsAchievable(n, x, a, b, distance);

  forall pa: int, pb: int | 1 <= pa <= n && 1 <= pb <= n && pa != pb && SwapCost(a, b, pa, pb) <= x
    ensures Abs(pa - pb) <= distance
  {
    if da + db < x {
      assert da == oa - 1;
      assert la == 1;
      assert db == n - ob;
      assert lb == n;
      assert distance == n - 1;
      assert Abs(pa - pb) <= n - 1;
    } else {
      assert da + db == x;
      if a < b {
        assert distance == (b - a) + x;
        if pa <= pb {
          assert !OrderFlipped(a, b, pa, pb);
          assert SwapCost(a, b, pa, pb) == Abs(a - pa) + Abs(b - pb);
          assert pb - pa <= Abs(a - pa) + (b - a) + Abs(b - pb);
          assert pb - pa <= x + (b - a);
          assert Abs(pa - pb) == pb - pa;
          assert Abs(pa - pb) <= distance;
        } else {
          assert OrderFlipped(a, b, pa, pb);
          assert SwapCost(a, b, pa, pb) == Abs(a - pa) + Abs(b - pb) - 1;
          assert pa - pb <= Abs(a - pa) + Abs(b - pb) - (b - a);
          assert pa - pb <= x + 1 - (b - a);
          assert pa - pb <= x;
          assert Abs(pa - pb) == pa - pb;
          assert Abs(pa - pb) <= distance;
        }
      } else {
        assert distance == (a - b) + x;
        if pa >= pb {
          assert !OrderFlipped(a, b, pa, pb);
          assert SwapCost(a, b, pa, pb) == Abs(a - pa) + Abs(b - pb);
          assert pa - pb <= Abs(a - pa) + (a - b) + Abs(b - pb);
          assert pa - pb <= x + (a - b);
          assert Abs(pa - pb) == pa - pb;
          assert Abs(pa - pb) <= distance;
        } else {
          assert OrderFlipped(a, b, pa, pb);
          assert SwapCost(a, b, pa, pb) == Abs(a - pa) + Abs(b - pb) - 1;
          assert pb - pa <= Abs(a - pa) + Abs(b - pb) - (a - b);
          assert pb - pa <= x + 1 - (a - b);
          assert pb - pa <= x;
          assert Abs(pa - pb) == pb - pa;
          assert Abs(pa - pb) <= distance;
        }
      }
    }
  }
}