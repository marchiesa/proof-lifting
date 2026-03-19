ghost function CountChar(s: seq<char>, c: char): nat
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[|s|-1] == c then 1 else 0) + CountChar(s[..|s|-1], c)
}

ghost function CountInt(s: seq<int>, v: int): nat
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[|s|-1] == v then 1 else 0) + CountInt(s[..|s|-1], v)
}

ghost predicate FeasibleCounts(cn: nat, cz: nat, cr: nat, co: nat, ce: nat,
                         ones: nat, zeros: nat)
{
  ones <= cn &&
  zeros <= cz &&
  zeros <= cr &&
  ones + zeros <= co &&
  ones + zeros <= ce
}

ghost predicate Feasible(s: seq<char>, ones: nat, zeros: nat)
{
  FeasibleCounts(CountChar(s, 'n'), CountChar(s, 'z'), CountChar(s, 'r'),
                 CountChar(s, 'o'), CountChar(s, 'e'), ones, zeros)
}

ghost predicate BinaryGeq(x1: nat, y1: nat, x2: nat, y2: nat)
{
  if x2 == 0 then true
  else if x1 == 0 then false
  else x1 + y1 > x2 + y2 || (x1 + y1 == x2 + y2 && x1 >= x2)
}

lemma CountCharStep(s: seq<char>, i: nat, c: char)
  requires 0 <= i < |s|
  ensures CountChar(s[..i+1], c) == CountChar(s[..i], c) + (if s[i] == c then 1 else 0)
{
  assert s[..i+1][..i] == s[..i];
}

lemma CountIntOnesSeq(n: nat)
  ensures CountInt(seq(n, (i: nat) => 1), 1) == n
  ensures CountInt(seq(n, (i: nat) => 1), 0) == 0
  decreases n
{
  if n > 0 {
    assert seq(n, (i: nat) => 1)[..n-1] == seq(n-1, (i: nat) => 1);
    CountIntOnesSeq(n-1);
  }
}

lemma CountIntZerosSeq(n: nat)
  ensures CountInt(seq(n, (i: nat) => 0), 0) == n
  ensures CountInt(seq(n, (i: nat) => 0), 1) == 0
  decreases n
{
  if n > 0 {
    assert seq(n, (i: nat) => 0)[..n-1] == seq(n-1, (i: nat) => 0);
    CountIntZerosSeq(n-1);
  }
}

lemma CountIntConcat(a: seq<int>, b: seq<int>, v: int)
  ensures CountInt(a + b, v) == CountInt(a, v) + CountInt(b, v)
  decreases |b|
{
  if |b| == 0 {
    assert a + b == a;
  } else {
    assert (a + b)[..|a + b| - 1] == a + b[..|b| - 1];
    CountIntConcat(a, b[..|b| - 1], v);
  }
}

lemma OptimalityLemma(cn: nat, cz: nat, cr: nat, co: nat, ce: nat,
                       x: nat, y: nat, xp: nat, yp: nat)
  requires x <= co && x <= cn && x <= ce
  requires x == co || x == cn || x == ce
  requires y <= cz && y <= ce - x && y <= cr && y <= co - x
  requires y == cz || y == ce - x || y == cr || y == co - x
  requires FeasibleCounts(cn, cz, cr, co, ce, xp, yp)
  ensures BinaryGeq(x, y, xp, yp)
{
  assert xp <= cn;
  assert xp <= co;
  assert xp <= ce;
  assert xp <= x;

  if xp == 0 {
  } else {
    if y == co - x {
      assert x + y == co;
      assert xp + yp <= co;
    } else if y == ce - x {
      assert x + y == ce;
      assert xp + yp <= ce;
    } else if y == cz {
      assert yp <= cz;
      assert yp <= y;
      assert xp + yp <= x + y;
    } else {
      assert y == cr;
      assert yp <= cr;
      assert yp <= y;
      assert xp + yp <= x + y;
    }
  }
}

method Cards(s: seq<char>) returns (result: seq<int>)
  requires forall i | 0 <= i < |s| :: s[i] in {'z', 'e', 'r', 'o', 'n'}
  ensures var ones := CountInt(result, 1);
          var zeros := CountInt(result, 0);
          var cn := CountChar(s, 'n');
          var cz := CountChar(s, 'z');
          var cr := CountChar(s, 'r');
          var co := CountChar(s, 'o');
          var ce := CountChar(s, 'e');
          |result| == ones + zeros &&
          result == seq(ones, (i: nat) => 1) + seq(zeros, (i: nat) => 0) &&
          FeasibleCounts(cn, cz, cr, co, ce, ones, zeros) &&
          (forall x: nat, y: nat ::
            FeasibleCounts(cn, cz, cr, co, ce, x, y) ==>
            BinaryGeq(ones, zeros, x, y))
{
  var z: nat := 0;
  var e: nat := 0;
  var r: nat := 0;
  var o: nat := 0;
  var n: nat := 0;

  for i := 0 to |s|
    invariant z == CountChar(s[..i], 'z')
    invariant e == CountChar(s[..i], 'e')
    invariant r == CountChar(s[..i], 'r')
    invariant o == CountChar(s[..i], 'o')
    invariant n == CountChar(s[..i], 'n')
  {
    CountCharStep(s, i, 'z');
    CountCharStep(s, i, 'e');
    CountCharStep(s, i, 'r');
    CountCharStep(s, i, 'o');
    CountCharStep(s, i, 'n');
    if s[i] == 'z' {
      z := z + 1;
    } else if s[i] == 'e' {
      e := e + 1;
    } else if s[i] == 'r' {
      r := r + 1;
    } else if s[i] == 'o' {
      o := o + 1;
    } else {
      assert s[i] == 'n';
      n := n + 1;
    }
  }

  ghost var gcn := n;
  ghost var gcz := z;
  ghost var gcr := r;
  ghost var gco := o;
  ghost var gce := e;

  var x := o;
  if n < x { x := n; }
  if e < x { x := e; }

  assert x <= gco && x <= gcn && x <= gce;
  assert x == gco || x == gcn || x == gce;

  o := o - x;
  n := n - x;
  e := e - x;

  var y := z;
  if e < y { y := e; }
  if r < y { y := r; }
  if o < y { y := o; }

  assert y <= gcz && y <= gce - x && y <= gcr && y <= gco - x;
  assert y == gcz || y == gce - x || y == gcr || y == gco - x;

  result := seq(x, (i: nat) => 1) + seq(y, (i: nat) => 0);

  CountIntOnesSeq(x);
  CountIntZerosSeq(y);
  CountIntConcat(seq(x, (i: nat) => 1), seq(y, (i: nat) => 0), 1);
  CountIntConcat(seq(x, (i: nat) => 1), seq(y, (i: nat) => 0), 0);

  assert CountInt(result, 1) == x;
  assert CountInt(result, 0) == y;

  assert FeasibleCounts(gcn, gcz, gcr, gco, gce, x, y);

  forall a: nat, b: nat | FeasibleCounts(gcn, gcz, gcr, gco, gce, a, b)
    ensures BinaryGeq(x, y, a, b)
  {
    OptimalityLemma(gcn, gcz, gcr, gco, gce, x, y, a, b);
  }
}

method {:verify false} Main()
{
  var r1 := Cards("ezor");
  expect r1 == [0], "Test 1 failed";

  var r2 := Cards("nznooeeoer");
  expect r2 == [1, 1, 0], "Test 2 failed";

  var r3 := Cards("eorz");
  expect r3 == [0], "Test 3 failed";

  var r4 := Cards("noe");
  expect r4 == [1], "Test 4 failed";

  var r5 := Cards("oeerzzozozzrezeezzzoroozrrreorrreereooeo");
  expect r5 == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0], "Test 5 failed";

  var r6 := Cards("oeonznzneeononnerooooooeeeneenre");
  expect r6 == [1, 1, 1, 1, 1, 1, 1, 1, 0, 0], "Test 6 failed";

  var r7 := Cards("ozrorrooeoeeeozonoenzoeoreenzrzenen");
  expect r7 == [1, 1, 1, 1, 1, 0, 0, 0, 0, 0], "Test 7 failed";

  var r8 := Cards("ooeoeneenneooeennnoeeonnooneno");
  expect r8 == [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], "Test 8 failed";

  var r9 := Cards("zzzerrzrzzrozrezooreroeoeezerrzeerooereezeeererrezrororoorrzezoeerrorzrezzrzoerrzorrooerzrzeozrrorzzzzeoeereeroeozezeozoozooereoeorrzoroeoezooeerorreeorezeozeroerezoerooooeerozrrorzozeroereerozeozeoerroroereeeerzzrzeeozrezzozeoooeerzzzorozrzezrrorozezoorzzerzroeeeerorreeoezoeroeeezerrzeorzoeorzoeeororzezrzzorrreozzorzroozzoereorzzroozorezzrozzzzzezorzzrzoooorzzzrrozeezrzzzezzoezeozooe...
  expect r9 == seq(100, (i: nat) => 0), "Test 9 failed";

  var r10 := Cards("eeroooreoeoeroenezononnenonrnrzenonooozrznrezonezeeoeezeoroenoezrrrzoeoeooeeeezrrorzrooorrenznoororoozzrezeroerzrnnoreoeozne...
  expect r10 == seq(44, (i: nat) => 1) + seq(56, (i: nat) => 0), "Test 10 failed";

  var r11 := Cards("zzornzoereooreoeeoeeeezezrnzzeozorororznoznzoozrozezrnornrrronneeeeonezeornoooeeeeeeernzooozrroeezznzeozooenoroooeeeooezorrozoeoonoonreoezerreno...
  expect r11 == seq(50, (i: nat) => 1) + seq(50, (i: nat) => 0), "Test 11 failed";

  var r12 := Cards("oeeeneoenooonnoeeoonenoeeeooeeneoeneeeenoeooooenneneeneoneonnnonnonnnnennoneoonenoeononennnonoonneeoooeeeeneonoo...
  expect r12 == seq(100, (i: nat) => 1), "Test 12 failed";

  print "All tests passed\n";
}