function CountChar(s: seq<char>, c: char): nat
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[|s|-1] == c then 1 else 0) + CountChar(s[..|s|-1], c)
}

function CountInt(s: seq<int>, v: int): nat
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[|s|-1] == v then 1 else 0) + CountInt(s[..|s|-1], v)
}

predicate FeasibleCounts(cn: nat, cz: nat, cr: nat, co: nat, ce: nat,
                         ones: nat, zeros: nat)
{
  ones <= cn &&
  zeros <= cz &&
  zeros <= cr &&
  ones + zeros <= co &&
  ones + zeros <= ce
}

predicate Feasible(s: seq<char>, ones: nat, zeros: nat)
{
  FeasibleCounts(CountChar(s, 'n'), CountChar(s, 'z'), CountChar(s, 'r'),
                 CountChar(s, 'o'), CountChar(s, 'e'), ones, zeros)
}

predicate BinaryGeq(x1: nat, y1: nat, x2: nat, y2: nat)
{
  if x2 == 0 then true
  else if x1 == 0 then false
  else x1 + y1 > x2 + y2 || (x1 + y1 == x2 + y2 && x1 >= x2)
}

// Top-level spec predicate wrapping the ensures clause of Cards
predicate CardsSpec(s: seq<char>, result: seq<int>)
{
  var ones := CountInt(result, 1);
  var zeros := CountInt(result, 0);
  var cn := CountChar(s, 'n');
  var cz := CountChar(s, 'z');
  var cr := CountChar(s, 'r');
  var co := CountChar(s, 'o');
  var ce := CountChar(s, 'e');
  |result| == ones + zeros &&
  result == seq(ones, (i: nat) => 1) + seq(zeros, (i: nat) => 0) &&
  FeasibleCounts(cn, cz, cr, co, ce, ones, zeros) &&
  (forall x, y | 0 <= x <= |s| && 0 <= y <= |s| &&
                   FeasibleCounts(cn, cz, cr, co, ce, x, y) ::
    BinaryGeq(ones, zeros, x, y))
}

method {:verify false} Cards(s: seq<char>) returns (result: seq<int>)
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
          (forall x, y | 0 <= x <= |s| && 0 <= y <= |s| &&
                         FeasibleCounts(cn, cz, cr, co, ce, x, y) ::
            BinaryGeq(ones, zeros, x, y))
{
  var z := 0;
  var e := 0;
  var r := 0;
  var o := 0;
  var n := 0;

  for i := 0 to |s| {
    if s[i] == 'z' {
      z := z + 1;
    } else if s[i] == 'e' {
      e := e + 1;
    } else if s[i] == 'r' {
      r := r + 1;
    } else if s[i] == 'o' {
      o := o + 1;
    } else {
      n := n + 1;
    }
  }

  var x := o;
  if n < x { x := n; }
  if e < x { x := e; }

  o := o - x;
  n := n - x;
  e := e - x;

  var y := z;
  if e < y { y := e; }
  if r < y { y := r; }
  if o < y { y := o; }

  result := seq(x, (i: nat) => 1) + seq(y, (i: nat) => 0);
}

method {:verify false} Main()
{
  // ===== SPEC POSITIVE TESTS (small inputs, correct outputs) =====
  // Empty input => empty output
  expect CardsSpec("", []), "spec positive 1";
  // Single chars that can't spell "one" or "zero"
  expect CardsSpec("n", []), "spec positive 2";
  expect CardsSpec("e", []), "spec positive 3";
  expect CardsSpec("o", []), "spec positive 4";
  // Exactly the letters for "one" => [1]
  expect CardsSpec("one", [1]), "spec positive 5";
  // Permutations of "one" => [1]  (scaled from test 4: "noe" -> [1])
  expect CardsSpec("noe", [1]), "spec positive 6";
  expect CardsSpec("eon", [1]), "spec positive 7";

  // ===== SPEC NEGATIVE TESTS (small inputs, wrong outputs) =====
  // Scaled from neg 1: no 'n', can't spell "one" — wrong output [1]
  expect !CardsSpec("ero", [1]), "spec negative 1";
  // Scaled from neg 2: result contains 2 (not a valid digit)
  expect !CardsSpec("noe", [2]), "spec negative 2";
  // Scaled from neg 3: no 'n'/'z', can't spell "one" — wrong output [1]
  expect !CardsSpec("ore", [1]), "spec negative 3";
  // Neg 4 is already small: "noe" -> [2]
  expect !CardsSpec("one", [2]), "spec negative 4";
  // Scaled from neg 5: no 'n', can't make ones=1
  expect !CardsSpec("ze", [1]), "spec negative 5";
  // Scaled from neg 6: result contains 2
  expect !CardsSpec("eno", [2, 1]), "spec negative 6";
  // Scaled from neg 7: result contains 2
  expect !CardsSpec("oe", [2]), "spec negative 7";
  // Scaled from neg 8: result contains 2
  expect !CardsSpec("ne", [2]), "spec negative 8";
  // Scaled from neg 9: no 'n'/'o'/'e', can't make ones=1
  expect !CardsSpec("zr", [1]), "spec negative 9";
  // Scaled from neg 10: result contains 2
  expect !CardsSpec("oen", [2, 1]), "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====
  var r1 := Cards("ezor");
  expect r1 == [0], "impl test 1 failed";

  var r2 := Cards("nznooeeoer");
  expect r2 == [1, 1, 0], "impl test 2 failed";

  var r3 := Cards("eorz");
  expect r3 == [0], "impl test 3 failed";

  var r4 := Cards("noe");
  expect r4 == [1], "impl test 4 failed";

  var r5 := Cards("oeerzzozozzrezeezzzoroozrrreorrreereooeo");
  expect r5 == seq(10, (i: nat) => 0), "impl test 5 failed";

  var r6 := Cards("oeonznzneeononnerooooooeeeneenre");
  expect r6 == seq(8, (i: nat) => 1) + seq(2, (i: nat) => 0), "impl test 6 failed";

  var r7 := Cards("ozrorrooeoeeeozonoenzoeoreenzrzenen");
  expect r7 == seq(5, (i: nat) => 1) + seq(5, (i: nat) => 0), "impl test 7 failed";

  var r8 := Cards("ooeoeneenneooeennnoeeonnooneno");
  expect r8 == seq(10, (i: nat) => 1), "impl test 8 failed";

  var r9 := Cards("zzzerrzrzzrozrezooreroeoeezerrzeerooereezeeererrezrororoorrzezoeerrorzrezzrzoerrzorrooerzrzeozrrorzzzzeoeereeroeozezeozoozooereoeorrzoroeoezooeerorreeorezeozeroerezoerooooeerozrrorzozeroereerozeozeoerroroereeeerzzrzeeozrezzozeoooeerzzzorozrzezrrorozezoorzzerzroeeeerorreeoezoeroeeezerrzeorzoeorzoeeororzezrzzorrreozzorzroozzoereorzzroozoreorrrorezzozzzzezorzzrzoooorzzzrrozeezrzzzezzoezeozoooezroozez");
  expect r9 == seq(100, (i: nat) => 0), "impl test 9 failed";

  var r10 := Cards("eeroooreoeoeroenezononnenonrnrzenonooozrznrezonezeeoeezeoroenoezrrrzoeoeooeeeezrrorzrooorrenznoororoozzrezeroerzrnnoreoeoznezrznorznozoozeoneeezerrnronrernzzrneoeroezoorerzrneoeoozerenreeozrneoeozeoeonzernneoeozooeeoezoroeroeorzeeeeooozooorzeeorzreezeezooeeezeooeozreooeoooeoenzrezonrnzoezooeoneneeozrnozooooeoeozreezerzooroooernzneozzznnezeneennerzereonee");
  expect r10 == seq(44, (i: nat) => 1) + seq(56, (i: nat) => 0), "impl test 10 failed";

  var r11 := Cards("zzornzoereooreoeeoeeeezezrnzzeozorororznoznzoozrozezrnornrrronneeeeonezeornoooeeeeeeernzooozrroeezznzeozooenoroooeeeooezorrozoeoonoonreoezerrenozoenooeenneneorzorzonooooozoeoneeooorennezeezoeeeoereezoorrnreerenezneznzoooereorzozeoerznoonzrzneonzreoeeoenoeroeorooerrezroeoeeeoneneornonennnenenoeznonzreenororeeeznoeeeoezonorzoeoonreroenneeeezoorozrzoz");
  expect r11 == seq(50, (i: nat) => 1) + seq(50, (i: nat) => 0), "impl test 11 failed";

  var r12 := Cards("oeeeneoenooonnoeeoonenoeeeooeeneoeneeeenoeooooenneneeneoneonnnonnonnnnennoneoonenoeononennnonoonneeoooeeeeneonooeoonoononoeeooennnneneneeneoononeeeennooeenooeoeoeneeoennooeeennenoonenneooenoenneneneoeonnneooooneeonoonnnnnoeoenoonnnennnoneeononeeeenoeeeoeoeoonnonoeneoneooooonoooneeeeooneneonnoneeoooe");
  expect r12 == seq(100, (i: nat) => 1), "impl test 12 failed";

  print "All tests passed\n";
}