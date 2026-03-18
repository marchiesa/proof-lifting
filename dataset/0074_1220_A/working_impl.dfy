method Cards(s: seq<char>) returns (result: seq<int>)
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

method Main()
{
  // Test 1
  var r1 := Cards("ezor");
  expect r1 == [0], "Test 1 failed";

  // Test 2
  var r2 := Cards("nznooeeoer");
  expect r2 == [1, 1, 0], "Test 2 failed";

  // Test 3
  var r3 := Cards("eorz");
  expect r3 == [0], "Test 3 failed";

  // Test 4
  var r4 := Cards("noe");
  expect r4 == [1], "Test 4 failed";

  // Test 5
  var r5 := Cards("oeerzzozozzrezeezzzoroozrrreorrreereooeo");
  expect r5 == [0, 0, 0, 0, 0, 0, 0, 0, 0, 0], "Test 5 failed";

  // Test 6
  var r6 := Cards("oeonznzneeononnerooooooeeeneenre");
  expect r6 == [1, 1, 1, 1, 1, 1, 1, 1, 0, 0], "Test 6 failed";

  // Test 7
  var r7 := Cards("ozrorrooeoeeeozonoenzoeoreenzrzenen");
  expect r7 == [1, 1, 1, 1, 1, 0, 0, 0, 0, 0], "Test 7 failed";

  // Test 8
  var r8 := Cards("ooeoeneenneooeennnoeeonnooneno");
  expect r8 == [1, 1, 1, 1, 1, 1, 1, 1, 1, 1], "Test 8 failed";

  // Test 9
  var r9 := Cards("zzzerrzrzzrozrezooreroeoeezerrzeerooereezeeererrezrororoorrzezoeerrorzrezzrzoerrzorrooerzrzeozrrorzzzzeoeereeroeozezeozoozooereoeorrzoroeoezooeerorreeorezeozeroerezoerooooeerozrrorzozeroereerozeozeoerroroereeeerzzrzeeozrezzozeoooeerzzzorozrzezrrorozezoorzzerzroeeeerorreeoezoeroeeezerrzeorzoeorzoeeororzezrzzorrreozzorzroozzoereorzzroozoreorrrorezzozzzzezorzzrzoooorzzzrrozeezrzzzezzoezeozoooezroozez");
  expect r9 == seq(100, (i: nat) => 0), "Test 9 failed";

  // Test 10
  var r10 := Cards("eeroooreoeoeroenezononnenonrnrzenonooozrznrezonezeeoeezeoroenoezrrrzoeoeooeeeezrrorzrooorrenznoororoozzrezeroerzrnnoreoeoznezrznorznozoozeoneeezerrnronrernzzrneoeroezoorerzrneoeoozerenreeozrneoeozeoeonzernneoeozooeeoezoroeroeorzeeeeooozooorzeeorzreezeezooeeezeooeozreooeoooeoenzrezonrnzoezooeoneneeozrnozooooeoeozreezerzooroooernzneozzznnezeneennerzereonee");
  expect r10 == seq(44, (i: nat) => 1) + seq(56, (i: nat) => 0), "Test 10 failed";

  // Test 11
  var r11 := Cards("zzornzoereooreoeeoeeeezezrnzzeozorororznoznzoozrozezrnornrrronneeeeonezeornoooeeeeeeernzooozrroeezznzeozooenoroooeeeooezorrozoeoonoonreoezerrenozoenooeenneneorzorzonooooozoeoneeooorennezeezoeeeoereezoorrnreerenezneznzoooereorzozeoerznoonzrzneonzreoeeoenoeroeorooerrezroeoeeeoneneornonennnenenoeznonzreenororeeeznoeeeoezonorzoeoonreroenneeeezoorozrzoz");
  expect r11 == seq(50, (i: nat) => 1) + seq(50, (i: nat) => 0), "Test 11 failed";

  // Test 12
  var r12 := Cards("oeeeneoenooonnoeeoonenoeeeooeeneoeneeeenoeooooenneneeneoneonnnonnonnnnennoneoonenoeononennnonoonneeoooeeeeneonooeoonoononoeeooennnneneneeneoononeeeennooeenooeoeoeneeoennooeeennenoonenneooenoenneneneoeonnneooooneeonoonnnnnoeoenoonnnennnoneeononeeeenoeeeoeoeoonnonoeneoneooooonoooneeeeooneneonnoneeoooe");
  expect r12 == seq(100, (i: nat) => 1), "Test 12 failed";

  print "All tests passed\n";
}