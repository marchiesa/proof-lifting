predicate EndsWith(s: string, suffix: string)
{
  |s| >= |suffix| && s[|s| - |suffix|..] == suffix
}

predicate ValidSentence(s: string)
{
  EndsWith(s, "po") || EndsWith(s, "desu") || EndsWith(s, "masu") || EndsWith(s, "mnida")
}

function ClassifySentence(s: string): string
  requires ValidSentence(s)
{
  if EndsWith(s, "po") then "FILIPINO"
  else if EndsWith(s, "desu") || EndsWith(s, "masu") then "JAPANESE"
  else "KOREAN"
}

function ClassifyAll(sentences: seq<string>): seq<string>
  requires forall i | 0 <= i < |sentences| :: ValidSentence(sentences[i])
  decreases |sentences|
{
  if |sentences| == 0 then []
  else ClassifyAll(sentences[..|sentences|-1]) + [ClassifySentence(sentences[|sentences|-1])]
}

method SuffixThree(sentences: seq<string>) returns (results: seq<string>)
  requires forall i | 0 <= i < |sentences| :: ValidSentence(sentences[i])
  ensures results == ClassifyAll(sentences)
{
  results := [];
  for i := 0 to |sentences| {
    var s := sentences[i];
    var last := s[|s| - 1];
    if last == 'o' {
      results := results + ["FILIPINO"];
    } else if last == 'u' {
      results := results + ["JAPANESE"];
    } else {
      results := results + ["KOREAN"];
    }
  }
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // Testing ClassifyAll with small inputs derived from each test pair

  // From Test 1 (first 3 elements)
  expect ClassifyAll(["kamusta_po", "genki_desu", "ohayou_gozaimasu"]) == ["FILIPINO", "JAPANESE", "JAPANESE"], "spec positive 1";

  // From Test 2 (3 selected elements covering all 3 languages)
  expect ClassifyAll(["opo", "desu", "mmnida"]) == ["FILIPINO", "JAPANESE", "KOREAN"], "spec positive 2";

  // From Test 3 (3 selected elements)
  expect ClassifyAll(["po", "masu", "dmnida"]) == ["FILIPINO", "JAPANESE", "KOREAN"], "spec positive 3";

  // From Test 4 (3 selected elements)
  expect ClassifyAll(["imamnida", "desu_po", "masupo"]) == ["KOREAN", "FILIPINO", "FILIPINO"], "spec positive 4";

  // From Test 5 (3 selected elements)
  expect ClassifyAll(["mnidamnida", "adinm_masu", "mnida_po"]) == ["KOREAN", "JAPANESE", "FILIPINO"], "spec positive 5";

  // Single-element and empty tests
  expect ClassifyAll(["po"]) == ["FILIPINO"], "spec positive 6";
  expect ClassifyAll(["desu"]) == ["JAPANESE"], "spec positive 7";
  expect ClassifyAll(["masu"]) == ["JAPANESE"], "spec positive 8";
  expect ClassifyAll(["mnida"]) == ["KOREAN"], "spec positive 9";
  expect ClassifyAll([]) == [], "spec positive 10";

  // === SPEC NEGATIVE TESTS ===
  // Testing that ClassifyAll rejects wrong outputs, derived from each negative pair (scaled down)

  // From Negative 1: last element wrong "JAPANESE WRONG"
  expect ClassifyAll(["kamusta_po", "si_roy_mustang_ay_namamasu"]) != ["FILIPINO", "JAPANESE WRONG"], "spec negative 1";

  // From Negative 2: last element wrong "JAPANESE WRONG"
  expect ClassifyAll(["nakupo", "po_masu"]) != ["FILIPINO", "JAPANESE WRONG"], "spec negative 2";

  // From Negative 3: last element wrong "FILIPINO WRONG"
  expect ClassifyAll(["m_umasu", "o_ppo"]) != ["JAPANESE", "FILIPINO WRONG"], "spec negative 3";

  // From Negative 4: last element wrong "KOREAN WRONG"
  expect ClassifyAll(["masumasu", "masu_mnida"]) != ["JAPANESE", "KOREAN WRONG"], "spec negative 4";

  // From Negative 5: last element wrong "KOREAN WRONG"
  expect ClassifyAll(["tang_na_moo_po", "usam_mnida"]) != ["FILIPINO", "KOREAN WRONG"], "spec negative 5";

  // Additional negatives with swapped classifications
  expect ClassifyAll(["po"]) != ["JAPANESE"], "spec negative 6";
  expect ClassifyAll(["desu"]) != ["FILIPINO"], "spec negative 7";
  expect ClassifyAll(["mnida"]) != ["JAPANESE"], "spec negative 8";
  expect ClassifyAll(["po", "desu"]) != ["JAPANESE", "FILIPINO"], "spec negative 9";
  expect ClassifyAll(["masu"]) != ["KOREAN"], "spec negative 10";

  // === IMPLEMENTATION TESTS ===

  // Impl Test 1
  var r1 := SuffixThree([
    "kamusta_po",
    "genki_desu",
    "ohayou_gozaimasu",
    "annyeong_hashimnida",
    "hajime_no_ippo",
    "bensamu_no_sentou_houhou_ga_okama_kenpo",
    "ang_halaman_doon_ay_sarisari_singkamasu",
    "si_roy_mustang_ay_namamasu"
  ]);
  expect r1 == [
    "FILIPINO",
    "JAPANESE",
    "JAPANESE",
    "KOREAN",
    "FILIPINO",
    "FILIPINO",
    "JAPANESE",
    "JAPANESE"
  ], "impl test 1 failed";

  // Impl Test 2
  var r2 := SuffixThree([
    "opo",
    "p_po",
    "popo",
    "desu",
    "po",
    "udesu",
    "podesu",
    "desupo",
    "sddesu",
    "mumasu",
    "mmnida",
    "mmasu",
    "masu",
    "desu_po",
    "pomnida",
    "masumasu",
    "pppo",
    "mnida",
    "masu_po",
    "desu_masu",
    "a_masu",
    "po_po",
    "masupo",
    "masu_masu",
    "mnidamasu",
    "pomasu",
    "mnida_po",
    "mnida_desu",
    "nakupo",
    "po_masu"
  ]);
  expect r2 == [
    "FILIPINO",
    "FILIPINO",
    "FILIPINO",
    "JAPANESE",
    "FILIPINO",
    "JAPANESE",
    "JAPANESE",
    "FILIPINO",
    "JAPANESE",
    "JAPANESE",
    "KOREAN",
    "JAPANESE",
    "JAPANESE",
    "FILIPINO",
    "KOREAN",
    "JAPANESE",
    "FILIPINO",
    "KOREAN",
    "FILIPINO",
    "JAPANESE",
    "JAPANESE",
    "FILIPINO",
    "FILIPINO",
    "JAPANESE",
    "JAPANESE",
    "JAPANESE",
    "FILIPINO",
    "JAPANESE",
    "FILIPINO",
    "JAPANESE"
  ], "impl test 2 failed";

  // Impl Test 3
  var r3 := SuffixThree([
    "po",
    "ppo",
    "op_po",
    "mnida",
    "masu",
    "desu",
    "popo",
    "msmasu",
    "pomasu",
    "po_po",
    "usedpo",
    "masu_po",
    "opmasu",
    "opo",
    "ua_masu",
    "op_masu",
    "mnidapo",
    "dmnida",
    "opdesu",
    "adinmpo",
    "podesu",
    "nakupo",
    "oppo",
    "mmasu",
    "p_po",
    "adinm_po",
    "used_po",
    "usedmasu",
    "m_umasu",
    "o_ppo"
  ]);
  expect r3 == [
    "FILIPINO",
    "FILIPINO",
    "FILIPINO",
    "KOREAN",
    "JAPANESE",
    "JAPANESE",
    "FILIPINO",
    "JAPANESE",
    "JAPANESE",
    "FILIPINO",
    "FILIPINO",
    "FILIPINO",
    "JAPANESE",
    "FILIPINO",
    "JAPANESE",
    "JAPANESE",
    "FILIPINO",
    "KOREAN",
    "JAPANESE",
    "FILIPINO",
    "JAPANESE",
    "FILIPINO",
    "FILIPINO",
    "JAPANESE",
    "FILIPINO",
    "FILIPINO",
    "FILIPINO",
    "JAPANESE",
    "JAPANESE",
    "FILIPINO"
  ], "impl test 3 failed";

  // Impl Test 4
  var r4 := SuffixThree([
    "imamnida",
    "usamdesu",
    "pomnida",
    "desudesu",
    "op_desu",
    "desumnida",
    "po_desu",
    "po_mnida",
    "a_mnida",
    "desu_po",
    "mnidamasu",
    "masupo",
    "desumasu",
    "udesu",
    "desupo",
    "e_desu",
    "po_masu",
    "uudesu",
    "usedmnida",
    "usampo",
    "masu_masu",
    "mnida_masu",
    "kamusta_po",
    "masudesu",
    "u_masu",
    "ds_desu",
    "u_edesu",
    "desu_masu",
    "masumasu",
    "masu_mnida"
  ]);
  expect r4 == [
    "KOREAN",
    "JAPANESE",
    "KOREAN",
    "JAPANESE",
    "JAPANESE",
    "KOREAN",
    "JAPANESE",
    "KOREAN",
    "KOREAN",
    "FILIPINO",
    "JAPANESE",
    "FILIPINO",
    "JAPANESE",
    "JAPANESE",
    "FILIPINO",
    "JAPANESE",
    "JAPANESE",
    "JAPANESE",
    "KOREAN",
    "FILIPINO",
    "JAPANESE",
    "JAPANESE",
    "FILIPINO",
    "JAPANESE",
    "JAPANESE",
    "JAPANESE",
    "JAPANESE",
    "JAPANESE",
    "JAPANESE",
    "KOREAN"
  ], "impl test 4 failed";

  // Impl Test 5
  var r5 := SuffixThree([
    "mnidamnida",
    "opmnida",
    "adinm_masu",
    "usam_masu",
    "useddesu",
    "adinmmasu",
    "mnida_po",
    "dnmnida",
    "masumnida",
    "usam_po",
    "mnidadesu",
    "used_masu",
    "mnida_mnida",
    "adinm_mnida",
    "usammasu",
    "masu_desu",
    "usammnida",
    "genki_desu",
    "mm_mnida",
    "adinmmnida",
    "op_mnida",
    "adinm_desu",
    "used_desu",
    "usam_desu",
    "adinmdesu",
    "saranghamnida",
    "desu_desu",
    "tang_na_moo_po",
    "used_mnida",
    "usam_mnida"
  ]);
  expect r5 == [
    "KOREAN",
    "KOREAN",
    "JAPANESE",
    "JAPANESE",
    "JAPANESE",
    "JAPANESE",
    "FILIPINO",
    "KOREAN",
    "KOREAN",
    "FILIPINO",
    "JAPANESE",
    "JAPANESE",
    "KOREAN",
    "KOREAN",
    "JAPANESE",
    "JAPANESE",
    "KOREAN",
    "JAPANESE",
    "KOREAN",
    "KOREAN",
    "KOREAN",
    "JAPANESE",
    "JAPANESE",
    "JAPANESE",
    "JAPANESE",
    "KOREAN",
    "JAPANESE",
    "FILIPINO",
    "KOREAN",
    "KOREAN"
  ], "impl test 5 failed";

  print "All tests passed\n";
}