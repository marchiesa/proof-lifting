function ToLower(c: char): char
{
  if 'A' <= c <= 'Z' then
    ((c as int - 'A' as int + 'a' as int) as char)
  else
    c
}

predicate CIEqual(s: seq<char>, t: seq<char>)
{
  |s| == |t| &&
  forall i | 0 <= i < |s| :: ToLower(s[i]) == ToLower(t[i])
}

predicate CILessThan(s: seq<char>, t: seq<char>)
{
  exists k | 0 <= k <= |s| && k <= |t| ::
    (forall j | 0 <= j < k :: ToLower(s[j]) == ToLower(t[j]))
    && ((k == |s| && k < |t|) || (k < |s| && k < |t| && ToLower(s[k]) < ToLower(t[k])))
}

method PetyaAndStrings(s: seq<char>, t: seq<char>) returns (result: int)
  ensures result == 0 <==> CIEqual(s, t)
  ensures result == -1 <==> CILessThan(s, t)
  ensures result == 1 <==> CILessThan(t, s)
{
  var len := if |s| < |t| then |s| else |t|;
  var i := 0;
  while i < len
  {
    var cs := s[i];
    var ct := t[i];
    if 'A' <= cs <= 'Z' {
      cs := (cs as int - 'A' as int + 'a' as int) as char;
    }
    if 'A' <= ct <= 'Z' {
      ct := (ct as int - 'A' as int + 'a' as int) as char;
    }
    if cs < ct {
      result := -1;
      return;
    } else if cs > ct {
      result := 1;
      return;
    }
    i := i + 1;
  }
  if |s| < |t| {
    result := -1;
  } else if |s| > |t| {
    result := 1;
  } else {
    result := 0;
  }
}

method Main()
{
  var r: int;

  // ===== SPEC POSITIVE TESTS =====
  // Scaled to small inputs (length 1-2) to keep bounded quantifier evaluation fast.
  // Each maps to an ensures predicate: result==0 ↔ CIEqual, result==-1 ↔ CILessThan(s,t), result==1 ↔ CILessThan(t,s)

  // From test 1 (aaaa/aaaA → 0): scaled to ("a","A") → equal
  expect CIEqual("a", "A"), "spec positive 1";

  // From test 2 (abs/Abz → -1): key diff s<z, scaled to ("s","z")
  expect CILessThan("s", "z"), "spec positive 2";

  // From test 3 (abcdefg/AbCdEfF → 1): key diff g>f, scaled to ("g","F") → CILessThan(t,s)
  expect CILessThan("F", "g"), "spec positive 3";

  // From test 4 (asadasdasd/asdwasdawd → -1): diff at pos 2 a<d, scaled to ("a","d")
  expect CILessThan("a", "d"), "spec positive 4";

  // From test 5 (aslkjlkasdd/asdlkjdajwi → 1): diff at pos 2 l>d, scaled to ("l","d") → CILessThan(t,s)
  expect CILessThan("d", "l"), "spec positive 5";

  // From test 6 (equal strings → 0): scaled to ("aa","aa")
  expect CIEqual("aa", "aa"), "spec positive 6";

  // From test 7 (mixed case equal → 0): scaled to ("aA","Aa")
  expect CIEqual("aA", "Aa"), "spec positive 7";

  // From test 8 (bwu.../Hho... → -1): diff at pos 0 b<h, scaled to ("b","h")
  expect CILessThan("b", "h"), "spec positive 8";

  // From test 9 (kGW.../cvO... → 1): diff at pos 0 k>c, scaled to ("k","c") → CILessThan(t,s)
  expect CILessThan("c", "k"), "spec positive 9";

  // From test 10 (nCe.../HJb... → 1): diff at pos 0 n>h, scaled to ("n","h") → CILessThan(t,s)
  expect CILessThan("h", "n"), "spec positive 10";

  // ===== SPEC NEGATIVE TESTS =====
  // Wrong outputs must be rejected. For wrong==W, the predicate that would need to hold for result==W must be false.
  // wrong==0 → !CIEqual, wrong==1 → !CILessThan(t,s), wrong==-1 → !CILessThan(s,t)
  // Neg cases with wrong==2 are skipped (2 is outside {-1,0,1} so no predicate maps to it).

  // From neg 1: (a/A) wrong=1 → CILessThan(t,s) should be false
  expect !CILessThan("A", "a"), "spec negative 1";

  // From neg 2: (s/z) wrong=0 → CIEqual should be false
  expect !CIEqual("s", "z"), "spec negative 2";

  // From neg 4: (a/d) wrong=0 → CIEqual should be false
  expect !CIEqual("a", "d"), "spec negative 4";

  // From neg 6: (aa/aa) wrong=1 → CILessThan(t,s) should be false
  expect !CILessThan("aa", "aa"), "spec negative 6";

  // From neg 7: (aA/Aa) wrong=1 → CILessThan(t,s) should be false
  expect !CILessThan("Aa", "aA"), "spec negative 7";

  // From neg 8: (b/h) wrong=0 → CIEqual should be false
  expect !CIEqual("b", "h"), "spec negative 8";

  // ===== IMPLEMENTATION TESTS =====
  // Full-size test pairs — the method is fast, no quantifier enumeration needed.

  r := PetyaAndStrings("aaaa", "aaaA");
  expect r == 0, "impl test 1 failed";

  r := PetyaAndStrings("abs", "Abz");
  expect r == -1, "impl test 2 failed";

  r := PetyaAndStrings("abcdefg", "AbCdEfF");
  expect r == 1, "impl test 3 failed";

  r := PetyaAndStrings("asadasdasd", "asdwasdawd");
  expect r == -1, "impl test 4 failed";

  r := PetyaAndStrings("aslkjlkasdd", "asdlkjdajwi");
  expect r == 1, "impl test 5 failed";

  r := PetyaAndStrings("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
  expect r == 0, "impl test 6 failed";

  r := PetyaAndStrings("aAaaaAAaAaaAzZsssSsdDfeEaeqZlpP", "AaaaAaaAaaAaZzSSSSsDdFeeAeQZLpp");
  expect r == 0, "impl test 7 failed";

  r := PetyaAndStrings("bwuEhEveouaTECagLZiqmUdxEmhRSOzMauJRWLQMppZOumxhAmwuGeDIkvkBLvMXwUoFmpAfDprBcFtEwOULcZWRQhcTbTbX", "HhoDWbcxwiMnCNexOsKsujLiSGcLllXOkRSbnOzThAjnnliLYFFmsYkOfpTxRNEfBsoUHfoLTiqAINRPxWRqrTJhgfkKcDOH");
  expect r == -1, "impl test 8 failed";

  r := PetyaAndStrings("kGWUuguKzcvxqKTNpxeDWXpXkrXDvGMFGoXKDfPBZvWSDUyIYBynbKOUonHvmZaKeirUhfmVRKtGhAdBfKMWXDUoqvbfpfHYcg", "cvOULleuIIiYVVxcLZmHVpNGXuEpzcWZZWyMOwIwbpkKPwCfkVbKkUuosvxYCKjqfVmHfJKbdrsAcatPYgrCABaFcoBuOmMfFt");
  expect r == 1, "impl test 9 failed";

  r := PetyaAndStrings("nCeNVIzHqPceNhjHeHvJvgBsNFiXBATRrjSTXJzhLMDMxiJztphxBRlDlqwDFImWeEPkggZCXSRwelOdpNrYnTepiOqpvkr", "HJbjJFtlvNxIbkKlxQUwmZHJFVNMwPAPDRslIoXISBYHHfymyIaQHLgECPxAmqnOCizwXnIUBRmpYUBVPenoUKhCobKdOjL");
  expect r == 1, "impl test 10 failed";

  r := PetyaAndStrings("ttXjenUAlfixytHEOrPkgXmkKTSGYuyVXGIHYmWWYGlBYpHkujueqBSgjLguSgiMGJWATIGEUjjAjKXdMiVbHozZUmqQtFrT", "JziDBFBDmDJCcGqFsQwDFBYdOidLxxhBCtScznnDgnsiStlWFnEXQrJxqTXKPxZyIGfLIToETKWZBPUIBmLeImrlSBWCkTNo");
  expect r == 1, "impl test 11 failed";

  r := PetyaAndStrings("AjQhPqSVhwQQjcgCycjKorWBgFCRuQBwgdVuAPSMJAvTyxGVuFHjfJzkKfsmfhFbKqFrFIohSZBbpjgEHebezmVlGLTPSCTMf", "XhxWuSnMmKFrCUOwkTUmvKAfbTbHWzzOTzxJatLLCdlGnHVaBUnxDlsqpvjLHMThOPAFBggVKDyKBrZAmjnjrhHlrnSkyzBja");
  expect r == -1, "impl test 12 failed";

  r := PetyaAndStrings("HCIgYtnqcMyjVngziNflxKHtdTmcRJhzMAjFAsNdWXFJYEhiTzsQUtFNkAbdrFBRmvLirkuirqTDvIpEfyiIqkrwsjvpPWTEdI", "ErqiiWKsmIjyZuzgTlTqxYZwlrpvRyaVhRTOYUqtPMVGGtWOkDCOOQRKrkkRzPftyQCkYkzKkzTPqqXmeZhvvEEiEhkdOmoMvy");
  expect r == 1, "impl test 13 failed";

  r := PetyaAndStrings("mtBeJYILXcECGyEVSyzLFdQJbiVnnfkbsYYsdUJSIRmyzLfTTtFwIBmRLVnwcewIqcuydkcLpflHAFyDaToLiFMgeHvQorTVbI", "ClLvyejznjbRfCDcrCzkLvqQaGzTjwmWONBdCctJAPJBcQrcYvHaSLQgPIJbmkFBhFzuQLBiRzAdNHulCjIAkBvZxxlkdzUWLR");
  expect r == 1, "impl test 14 failed";

  r := PetyaAndStrings("tjucSbGESVmVridTBjTmpVBCwwdWKBPeBvmgdxgIVLwQxveETnSdxkTVJpXoperWSgdpPMKNmwDiGeHfxnuqaDissgXPlMuNZIr", "HfjOOJhomqNIKHvqSgfySjlsWJQBuWYwhLQhlZYlpZwboMpoLoluGsBmhhlYgeIouwdkPfiaAIrkYRlxtiFazOPOllPsNZHcIZd");
  expect r == 1, "impl test 15 failed";

  r := PetyaAndStrings("AanbDfbZNlUodtBQlvPMyomStKNhgvSGhSbTdabxGFGGXCdpsJDimsAykKjfBDPMulkhBMsqLmVKLDoesHZsRAEEdEzqigueXInY", "cwfyjoppiJNrjrOLNZkqcGimrpTsiyFBVgMWEPXsMrxLJDDbtYzerXiFGuLBcQYitLdqhGHBpdjRnkUegmnwhGHAKXGyFtscWDSI");
  expect r == -1, "impl test 16 failed";

  r := PetyaAndStrings("HRfxniwuJCaHOcaOVgjOGHXKrwxrDQxJpppeGDXnTAowyKbCsCQPbchCKeTWOcKbySSYnoaTJDnmRcyGPbfXJyZoPcARHBu", "xkLXvwkvGIWSQaFTznLOctUXNuzzBBOlqvzmVfTSejekTAlwidRrsxkbZTsGGeEWxCXHzqWVuLGoCyrGjKkQoHqduXwYQKC");
  expect r == -1, "impl test 17 failed";

  r := PetyaAndStrings("OjYwwNuPESIazoyLFREpObIaMKhCaKAMWMfRGgucEuyNYRantwdwQkmflzfqbcFRaXBnZoIUGsFqXZHGKwlaBUXABBcQEWWPvkjW", "RxLqGcTTpBwHrHltCOllnTpRKLDofBUqqHxnOtVWPgvGaeHIevgUSOeeDOJubfqonFpVNGVbHFcAhjnyFvrrqnRgKhkYqQZmRfUl");
  expect r == -1, "impl test 18 failed";

  r := PetyaAndStrings("tatuhQPIzjptlzzJpCAPXSRTKZRlwgfoCIsFjJquRoIDyZZYRSPdFUTjjUPhLBBfeEIfLQpygKXRcyQFiQsEtRtLnZErBqW", "tkHUjllbafLUWhVCnvblKjgYIEoHhsjVmrDBmAWbvtkHxDbRFvsXAjHIrujaDbYwOZmacknhZPeCcorbRgHjjgAgoJdjvLo");
  expect r == -1, "impl test 19 failed";

  r := PetyaAndStrings("cymCPGqdXKUdADEWDdUaLEEMHiXHsdAZuDnJDMUvxvrLRBrPSDpXPAgMRoGplLtniFRTomDTAHXWAdgUveTxaqKVSvnOyhOwiRN", "uhmyEWzapiRNPFDisvHTbenXMfeZaHqOFlKjrfQjUBwdFktNpeiRoDWuBftZLcCZZAVfioOihZVNqiNCNDIsUdIhvbcaxpTRWoV");
  expect r == -1, "impl test 20 failed";

  print "All tests passed\n";
}