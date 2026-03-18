method PetyaAndStrings(s: seq<char>, t: seq<char>) returns (result: int)
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

  r := PetyaAndStrings("aaaa", "aaaA");
  expect r == 0, "Test 1 failed";

  r := PetyaAndStrings("abs", "Abz");
  expect r == -1, "Test 2 failed";

  r := PetyaAndStrings("abcdefg", "AbCdEfF");
  expect r == 1, "Test 3 failed";

  r := PetyaAndStrings("asadasdasd", "asdwasdawd");
  expect r == -1, "Test 4 failed";

  r := PetyaAndStrings("aslkjlkasdd", "asdlkjdajwi");
  expect r == 1, "Test 5 failed";

  r := PetyaAndStrings("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
  expect r == 0, "Test 6 failed";

  r := PetyaAndStrings("aAaaaAAaAaaAzZsssSsdDfeEaeqZlpP", "AaaaAaaAaaAaZzSSSSsDdFeeAeQZLpp");
  expect r == 0, "Test 7 failed";

  r := PetyaAndStrings("bwuEhEveouaTECagLZiqmUdxEmhRSOzMauJRWLQMppZOumxhAmwuGeDIkvkBLvMXwUoFmpAfDprBcFtEwOULcZWRQhcTbTbX", "HhoDWbcxwiMnCNexOsKsujLiSGcLllXOkRSbnOzThAjnnliLYFFmsYkOfpTxRNEfBsoUHfoLTiqAINRPxWRqrTJhgfkKcDOH");
  expect r == -1, "Test 8 failed";

  r := PetyaAndStrings("kGWUuguKzcvxqKTNpxeDWXpXkrXDvGMFGoXKDfPBZvWSDUyIYBynbKOUonHvmZaKeirUhfmVRKtGhAdBfKMWXDUoqvbfpfHYcg", "cvOULleuIIiYVVxcLZmHVpNGXuEpzcWZZWyMOwIwbpkKPwCfkVbKkUuosvxYCKjqfVmHfJKbdrsAcatPYgrCABaFcoBuOmMfFt");
  expect r == 1, "Test 9 failed";

  r := PetyaAndStrings("nCeNVIzHqPceNhjHeHvJvgBsNFiXBATRrjSTXJzhLMDMxiJztphxBRlDlqwDFImWeEPkggZCXSRwelOdpNrYnTepiOqpvkr", "HJbjJFtlvNxIbkKlxQUwmZHJFVNMwPAPDRslIoXISBYHHfymyIaQHLgECPxAmqnOCizwXnIUBRmpYUBVPenoUKhCobKdOjL");
  expect r == 1, "Test 10 failed";

  r := PetyaAndStrings("ttXjenUAlfixytHEOrPkgXmkKTSGYuyVXGIHYmWWYGlBYpHkujueqBSgjLguSgiMGJWATIGEUjjAjKXdMiVbHozZUmqQtFrT", "JziDBFBDmDJCcGqFsQwDFBYdOidLxxhBCtScznnDgnsiStlWFnEXQrJxqTXKPxZyIGfLIToETKWZBPUIBmLeImrlSBWCkTNo");
  expect r == 1, "Test 11 failed";

  r := PetyaAndStrings("AjQhPqSVhwQQjcgCycjKorWBgFCRuQBwgdVuAPSMJAvTyxGVuFHjfJzkKfsmfhFbKqFrFIohSZBbpjgEHebezmVlGLTPSCTMf", "XhxWuSnMmKFrCUOwkTUmvKAfbTbHWzzOTzxJatLLCdlGnHVaBUnxDlsqpvjLHMThOPAFBggVKDyKBrZAmjnjrhHlrnSkyzBja");
  expect r == -1, "Test 12 failed";

  r := PetyaAndStrings("HCIgYtnqcMyjVngziNflxKHtdTmcRJhzMAjFAsNdWXFJYEhiTzsQUtFNkAbdrFBRmvLirkuirqTDvIpEfyiIqkrwsjvpPWTEdI", "ErqiiWKsmIjyZuzgTlTqxYZwlrpvRyaVhRTOYUqtPMVGGtWOkDCOOQRKrkkRzPftyQCkYkzKkzTPqqXmeZhvvEEiEhkdOmoMvy");
  expect r == 1, "Test 13 failed";

  r := PetyaAndStrings("mtBeJYILXcECGyEVSyzLFdQJbiVnnfkbsYYsdUJSIRmyzLfTTtFwIBmRLVnwcewIqcuydkcLpflHAFyDaToLiFMgeHvQorTVbI", "ClLvyejznjbRfCDcrCzkLvqQaGzTjwmWONBdCctJAPJBcQrcYvHaSLQgPIJbmkFBhFzuQLBiRzAdNHulCjIAkBvZxxlkdzUWLR");
  expect r == 1, "Test 14 failed";

  r := PetyaAndStrings("tjucSbGESVmVridTBjTmpVBCwwdWKBPeBvmgdxgIVLwQxveETnSdxkTVJpXoperWSgdpPMKNmwDiGeHfxnuqaDissgXPlMuNZIr", "HfjOOJhomqNIKHvqSgfySjlsWJQBuWYwhLQhlZYlpZwboMpoLoluGsBmhhlYgeIouwdkPfiaAIrkYRlxtiFazOPOllPsNZHcIZd");
  expect r == 1, "Test 15 failed";

  r := PetyaAndStrings("AanbDfbZNlUodtBQlvPMyomStKNhgvSGhSbTdabxGFGGXCdpsJDimsAykKjfBDPMulkhBMsqLmVKLDoesHZsRAEEdEzqigueXInY", "cwfyjoppiJNrjrOLNZkqcGimrpTsiyFBVgMWEPXsMrxLJDDbtYzerXiFGuLBcQYitLdqhGHBpdjRnkUegmnwhGHAKXGyFtscWDSI");
  expect r == -1, "Test 16 failed";

  r := PetyaAndStrings("HRfxniwuJCaHOcaOVgjOGHXKrwxrDQxJpppeGDXnTAowyKbCsCQPbchCKeTWOcKbySSYnoaTJDnmRcyGPbfXJyZoPcARHBu", "xkLXvwkvGIWSQaFTznLOctUXNuzzBBOlqvzmVfTSejekTAlwidRrsxkbZTsGGeEWxCXHzqWVuLGoCyrGjKkQoHqduXwYQKC");
  expect r == -1, "Test 17 failed";

  r := PetyaAndStrings("OjYwwNuPESIazoyLFREpObIaMKhCaKAMWMfRGgucEuyNYRantwdwQkmflzfqbcFRaXBnZoIUGsFqXZHGKwlaBUXABBcQEWWPvkjW", "RxLqGcTTpBwHrHltCOllnTpRKLDofBUqqHxnOtVWPgvGaeHIevgUSOeeDOJubfqonFpVNGVbHFcAhjnyFvrrqnRgKhkYqQZmRfUl");
  expect r == -1, "Test 18 failed";

  r := PetyaAndStrings("tatuhQPIzjptlzzJpCAPXSRTKZRlwgfoCIsFjJquRoIDyZZYRSPdFUTjjUPhLBBfeEIfLQpygKXRcyQFiQsEtRtLnZErBqW", "tkHUjllbafLUWhVCnvblKjgYIEoHhsjVmrDBmAWbvtkHxDbRFvsXAjHIrujaDbYwOZmacknhZPeCcorbRgHjjgAgoJdjvLo");
  expect r == -1, "Test 19 failed";

  r := PetyaAndStrings("cymCPGqdXKUdADEWDdUaLEEMHiXHsdAZuDnJDMUvxvrLRBrPSDpXPAgMRoGplLtniFRTomDTAHXWAdgUveTxaqKVSvnOyhOwiRN", "uhmyEWzapiRNPFDisvHTbenXMfeZaHqOFlKjrfQjUBwdFktNpeiRoDWuBftZLcCZZAVfioOihZVNqiNCNDIsUdIhvbcaxpTRWoV");
  expect r == -1, "Test 20 failed";

  print "All tests passed\n";
}