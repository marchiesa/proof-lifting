method DejaVu(s: string) returns (possible: bool, result: string)
{
  // Check if all characters are 'a'
  var allA := true;
  var i := 0;
  while i < |s| && allA {
    if s[i] != 'a' {
      allA := false;
    }
    i := i + 1;
  }

  if allA {
    possible := false;
    result := "";
    return;
  }

  // Check if s + "a" is a palindrome
  var sa := s + "a";
  var isPalin := true;
  var j := 0;
  while j < |sa| / 2 && isPalin {
    if sa[j] != sa[|sa| - 1 - j] {
      isPalin := false;
    }
    j := j + 1;
  }

  if isPalin {
    possible := true;
    result := "a" + s;
  } else {
    possible := true;
    result := s + "a";
  }
}

method Main()
{
  // Test 1
  var p1, r1 := DejaVu("cbabc");
  expect p1 == true, "Test cbabc: expected YES";
  expect r1 == "cbabca", "Test cbabc: expected cbabca, got " + r1;

  var p2, r2 := DejaVu("ab");
  expect p2 == true, "Test ab: expected YES";
  expect r2 == "aab", "Test ab: expected aab, got " + r2;

  var p3, r3 := DejaVu("zza");
  expect p3 == true, "Test zza: expected YES";
  expect r3 == "zzaa", "Test zza: expected zzaa, got " + r3;

  var p4, r4 := DejaVu("ba");
  expect p4 == true, "Test ba: expected YES";
  expect r4 == "baa", "Test ba: expected baa, got " + r4;

  var p5, r5 := DejaVu("a");
  expect p5 == false, "Test a: expected NO";

  var p6, r6 := DejaVu("nutforajaroftuna");
  expect p6 == true, "Test nutforajaroftuna: expected YES";
  expect r6 == "nutforajaroftunaa", "Test nutforajaroftuna: expected nutforajaroftunaa, got " + r6;

  // Test 2
  var p7, r7 := DejaVu("aba");
  expect p7 == true, "Test aba: expected YES";
  expect r7 == "abaa", "Test aba: expected abaa, got " + r7;

  // "a" already tested above
  // "ab" already tested above

  // Test 3
  var p8, r8 := DejaVu("aaa");
  expect p8 == false, "Test aaa: expected NO";

  var p9, r9 := DejaVu("aaaa");
  expect p9 == false, "Test aaaa: expected NO";

  // Test 4
  var p10, r10 := DejaVu("z");
  expect p10 == true, "Test z: expected YES";
  expect r10 == "za", "Test z: expected za, got " + r10;

  // Test 5
  var p11, r11 := DejaVu("b");
  expect p11 == true, "Test b: expected YES";
  expect r11 == "ba", "Test b: expected ba, got " + r11;

  // "ba" already tested above
  // "ab" already tested above

  var p12, r12 := DejaVu("bb");
  expect p12 == true, "Test bb: expected YES";
  expect r12 == "bba", "Test bb: expected bba, got " + r12;

  // Test 6
  var p13, r13 := DejaVu("abc");
  expect p13 == true, "Test abc: expected YES";
  expect r13 == "abca", "Test abc: expected abca, got " + r13;

  var p14, r14 := DejaVu("cba");
  expect p14 == true, "Test cba: expected YES";
  expect r14 == "cbaa", "Test cba: expected cbaa, got " + r14;

  // "aba" already tested above

  var p15, r15 := DejaVu("aab");
  expect p15 == true, "Test aab: expected YES";
  expect r15 == "aaba", "Test aab: expected aaba, got " + r15;

  var p16, r16 := DejaVu("baa");
  expect p16 == true, "Test baa: expected YES";
  expect r16 == "baaa", "Test baa: expected baaa, got " + r16;

  // Test 7
  var p17, r17 := DejaVu("xx");
  expect p17 == true, "Test xx: expected YES";
  expect r17 == "xxa", "Test xx: expected xxa, got " + r17;

  var p18, r18 := DejaVu("xyx");
  expect p18 == true, "Test xyx: expected YES";
  expect r18 == "xyxa", "Test xyx: expected xyxa, got " + r18;

  // Test 8
  var p19, r19 := DejaVu("abcba");
  expect p19 == true, "Test abcba: expected YES";
  expect r19 == "abcbaa", "Test abcba: expected abcbaa, got " + r19;

  var p20, r20 := DejaVu("aa");
  expect p20 == false, "Test aa: expected NO";

  // "aba" already tested above

  // Test 9
  var p21, r21 := DejaVu("racecar");
  expect p21 == true, "Test racecar: expected YES";
  expect r21 == "racecara", "Test racecar: expected racecara, got " + r21;

  // Test 10
  // "a", "aa", "aaa" already tested above
  // "b" already tested above

  // Test 11
  var p22, r22 := DejaVu("mm");
  expect p22 == true, "Test mm: expected YES";
  expect r22 == "mma", "Test mm: expected mma, got " + r22;

  // "aba" already tested above

  var p23, r23 := DejaVu("xy");
  expect p23 == true, "Test xy: expected YES";
  expect r23 == "xya", "Test xy: expected xya, got " + r23;

  print "All tests passed\n";
}