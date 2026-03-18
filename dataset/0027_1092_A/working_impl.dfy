method UniformString(n: int, k: int) returns (s: seq<char>)
{
  var pattern: seq<char> := [];
  var i := 0;
  while i < k {
    pattern := pattern + [('a' as int + i) as char];
    i := i + 1;
  }
  s := [];
  while |s| < n {
    s := s + pattern;
  }
  s := s[..n];
}

method Main() {
  // Test 1
  var s1 := UniformString(7, 3);
  expect s1 == "abcabca", "Test 1.1 failed";

  var s2 := UniformString(4, 4);
  expect s2 == "abcd", "Test 1.2 failed";

  var s3 := UniformString(6, 2);
  expect s3 == "ababab", "Test 1.3 failed";

  // Test 2: 66 identical cases of (1, 1) -> "a"
  var i := 0;
  while i < 66 {
    var s := UniformString(1, 1);
    expect s == "a", "Test 2 failed";
    i := i + 1;
  }

  print "All tests passed\n";
}