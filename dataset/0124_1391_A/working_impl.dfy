method GoodPermutation(n: int) returns (p: seq<int>)
{
  p := [];
  var i := 1;
  while i <= n
  {
    p := p + [i];
    i := i + 1;
  }
}

method ExpectedPermutation(n: int) returns (e: seq<int>)
{
  e := [];
  var i := 1;
  while i <= n
  {
    e := e + [i];
    i := i + 1;
  }
}

method Main()
{
  var p: seq<int>;
  var e: seq<int>;

  // Test 1: inputs 1, 3, 7
  p := GoodPermutation(1);
  e := ExpectedPermutation(1);
  expect p == e, "Failed for n=1 (Test 1)";

  p := GoodPermutation(3);
  e := ExpectedPermutation(3);
  expect p == e, "Failed for n=3 (Test 1)";

  p := GoodPermutation(7);
  e := ExpectedPermutation(7);
  expect p == e, "Failed for n=7 (Test 1)";

  // Test 2: inputs 1..100
  var i := 1;
  while i <= 100
  {
    p := GoodPermutation(i);
    e := ExpectedPermutation(i);
    var s := ToString(i);
    expect p == e, "Failed for Test 2, n=" + s;
    i := i + 1;
  }

  // Test 3: n=77
  p := GoodPermutation(77);
  e := ExpectedPermutation(77);
  expect p == e, "Failed for n=77 (Test 3)";

  // Test 4: n=57
  p := GoodPermutation(57);
  e := ExpectedPermutation(57);
  expect p == e, "Failed for n=57 (Test 4)";

  print "All tests passed\n";
}

method ToString(n: int) returns (s: string)
{
  if n == 0 { return "0"; }
  s := "";
  var val := n;
  if val < 0 { val := -val; }
  while val > 0
  {
    s := [(val % 10) as char + '0'] + s;
    val := val / 10;
  }
  if n < 0 { s := "-" + s; }
}