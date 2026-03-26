method BalancedArray(n: int) returns (possible: bool, a: seq<int>)
{
  if n % 4 == 2 {
    possible := false;
    a := [];
  } else {
    possible := true;
    var half := n / 2;
    var arr := new int[n];
    var i := 0;
    while i < half {
      arr[i] := 2 * (i + 1);
      i := i + 1;
    }
    i := 0;
    while i < half - 1 {
      arr[half + i] := 2 * i + 1;
      i := i + 1;
    }
    arr[n - 1] := 3 * half - 1;
    a := arr[..];
  }
}

method Main()
{
  var p, a: seq<int>;

  p, a := BalancedArray(2);
  expect !p, "n=2 should be NO";

  p, a := BalancedArray(4);
  expect p, "n=4 should be YES";
  expect a == [2, 4, 1, 5], "n=4 array mismatch";

  p, a := BalancedArray(6);
  expect !p, "n=6 should be NO";

  p, a := BalancedArray(8);
  expect p, "n=8 should be YES";
  expect a == [2, 4, 6, 8, 1, 3, 5, 11], "n=8 array mismatch";

  p, a := BalancedArray(10);
  expect !p, "n=10 should be NO";

  p, a := BalancedArray(200000);
  expect p, "n=200000 should be YES";
  expect |a| == 200000, "n=200000 length";
  expect a[0] == 2, "n=200000 first element";
  expect a[99999] == 200000, "n=200000 last even";
  expect a[100000] == 1, "n=200000 first odd";
  expect a[199999] == 299999, "n=200000 last element";

  p, a := BalancedArray(199998);
  expect !p, "n=199998 should be NO";

  p, a := BalancedArray(46340);
  expect p, "n=46340 should be YES";
  expect |a| == 46340, "n=46340 length";
  expect a[0] == 2, "n=46340 first element";
  expect a[23169] == 46340, "n=46340 last even";
  expect a[23170] == 1, "n=46340 first odd";
  expect a[46339] == 69509, "n=46340 last element";

  p, a := BalancedArray(7876);
  expect p, "n=7876 should be YES";
  expect |a| == 7876, "n=7876 length";
  expect a[0] == 2, "n=7876 first element";
  expect a[3937] == 7876, "n=7876 last even";
  expect a[3938] == 1, "n=7876 first odd";
  expect a[7875] == 11813, "n=7876 last element";

  print "All tests passed\n";
}