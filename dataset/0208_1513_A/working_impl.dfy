method ArrayAndPeaks(n: int, k: int) returns (result: seq<int>, possible: bool)
{
  var ma := (n - 1) / 2;
  if k > ma || k < 0 || n < 1 {
    result := [];
    possible := false;
  } else {
    var ans := new int[n];
    var idx := 0;
    while idx < n {
      ans[idx] := 0;
      idx := idx + 1;
    }

    var c := 0;
    var i := 1;
    while i < n && c < k {
      ans[i] := n - c;
      c := c + 1;
      i := i + 2;
    }

    var j := 1;
    i := 0;
    while i < n {
      if ans[i] == 0 {
        ans[i] := j;
        j := j + 1;
      }
      i := i + 1;
    }

    result := ans[..];
    possible := true;
  }
}

method Main()
{
  // Test 1
  {
    var r, p := ArrayAndPeaks(1, 0);
    expect p == true, "Test 1.1: expected possible";
    expect r == [1], "Test 1.1: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(5, 2);
    expect p == true, "Test 1.2: expected possible";
    expect r == [1, 5, 2, 4, 3], "Test 1.2: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(6, 6);
    expect p == false, "Test 1.3: expected impossible";
  }
  {
    var r, p := ArrayAndPeaks(2, 1);
    expect p == false, "Test 1.4: expected impossible";
  }
  {
    var r, p := ArrayAndPeaks(6, 1);
    expect p == true, "Test 1.5: expected possible";
    expect r == [1, 6, 2, 3, 4, 5], "Test 1.5: wrong result";
  }

  // Test 2
  {
    var r, p := ArrayAndPeaks(79, 29);
    expect p == true, "Test 2.1: expected possible";
    expect r == [1, 79, 2, 78, 3, 77, 4, 76, 5, 75, 6, 74, 7, 73, 8, 72, 9, 71, 10, 70, 11, 69, 12, 68, 13, 67, 14, 66, 15, 65, 16, 64, 17, 63, 18, 62, 19, 61, 20, 60, 21, 59, 22, 58, 23, 57, 24, 56, 25, 55, 26, 54, 27, 53, 28, 52, 29, 51, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50], "Test 2.1: wrong result";
  }

  // Test 3
  {
    var r, p := ArrayAndPeaks(3, 1);
    expect p == true, "Test 3.1: expected possible";
    expect r == [1, 3, 2], "Test 3.1: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(4, 1);
    expect p == true, "Test 3.2: expected possible";
    expect r == [1, 4, 2, 3], "Test 3.2: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(5, 0);
    expect p == true, "Test 3.3: expected possible";
    expect r == [1, 2, 3, 4, 5], "Test 3.3: wrong result";
  }

  // Test 4
  {
    var r, p := ArrayAndPeaks(1, 0);
    expect p == true, "Test 4.1: expected possible";
    expect r == [1], "Test 4.1: wrong result";
  }

  // Test 5
  {
    var r, p := ArrayAndPeaks(10, 3);
    expect p == true, "Test 5.1: expected possible";
    expect r == [1, 10, 2, 9, 3, 8, 4, 5, 6, 7], "Test 5.1: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(7, 2);
    expect p == true, "Test 5.2: expected possible";
    expect r == [1, 7, 2, 6, 3, 4, 5], "Test 5.2: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(3, 0);
    expect p == true, "Test 5.3: expected possible";
    expect r == [1, 2, 3], "Test 5.3: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(8, 1);
    expect p == true, "Test 5.4: expected possible";
    expect r == [1, 8, 2, 3, 4, 5, 6, 7], "Test 5.4: wrong result";
  }

  // Test 6
  {
    var r, p := ArrayAndPeaks(5, 3);
    expect p == false, "Test 6.1: expected impossible";
  }
  {
    var r, p := ArrayAndPeaks(2, 0);
    expect p == true, "Test 6.2: expected possible";
    expect r == [1, 2], "Test 6.2: wrong result";
  }

  // Test 7
  {
    var r, p := ArrayAndPeaks(6, 2);
    expect p == true, "Test 7.1: expected possible";
    expect r == [1, 6, 2, 5, 3, 4], "Test 7.1: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(4, 0);
    expect p == true, "Test 7.2: expected possible";
    expect r == [1, 2, 3, 4], "Test 7.2: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(9, 4);
    expect p == true, "Test 7.3: expected possible";
    expect r == [1, 9, 2, 8, 3, 7, 4, 6, 5], "Test 7.3: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(3, 1);
    expect p == true, "Test 7.4: expected possible";
    expect r == [1, 3, 2], "Test 7.4: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(7, 3);
    expect p == true, "Test 7.5: expected possible";
    expect r == [1, 7, 2, 6, 3, 5, 4], "Test 7.5: wrong result";
  }

  // Test 8
  {
    var r, p := ArrayAndPeaks(50, 10);
    expect p == true, "Test 8.1: expected possible";
    expect r == [1, 50, 2, 49, 3, 48, 4, 47, 5, 46, 6, 45, 7, 44, 8, 43, 9, 42, 10, 41, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40], "Test 8.1: wrong result";
  }

  // Test 9
  {
    var r, p := ArrayAndPeaks(1, 1);
    expect p == false, "Test 9.1: expected impossible";
  }
  {
    var r, p := ArrayAndPeaks(2, 0);
    expect p == true, "Test 9.2: expected possible";
    expect r == [1, 2], "Test 9.2: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(4, 1);
    expect p == true, "Test 9.3: expected possible";
    expect r == [1, 4, 2, 3], "Test 9.3: wrong result";
  }

  // Test 10
  {
    var r, p := ArrayAndPeaks(8, 3);
    expect p == true, "Test 10.1: expected possible";
    expect r == [1, 8, 2, 7, 3, 6, 4, 5], "Test 10.1: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(10, 0);
    expect p == true, "Test 10.2: expected possible";
    expect r == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10], "Test 10.2: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(5, 1);
    expect p == true, "Test 10.3: expected possible";
    expect r == [1, 5, 2, 3, 4], "Test 10.3: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(12, 5);
    expect p == true, "Test 10.4: expected possible";
    expect r == [1, 12, 2, 11, 3, 10, 4, 9, 5, 8, 6, 7], "Test 10.4: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(6, 0);
    expect p == true, "Test 10.5: expected possible";
    expect r == [1, 2, 3, 4, 5, 6], "Test 10.5: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(3, 0);
    expect p == true, "Test 10.6: expected possible";
    expect r == [1, 2, 3], "Test 10.6: wrong result";
  }

  // Test 11
  {
    var r, p := ArrayAndPeaks(15, 7);
    expect p == true, "Test 11.1: expected possible";
    expect r == [1, 15, 2, 14, 3, 13, 4, 12, 5, 11, 6, 10, 7, 9, 8], "Test 11.1: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(20, 5);
    expect p == true, "Test 11.2: expected possible";
    expect r == [1, 20, 2, 19, 3, 18, 4, 17, 5, 16, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], "Test 11.2: wrong result";
  }

  // Test 12
  {
    var r, p := ArrayAndPeaks(7, 0);
    expect p == true, "Test 12.1: expected possible";
    expect r == [1, 2, 3, 4, 5, 6, 7], "Test 12.1: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(9, 2);
    expect p == true, "Test 12.2: expected possible";
    expect r == [1, 9, 2, 8, 3, 4, 5, 6, 7], "Test 12.2: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(11, 5);
    expect p == true, "Test 12.3: expected possible";
    expect r == [1, 11, 2, 10, 3, 9, 4, 8, 5, 7, 6], "Test 12.3: wrong result";
  }
  {
    var r, p := ArrayAndPeaks(4, 4);
    expect p == false, "Test 12.4: expected impossible";
  }

  print "All tests passed\n";
}