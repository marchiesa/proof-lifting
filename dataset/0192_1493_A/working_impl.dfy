method AntiKnapsack(n: int, k: int) returns (chosen: seq<int>)
{
  chosen := [];
  var i := k + 1;
  while i <= n {
    chosen := chosen + [i];
    i := i + 1;
  }
  i := (k + 1) / 2;
  while i <= k - 1 {
    chosen := chosen + [i];
    i := i + 1;
  }
}

method TestAntiKnapsack(n: int, k: int, expected: seq<int>)
{
  var chosen := AntiKnapsack(n, k);
  expect chosen == expected;
}

method Main()
{
  // n=1
  TestAntiKnapsack(1, 1, []);

  // n=2
  TestAntiKnapsack(2, 1, [2]);
  TestAntiKnapsack(2, 2, [1]);

  // n=3
  TestAntiKnapsack(3, 1, [2, 3]);
  TestAntiKnapsack(3, 2, [3, 1]);
  TestAntiKnapsack(3, 3, [2]);

  // n=4
  TestAntiKnapsack(4, 1, [2, 3, 4]);
  TestAntiKnapsack(4, 2, [3, 4, 1]);
  TestAntiKnapsack(4, 3, [4, 2]);
  TestAntiKnapsack(4, 4, [2, 3]);

  // n=5
  TestAntiKnapsack(5, 1, [2, 3, 4, 5]);
  TestAntiKnapsack(5, 2, [3, 4, 5, 1]);
  TestAntiKnapsack(5, 3, [4, 5, 2]);
  TestAntiKnapsack(5, 4, [5, 2, 3]);
  TestAntiKnapsack(5, 5, [3, 4]);

  // n=6
  TestAntiKnapsack(6, 1, [2, 3, 4, 5, 6]);
  TestAntiKnapsack(6, 2, [3, 4, 5, 6, 1]);
  TestAntiKnapsack(6, 3, [4, 5, 6, 2]);
  TestAntiKnapsack(6, 4, [5, 6, 2, 3]);
  TestAntiKnapsack(6, 5, [6, 3, 4]);
  TestAntiKnapsack(6, 6, [3, 4, 5]);

  // n=7
  TestAntiKnapsack(7, 1, [2, 3, 4, 5, 6, 7]);
  TestAntiKnapsack(7, 2, [3, 4, 5, 6, 7, 1]);
  TestAntiKnapsack(7, 3, [4, 5, 6, 7, 2]);
  TestAntiKnapsack(7, 4, [5, 6, 7, 2, 3]);
  TestAntiKnapsack(7, 5, [6, 7, 3, 4]);
  TestAntiKnapsack(7, 6, [7, 3, 4, 5]);
  TestAntiKnapsack(7, 7, [4, 5, 6]);

  // n=8
  TestAntiKnapsack(8, 1, [2, 3, 4, 5, 6, 7, 8]);
  TestAntiKnapsack(8, 2, [3, 4, 5, 6, 7, 8, 1]);
  TestAntiKnapsack(8, 3, [4, 5, 6, 7, 8, 2]);
  TestAntiKnapsack(8, 4, [5, 6, 7, 8, 2, 3]);
  TestAntiKnapsack(8, 5, [6, 7, 8, 3, 4]);
  TestAntiKnapsack(8, 6, [7, 8, 3, 4, 5]);
  TestAntiKnapsack(8, 7, [8, 4, 5, 6]);
  TestAntiKnapsack(8, 8, [4, 5, 6, 7]);

  // n=9
  TestAntiKnapsack(9, 1, [2, 3, 4, 5, 6, 7, 8, 9]);
  TestAntiKnapsack(9, 2, [3, 4, 5, 6, 7, 8, 9, 1]);
  TestAntiKnapsack(9, 3, [4, 5, 6, 7, 8, 9, 2]);
  TestAntiKnapsack(9, 4, [5, 6, 7, 8, 9, 2, 3]);
  TestAntiKnapsack(9, 5, [6, 7, 8, 9, 3, 4]);
  TestAntiKnapsack(9, 6, [7, 8, 9, 3, 4, 5]);
  TestAntiKnapsack(9, 7, [8, 9, 4, 5, 6]);
  TestAntiKnapsack(9, 8, [9, 4, 5, 6, 7]);
  TestAntiKnapsack(9, 9, [5, 6, 7, 8]);

  // n=10
  TestAntiKnapsack(10, 1, [2, 3, 4, 5, 6, 7, 8, 9, 10]);
  TestAntiKnapsack(10, 2, [3, 4, 5, 6, 7, 8, 9, 10, 1]);
  TestAntiKnapsack(10, 3, [4, 5, 6, 7, 8, 9, 10, 2]);
  TestAntiKnapsack(10, 4, [5, 6, 7, 8, 9, 10, 2, 3]);
  TestAntiKnapsack(10, 5, [6, 7, 8, 9, 10, 3, 4]);
  TestAntiKnapsack(10, 6, [7, 8, 9, 10, 3, 4, 5]);
  TestAntiKnapsack(10, 7, [8, 9, 10, 4, 5, 6]);
  TestAntiKnapsack(10, 8, [9, 10, 4, 5, 6, 7]);
  TestAntiKnapsack(10, 9, [10, 5, 6, 7, 8]);
  TestAntiKnapsack(10, 10, [5, 6, 7, 8, 9]);

  // n=15
  TestAntiKnapsack(15, 1, [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]);
  TestAntiKnapsack(15, 2, [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 1]);
  TestAntiKnapsack(15, 3, [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 2]);
  TestAntiKnapsack(15, 4, [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 2, 3]);
  TestAntiKnapsack(15, 5, [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 3, 4]);
  TestAntiKnapsack(15, 6, [7, 8, 9, 10, 11, 12, 13, 14, 15, 3, 4, 5]);
  TestAntiKnapsack(15, 7, [8, 9, 10, 11, 12, 13, 14, 15, 4, 5, 6]);
  TestAntiKnapsack(15, 8, [9, 10, 11, 12, 13, 14, 15, 4, 5, 6, 7]);
  TestAntiKnapsack(15, 9, [10, 11, 12, 13, 14, 15, 5, 6, 7, 8]);
  TestAntiKnapsack(15, 10, [11, 12, 13, 14, 15, 5, 6, 7, 8, 9]);
  TestAntiKnapsack(15, 11, [12, 13, 14, 15, 6, 7, 8, 9, 10]);
  TestAntiKnapsack(15, 12, [13, 14, 15, 6, 7, 8, 9, 10, 11]);
  TestAntiKnapsack(15, 13, [14, 15, 7, 8, 9, 10, 11, 12]);
  TestAntiKnapsack(15, 14, [15, 7, 8, 9, 10, 11, 12, 13]);
  TestAntiKnapsack(15, 15, [8, 9, 10, 11, 12, 13, 14]);

  // Larger cases
  TestAntiKnapsack(20, 11, [12, 13, 14, 15, 16, 17, 18, 19, 20, 6, 7, 8, 9, 10]);
  TestAntiKnapsack(30, 15, [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 8, 9, 10, 11, 12, 13, 14]);
  TestAntiKnapsack(50, 25, [26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]);

  print "All tests passed\n";
}