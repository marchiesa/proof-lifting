// Pascal's Triangle Row Computation -- Reference solution with invariants

function Choose(n: nat, k: nat): nat
  decreases n, k
{
  if k == 0 then 1
  else if n == 0 then 0
  else Choose(n-1, k-1) + Choose(n-1, k)
}

function PascalRow(n: nat): seq<nat>
{
  seq(n + 1, k requires 0 <= k <= n => Choose(n, k))
}

lemma PascalRowLength(n: nat)
  ensures |PascalRow(n)| == n + 1
{}

lemma PascalRecurrence(n: nat, k: nat)
  requires 0 < k <= n
  ensures Choose(n, k) == Choose(n-1, k-1) + Choose(n-1, k)
{}

lemma ChooseNN(n: nat)
  ensures Choose(n, n) == 1
  decreases n
{
  if n == 0 {
  } else {
    ChooseNN(n - 1);
    ChooseNNIsZero(n-1, n);
    assert Choose(n, n) == Choose(n-1, n-1) + Choose(n-1, n);
    assert Choose(n-1, n) == 0;
  }
}

lemma ChooseNNIsZero(n: nat, k: nat)
  requires k > n
  ensures Choose(n, k) == 0
  decreases n
{
  if n == 0 {
  } else {
    ChooseNNIsZero(n-1, k-1);
    ChooseNNIsZero(n-1, k);
  }
}

method ComputePascalRow(n: nat) returns (row: seq<nat>)
  ensures row == PascalRow(n)
{
  row := [1];
  var i: nat := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant row == PascalRow(i - 1)
    invariant |row| == i
    decreases n - i + 1
  {
    var newRow: seq<nat> := [1];
    var j: nat := 1;
    while j < i
      invariant 1 <= j <= i
      invariant |newRow| == j
      invariant newRow[0] == 1
      invariant forall k :: 0 < k < j ==> newRow[k] == row[k-1] + row[k]
      invariant forall k :: 0 < k < j ==> newRow[k] == Choose(i, k)
      decreases i - j
    {
      PascalRecurrence(i, j);
      newRow := newRow + [row[j-1] + row[j]];
      j := j + 1;
    }
    newRow := newRow + [1];
    assert |newRow| == i + 1;
    assert newRow[0] == 1 == Choose(i, 0);
    ChooseNN(i);
    assert newRow[i] == 1 == Choose(i, i);
    assert forall k :: 0 <= k <= i ==> newRow[k] == Choose(i, k);
    assert newRow == PascalRow(i);
    row := newRow;
    i := i + 1;
  }
}
