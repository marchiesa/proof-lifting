# Matrix Multiplication

## Description

Given two matrices represented as `seq<seq<int>>`, compute their product.
Matrix A is m x n and matrix B is n x p, producing an m x p result matrix.

## Input

- `A`: an m x n matrix (seq<seq<int>> where each row has length n)
- `B`: an n x p matrix (seq<seq<int>> where each row has length p)

## Output

A matrix `C` (seq<seq<int>>) such that:
- `|C| == |A|` (m rows)
- Each row of C has length p
- `C[i][j] == sum of A[i][k] * B[k][j]` for k from 0 to n-1

## Examples

- `MatMul([[1,2],[3,4]], [[5,6],[7,8]])` returns `[[19,22],[43,50]]`
- `MatMul([[1,0],[0,1]], [[5,6],[7,8]])` returns `[[5,6],[7,8]]` (identity)
