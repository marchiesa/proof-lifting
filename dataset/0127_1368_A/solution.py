import sys
input = sys.stdin.readline
t = int(input())
for _ in range(t):
  a,b,n = map(int,input().split())
  if a > b:
    a,b = b,a
  for i in range(1,1000):
    if i%2:
      a += b
    else:
      b += a
    if max(a,b) > n:
      print(i)
      break