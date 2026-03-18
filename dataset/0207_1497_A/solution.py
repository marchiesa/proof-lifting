import sys
input = sys.stdin.readline
for _ in range(int(input())):
  n = int(input())
  a = list(map(int, input().split()))
  s = set()
  res = []
  ss = []
  for i in range(n):
    x = a[i]
    if x in s: ss.append(x)
    else: res.append(x)
    s.add(x)
  res.sort()
  res += ss
  print(*res)