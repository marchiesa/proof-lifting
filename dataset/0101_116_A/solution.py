import sys

n = int(sys.stdin.readline().strip())

current = 0;
max = 0;
for i in xrange(n):
  a, b = map(int, sys.stdin.readline().strip().split())
  current = current - a + b
  if current > max:
    max = current

print(max)