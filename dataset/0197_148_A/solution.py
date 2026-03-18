import sys

k, l, m, n, d = [int(s) for s in sys.stdin.read().split()]

c = 0
for i in xrange(1, d + 1):
    c += 1 if i % k == 0 or i % l == 0 or i % m == 0 or i % n == 0 else 0

print c