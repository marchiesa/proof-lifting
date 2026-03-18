n, m = map(int, raw_input().split())
a = raw_input().split()
b = raw_input().split()
q = int(raw_input())
for _ in xrange(q):
    x = int(raw_input()) - 1
    print a[x%n] + b[x%m]