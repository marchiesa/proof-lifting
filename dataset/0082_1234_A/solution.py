q = input()
for _ in xrange(q):
    n = input()
    a = map(int, raw_input().strip().split())
    s = sum(a)
    x = (s + n - 1) / n
    print x