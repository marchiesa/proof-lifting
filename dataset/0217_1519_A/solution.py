T = int(raw_input())
for t in xrange(T):
    r, b, d = map(int, raw_input().split())
    if r > b:
        r, b = b, r
    print "YES" if r * (d + 1) >= b else "NO"