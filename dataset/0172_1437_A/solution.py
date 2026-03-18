T = int(raw_input())
for _ in xrange(T):
    l, r = map(int, raw_input().split())
    print "NO" if l * 2 <= r else "YES"