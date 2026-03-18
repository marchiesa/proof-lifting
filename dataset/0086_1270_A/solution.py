def solve():
    n, k1, k2 = map(int, raw_input().split())
    a = map(int, raw_input().split())
    b = map(int, raw_input().split())
    print "YES" if max(a) > max(b) else "NO"
T = int(raw_input())
for _ in xrange(T):
    solve()