T = int(raw_input())
for t in xrange(T):
    n, m, k = map(int, raw_input().split())
    k -= 1 * (m - 1) + m * (n - 1)
    print "NO" if k else "YES"