n = int(raw_input())
a = map(int, raw_input().split())
ans = 0
a.sort()
for i, x in enumerate(a):
    if not x:
        continue
    for j in xrange(i, n):
        if a[j] % x == 0:
            a[j] = 0
    ans += 1
print ans