#CFR717-A-00
import sys;input = lambda: sys.stdin.readline().rstrip()
for _ in range(int(input())):
    n, k = map(int,input().split())
    A = list(map(int,input().split()))
    for i in range(n):
        if not k or i == n-1:
            break
        a = A[i]
        if k >= a:
            A[i] = 0
            k -= a
            A[-1] += a
        else:
            A[i] -= k
            A[-1] += k
            break
    print(*A)