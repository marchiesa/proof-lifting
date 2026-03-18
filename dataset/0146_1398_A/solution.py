def check(u, v, w):
    x = u + v - w
    y = u - v + w
    z = -u + v + w
    return x <= 0 or y <= 0 or z <= 0

def solve():
    n = int(input())
    a = list(map(int, input().split()))
    if check(a[0], a[1], a[-1]):
        print(1, 2, n)
        return
    if check(a[0], a[-1], a[-2]):
        print(1, n - 1, n)
        return
    if check(a[0], a[1], a[2]):
        print(1, 2, 3)
        return
    if check(a[-3], a[-2], a[-1]):
        print(n - 2, n - 1, n)
        return
    print(-1)

t = int(input())
for _ in range(t):
    solve()