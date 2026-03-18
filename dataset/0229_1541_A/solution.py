def solve(n):
    if not n:
        return []

    if n == 2:
        return [2, 1]

    if n == 3:
        return [3, 1, 2]

    return solve(n - 2) + [n, n - 1]

t = int(input())
for _ in range(t):
    n = int(input())
    res = solve(n)
    print(' '.join(str(x) for x in res))