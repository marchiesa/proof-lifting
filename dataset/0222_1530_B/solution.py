def solve(r, c):
    a = [[0] * m for _ in range(n)]
    a[r][c] = 1
    for i in range(m):
        if a[0][i] == 1 or (i > 0 and a[0][i - 1] == 1) or (i + 1 < m and a[0][i + 1] == 1):
            continue
        a[0][i] = 1

    for i in range(1, n):
        if a[i][m - 1] == 1 or (i > 0 and a[i - 1][m - 1] == 1) or (i > 0 and a[i - 1][m - 2] == 1):
            continue
        a[i][m - 1] = 1

    for i in reversed(range(m - 1)):
        if a[n - 1][i] == 1 or (i > 0 and a[n - 1][i - 1] == 1) or (i + 1 < m and a[n - 1][i + 1] == 1) or (
                i + 1 < m and a[n - 2][i + 1] == 1):
            continue
        a[n - 1][i] = 1

    for i in reversed(range(1, n - 1)):
        if a[i][0] == 1 or (i > 0 and a[i - 1][0] == 1) or (i > 0 and a[i - 1][1] == 1) or (
                i < n - 1 and a[i + 1][0] == 1) or (i < n - 1 and a[i + 1][1] == 1):
            continue
        a[i][0] = 1
    ans = 0
    for i in range(n):
        ans += sum(a[i])

    return a, ans


for _ in range(int(input())):
    n, m = [int(x) for x in input().split()]
    a1, ans1 = solve(0, 0)
    a2, ans2 = solve(0, 1)

    if ans1 > ans2:
        for i in range(n):
            print("".join(map(str, a1[i])))
    else:
        for i in range(n):
            print("".join(map(str, a2[i])))

    print()