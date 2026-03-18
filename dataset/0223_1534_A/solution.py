t = int(input())
while t > 0:
    t -= 1
    n, m = map(int, input().split())
    a = [list(input()) for i in range(n)]
    w = 0
    for i in range(n):
        for j in range(m):
            if a[i][j] == 'R':
                w = (i + j) % 2
            elif a[i][j] == 'W':
                w = 1 - (i + j) % 2
    bad = False
    for i in range(n):
        for j in range(m):
            c = 'R' if (i + j) % 2 == w else 'W'
            if a[i][j] != '.' and c != a[i][j]:
                bad = True
            a[i][j] = c
    if bad:
        print('NO')
    else:
        print('YES')
        print(*(''.join(a[i]) for i in range(n)), sep='\n')