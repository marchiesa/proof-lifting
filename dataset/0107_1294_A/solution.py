t = int(input())
for _ in range(t):
    a, b, c, n = map(int, input().split())
    tot = a + b + c + n
    if tot % 3:
        print('NO')
    else:
        des = tot // 3
        if a > des or b > des or c > des:
            print('NO')
        else:
            print('YES')