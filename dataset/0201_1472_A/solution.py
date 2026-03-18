import sys
input = sys.stdin.readline
for _ in range(int(input())):
    w, h, n = map(int, input().split())
    cnt = 1
    while not w % 2:
        cnt *= 2
        w //= 2
    while not h % 2:
        cnt *= 2
        h //= 2
    print("YES" if cnt >= n else "NO")