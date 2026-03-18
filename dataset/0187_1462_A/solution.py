import sys
input = sys.stdin.readline
for _ in range(int(input())):
    n = int(input())
    b = [*map(int, input().split())]
    x = 1
    y = 0
    ns = []
    for a in range(n):
        if y == 0:
            ns.append(b[x - 1])
            y = 1
        else:
            ns.append(b[- x])
            x += 1
            y = 0
    print(*ns)