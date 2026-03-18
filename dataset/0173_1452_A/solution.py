for _ in range(int(input())):
    x, y = map(int, input().split())
    print(min(x, y) * 2 + max(0, abs(x - y) * 2 - 1))