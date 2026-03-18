a, b, c = map(int, input().split())
m = max(a, b, c)
print(max(0, m - a - b - c + m + 1))