def solve():
    a = input()
    n = len(a)
    i = 0
    b = []
    while i < n:
        j = i
        while j < n and a[i] == a[j]:
            j += 1
        if a[i] == '1':
            b.append(j - i)
        i = j
    b.sort(reverse=True)
    ans = 0
    for i in range(0, len(b), 2):
        ans += b[i]
    print(ans)

t = int(input())
for _ in range(t):
    solve()