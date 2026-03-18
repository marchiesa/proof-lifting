for _ in range(int(input())):
    open_count = [0, 0]
    ans = 0
    for c in input():
        i = int(c in '[]')
        if c in '([':  # ])
            open_count[i] += 1
        elif open_count[i]:
            open_count[i] -= 1
            ans += 1
    print(ans)