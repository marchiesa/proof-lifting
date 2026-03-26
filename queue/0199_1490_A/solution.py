for _ in range(int(input())):
    n = int(input())
    arr = list(map(int, input().split()))
    l = arr[0]
    ans = 0
    for c in arr[1:]:
        while c > l * 2:
            l *= 2
            ans += 1
        while l > c * 2:
            l = (l + 1) // 2
            ans += 1
        l = c
    print(ans)