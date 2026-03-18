for _ in range(int(input())):
    n, k = map(int, input().split())
    
    ans = list(range(k + 1, n + 1))
    
    ans.extend(range((k + 1) // 2, k))
    
    print(len(ans))
    print(*ans)