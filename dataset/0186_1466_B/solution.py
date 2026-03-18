def main():
    pass
    n = int(input())
    # a, b = map(int, input().split())
    arr = list(map(int, input().split()))
    cnt = 1
    arr[-1] += 1
    for i in range(n - 2, -1, -1):
        if arr[i] == arr[i + 1]:
            continue
        if arr[i] + 1 == arr[i + 1]:
            cnt += 1
            continue
        arr[i] += 1
        cnt += 1
    print(cnt)




for i in range(int(input())):
    main()