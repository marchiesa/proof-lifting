for _ in range(int(input())):
    n, m = map(int, input().split())
    a = list(map(int, input().split()))
    b = list(map(int, input().split()))
    inter = set(a).intersection(set(b))
    if len(inter) == 0:
        print("NO")
    else:
        print("YES")
        print(1, list(inter)[0])